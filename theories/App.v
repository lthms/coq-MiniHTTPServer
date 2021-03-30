(** FreeSpec is a general-purpose framework for implementing (with a Free monad)
    and certifying (with contracts) impure computations. In this tutorial, we
    will use FreeSpec to implement and certify a webserver we call
    <<MiniHTTPServer>>. Our goal is to prove our HTTP server correctly uses the
    filesystem, that is it reads from and closes valid file descriptors, and
    closes all its file descriptors.

    The [FreeSpec.Core] module reexports the key component provided by
    FreeSpec. *)

Generalizable All Variables.

From Coq Require Import String.
From FreeSpec Require Import Core.

(** * I. Implementation *)

(** FreeSpec provides the [impure] monad to implement impure computations. This
    monad is equipped with the necessary notations to write idiomatic momadic
    code, thanks to the same notations as the ones introduced in recent versions
    of OCaml.

    The [impure] type takes two parameters respectively of type [interface] and
    [Type]:

      - An interface is a parameterized inductive type, whose constructors
        identify impure primitives. For an interface [i], a term of type [i a]
        identifies a primitive which produces a term of type [a]. An impure
        computation of type [impure i a] can leverage primitives of the
        interface [i].
      - The second parameter of [impure] is the type of result returned by the
        impure computation. Therefore, an impure computation of type [impure i a]
        is expected to produce a result of type [a]. *)

(** ** I.1 Defining Interfaces *)

(** An [interface] is a parameterized inductive type whose constructors identify
    impure primitives.

    For our server, we anticipate the use of three “kinds” of primitives to:

      - Create and manipulate TCP sockets
      - Interact with the filesystem
      - Interact with the console

    Since an impure computation can use _several_ interfaces, FreeSpec favors
    defining independent primitives as part of different interfaces. In our
    case, this means we will have three different interfaces.

    In practice, FreeSpec users do not defined their interface
    manually, but rather generate them.  To that end, we use
    <<coqffi>>. *)

(** *** The TCP Interface *)

From MiniHTTPServerFFI Require Import TCP.

(** *** The FILESYSTEM Interface *)

From MiniHTTPServerFFI Require Import FileSystem.

(** *** The CONSOLE Interface *)

From MiniHTTPServerFFI Require Import Console.

(** ** I.2. Implementing a HTTP Server *)

(** With the three interfaces we have defined in the previous section, we can
    now implement <<MiniHTTPServer>>, that is a minimal HTTP server. Our
    objective is to write a code as idiomatic as possible.

    To that end, we rely on the <<coq-ext-lib>> package, and therefore
    import it. *)

Import List.ListNotations.
From ExtLib Require Import Monad Functor.
Import MonadLetNotation FunctorNotation.
From CoqFFI Require Import String.

(** *** A Word on Non-Termination *)

(** As Coq users know, Gallina only allows to implement strictly recursive
    functions, which means a function in Coq will always terminate. A webserver,
    on the other hand, is expected to run as long as incoming connections
    arrive.  FreeSpec will eventually deal with non-termination, but this has
    not been our priority just yet. In the context of this tutorial, we
    compromise and <<MiniHTTPServer>> will therefore only accept a finite number
    of connections. However, we show that it is correct for any number of finite
    steps.

    To implement this behavior, we introduce [repeatM], which repeats an impure
    computation [n] times. *)

Fixpoint repeatM {m : Type -> Type} `{Monad m} {a} (n : nat) (p : m a) : m unit :=
  match n with
  | O => ret tt
  | S n => p;; repeatM n p
  end.

(** *** A Generic TCP Server *)

(** We first define a generic TCP Server as an impure computation parameterized
    by a so-called handler, that is an impure computation which computes a
    response message for each request message received from a client. *)

From FreeSpec.FFI Require Import FFI.

Definition tcp_server `{Monad m, MonadTCP m}
    (n : nat) (handler : string -> m string)
  : m unit :=
  let* server := new_tcp_socket "127.0.0.1:8088" in
  listen_incoming_connection server;;

  repeatM n (let* client := accept_connection server in

             let* req := read_socket client in
             let* res := handler req in
             write_socket client res;;

             close_tcp_socket client);;

  close_tcp_socket server.

(** *** A HTTP Handler *)

(** <<MiniHTTPServer>> is a minimal server which serves static files over HTTP.
    The main task of its handler will perform is therefore to fetch the content
    of a file identified by a given path. To implement this behavior, we define
    an impure computation [read_content], which performs some logging in
    addition to interacting with the file system.

    As such, [read_content] uses two interfaces. We can specify that thanks to
    [Provide], for instance with [`{Provide ix CONSOLE, Provide ix FILESYSTEM}].
    FreeSpec provides [Provide2], [Provide3], [Provide4], and [Provide5] to make
    the type more readable. *)

Definition read_content `{Monad m, MonadFileSystem m, MonadConsole m}
    (path : string)
  : m string :=
  echo ("  reading <" ++ path ++ ">... ");;
  let* fd := open_file path in
  let* c := read_file fd in
  close_file fd;;
  echo "done.\n";;
  ret c.

(** Using this utility function, we can define the handler itself.

    The parsing of the incoming HTTP requests, and the serialization of HTTP
    response have been implemented in Coq, but are not relevant in this
    tutorial. They are provided inside the <<coq-MiniHTTPServer>> and we reuse
    them. *)

From MiniHTTPServer Require Import URI HTTP.

(** This provides the following types and functions:

      - [http_req] encodes the supported HTTP requests (currently, only GET
        requests are supported).
      - [http_request] a parsing function of the form [bytes -> error_stack +
        http_req]
      - [http_res] encodes the HTTP responses used by MiniHTTPServer (in our
        case, 200, 401, and 404)
      - [response_to_string] to serialize a response as a valid HTTP string. *)

Definition request_handler `{Monad m, MonadFileSystem m, MonadConsole m}
    (base : list directory_id) (req : request)
  : m response :=
  match req with
  | Get uri =>
    let path := uri_to_path (sandbox base uri) in
    let* isf := file_exists path in
    if (isf : bool)
    then let* content := read_content path in
         ret (make_response success_OK content)
    else echo ("  resource <" ++ path ++"> not found\n");;
         ret (make_response client_error_NotFound "Resource not found.")
  end.

From ExtLib Require Import StateMonad.

Definition http_handler `{Monad m, MonadFileSystem m, MonadConsole m}
    (base : list directory_id) (req : string)
  : m string :=
  echo "new request received\n";;
  echo ("  request size is " ++ StrExt.of_int (StrExt.length req) ++ "\n");;

  let* res := match runStateT http_request (Slice.of_string req) with
              | inr req => request_handler base (fst req)
              | _ => ret (make_response client_error_BadRequest "Bad request")
              end in

  ret (response_to_string res).

(** Since [read_content] uses the [CONSOLE] interface in addition to
    [FILESYSTEM], our [http_handler] type exposes this explicitely. However,
    [http_handler] does not use the [TCP] interface itself, and therefore the
    [TCP] interface does not appear inside its type even if in practice it will
    be used in a context where [TCP] is available.

    [http_server] is the final function, the [tcp_server] is specialized with
    our [http_handler]. As a consequence, the type of [http_server] exposes the
    three interfaces we use. *)

Definition http_server `{Monad m, MonadFileSystem m, MonadTCP m, MonadConsole m} (n : nat)
  : m unit :=
  echo "hello, MiniHTTPServer!\n";;
  tcp_server n (http_handler [Dirname (Slice.of_string "tmp")]).

(** * II. Certifying *)

(** As a reminder, our goal is to prove our HTTP server correctly use the
    filesystem, that is it reads from and closes valid file descriptors, and
    closes all its file descriptors. To that end, we need to define a contract
    for the [FILESYSTEM] interface, then reason about [http_server] executions
    w.r.t. this contract. *)

(** ** II.1. Defining a Contract *)

From FreeSpec.Core Require Import CoreFacts.

(** Defining a contract for an interface in FreeSpec means specifying how an
    interface shall be used, but also what to expect from the results of its
    primitives. *)

(** *** The Witness State Type and Helpers *)

(** A contract in FreeSpec has a so-called witness state attached to it. It
    allows to take into account the stateful nature of impure computations and
    primitives implementers. More precisely, a primitive of an interface which
    could be used at a given time may become forbidden in the future.

    This is precisely the case with our use case: a valid file descriptor
    becomes invalid once it has been used as an arguent of the [Close]
    primitive. Witness states shall be as simple as possible, and only holds the
    minimum amount of information about past executed primitives. In our case,
    the witness state can be as simple as a set of open file descriptors. *)

Definition fd_set : Type := file -> bool.

(** In addition, we provide the usuals helpers to manipulate (addition,
    deletion) and reason about sets. *)

Axiom fd_eq_dec : forall (fd1 fd2 : file), { fd1 = fd2 } + { ~ (fd1 = fd2) }.

Definition add_fd (ω : fd_set) (fd : file) : fd_set :=
  fun (fd' : file) => if fd_eq_dec fd fd' then true else ω fd'.

Definition del_fd (ω : fd_set) (fd : file) : fd_set :=
  fun (fd' : file) => if fd_eq_dec fd fd' then false else ω fd'.

Definition member (ω : fd_set) (fd : file) : Prop :=
  ω fd = true.

Definition absent (ω : fd_set) (fd : file) : Prop :=
  ω fd = false.

Lemma member_not_absent (ω : fd_set) (fd : file)
  : member ω fd -> ~ absent ω fd.

Proof.
  unfold member, absent.
  intros m a.
  now rewrite m in a.
Qed.

#[global] Hint Resolve member_not_absent : minihttp.

Lemma absent_not_member (ω : fd_set) (fd : file)
  : absent ω fd -> ~ member ω fd.

Proof.
  unfold member, absent.
  intros a m.
  now rewrite m in a.
Qed.

#[global] Hint Resolve absent_not_member : minihttp.

Lemma member_add_fd (ω : fd_set) (fd : file) : member (add_fd ω fd) fd.

Proof.
  unfold member, add_fd.
  destruct fd_eq_dec; auto.
Qed.

#[global] Hint Resolve member_add_fd : minihttp.

(** *** The Update Function *)

(** In FreeSpec, a contract provides a so-called “update function” to be used to
    reason about an interface usage over time. At any computation step requiring
    the use of a primitive, the “current” witness state is used to determine
    both the caller and the callee obligations. Then, the update function is
    used to update the witness state to take into account what happened for
    future primitives execution.

    In our case, since the witness state is just a set of open file descriptors
    and does not hold any information about e.g. file actual content, the update
    function remains simple: we add newly open file descriptor after [Open], and
    remove them after [Close]. *)

Definition fd_set_update (ω : fd_set) (a : Type) (e : FILESYSTEM a) (x : a) : fd_set :=
  match e, x with
  | Open_file _, fd =>
    add_fd ω fd
  | Close_file fd, _ =>
    del_fd ω fd
  | Read_file _, _ =>
    ω
  | File_exists _, _ =>
    ω
  end.

(** *** The Caller Obligations *)

(** Our experience with FreeSpec has tended to show that using inductive types
    for obligations is the more convenient approach in practice, but this comes
    with a tradeoff in terms of readability. *)

Inductive fd_set_caller_obligation (ω : fd_set)
  : forall (a : Type), FILESYSTEM a -> Prop :=

(** We do not restrict the use of [Open] or [FileExists] *)

| fd_set_open_caller (p : string)
  : fd_set_caller_obligation ω file (Open_file p)
| fd_set_is_file_caller (p : string)
  : fd_set_caller_obligation ω bool (File_exists p)

(** In order for [Read] and [Close] to be used correctly, their
    [file] argument has to be a member of the witness state. *)

| fd_set_read_caller (fd : file)
    (is_member : member ω fd)
  : fd_set_caller_obligation ω string (Read_file fd)
| fd_set_close_caller (fd : file)
    (is_member : member ω fd)
  : fd_set_caller_obligation ω unit (Close_file fd).

#[global] Hint Constructors fd_set_caller_obligation : minihttp.

(** *** The Callee Obligations *)

(** The callee obligations of our contract are not as straightforward as the
    caller obligations. It appears that we could potentially require nothing
    special from a [FILESYSTEM] implementer for our particular use case. There
    is, however, one scenario that we want to avoid in practice:

      - The caller opens two different files
      - The callee returns the same file descriptor for both files
      - the caller closes one file descriptor, and uses the second one

    In such a scenario, the caller misuses the interface in good faith. To avoid
    this, we require the [Open] primitives to return _fresh_ file
    descriptors. *)

Inductive fd_set_callee_obligation (ω : fd_set)
  : forall (a : Type), FILESYSTEM a -> a -> Prop :=

(** The [file] returned by the [Open] primitive shall not be a member
    of the witness state. *)

| fd_set_open_callee (p : string) (fd : file)
    (is_absent : absent ω fd)
  : fd_set_callee_obligation ω file (Open_file p) fd

(** We do not specify any particular requirements for the results of the other
    primitives. Therefore, we cannot use this contract to reason about the
    result of reading twice the same file, for instance. This would require
    another contract, which is totally fine with FreeSpec since we can compose
    them together. *)

| fd_set_read_callee (fd : file) (s : string)
  : fd_set_callee_obligation ω string (Read_file fd) s
| fd_set_close_callee (fd : file) (t : unit)
  : fd_set_callee_obligation ω unit (Close_file fd) t
| fd_set_is_file_callee (p : string) (b : bool)
  : fd_set_callee_obligation ω bool (File_exists p) b.

#[global] Hint Constructors fd_set_callee_obligation : minihttp.

(** *** The Contract Definition *)

(** We put everything together by defining a term of type [contract FILESYSTEM
    fd set]. *)

Definition fd_set_contract : contract FILESYSTEM fd_set :=
  {| witness_update := fd_set_update
   ; caller_obligation := fd_set_caller_obligation
   ; callee_obligation := fd_set_callee_obligation
  |}.

(** ** II.2. Problem Definition *)

(** From the caller perspective, there is two concerns that we want to express.
    First, we _always_ use correct file descriptors. Secondly, we _eventually_
    close any file descriptor previously opened.

    The first objective is a _safety_ property that we can express
    using the [respectful_impure] predicate. The exact lemma is: *)

Lemma fd_set_respectful_http_server `{StrictProvide3 ix FILESYSTEM TCP CONSOLE}
    (ω : fd_set) (n : nat)
  : pre (to_hoare fd_set_contract (http_server n)) ω.
Abort.

(** The [StrictProvide3] typeclass is very analogous to the [Provide3] one, but
    it requires more contrains about its arguments. The exact details about
    the difference is out of the scope of this tutorial, especially since the
    two typeclasses with eventually be merged together.

    The second objective is a _liveness_ property that we can express agains the
    final witness state. This can be acheived using the [respectful_run]
    predicate provided by FreeSpec. *)

Lemma fd_set_preserving_http_server `{StrictProvide3 ix FILESYSTEM TCP CONSOLE}
      (n : nat)
  : forall (ω ω' : fd_set) (x : unit),
    post (to_hoare fd_set_contract (http_server n)) ω x ω'
    -> forall fd, ω fd = ω' fd.
Abort.

(** This property can be read as: any [file] which is opened during
    the execution of [http_server] is closed before the execution ends. This
    is a property that we generalize for any impure computations:  *)

Definition fd_set_preserving {a} `{MayProvide ix FILESYSTEM} (p : impure ix a) :=
  forall (ω ω' : fd_set) (x : a),
    post (to_hoare fd_set_contract p) ω x ω' -> forall fd, ω fd = ω' fd.

(** And, as a consequence, the second lemma we want to prove becomes: *)

Lemma fd_set_preserving_http_server `{StrictProvide3 ix FILESYSTEM TCP CONSOLE}
    (n : nat)
  : fd_set_preserving (http_server n).
Abort.

(** ** II.3. <<MiniHTTPServer>> Proofs of Correctness *)

(** We now have defined everything we need to prove the correctness of
    <<MiniHTTPServer>>. The rest of this tutorial consists in actually write the
    proofs. Our approach is bottom-up: we start from the leaves of our
    computations, show they have some important properties, then reuse our
    result to eventually conclude about the correctness of the whole program. *)

(** *** Certifying [read_content] *)

(** From the perspective of this tutorial, the [read_content] impure computation
    is an interesting starting point: it uses two primitives that can be misused
    according to the [fd_set_contract] ([Read], and [Close]), and it also uses
    an interface which is not relevant from the perspective of [fd_set_contract]
    ([CONSOLE]). *)

Lemma fd_set_respectful_read_content `{StrictProvide2 ix FILESYSTEM CONSOLE}
    (ω : fd_set) (path : string)
  : pre (to_hoare fd_set_contract (read_content path)) ω.

(** FreeSpec provides the [prove impure] tactics to automate as much as possible
    the construction of a proof for [respectful_impure] goals. It performs many
    uninteresting tasks that FreeSpec users would have to do manually if they
    decided not to use it. For the sake of demonstration, we attempt to do just that,
    and use [repeat constructor].

    This generates 5 hardly readable subgoals, for instance the 5th subgoal is:

<<
  ω : fd_set
  path : bytes
  x : unit
  H4 : gen_callee_obligation fd_set_contract ω
         (inj_p (Echo ("  reading <" ++ path ++ ">... "))) x
  x0 : file
  H5 : gen_callee_obligation fd_set_contract
         (gen_witness_update fd_set_contract ω
            (inj_p (Echo ("  reading <" ++ path ++ ">... "))) x)
         (inj_p (Open path)) x0
  x1 : bytes
  H6 : gen_callee_obligation fd_set_contract
         (gen_witness_update fd_set_contract
            (gen_witness_update fd_set_contract ω
               (inj_p (Echo ("  reading <" ++ path ++ ">... "))) x)
            (inj_p (Open path)) x0) (inj_p (Read x0)) x1
  x2 : unit
  H7 : gen_callee_obligation fd_set_contract
         (gen_witness_update fd_set_contract
            (gen_witness_update fd_set_contract
               (gen_witness_update fd_set_contract ω
                  (inj_p (Echo ("  reading <" ++ path ++ ">... "))) x)
               (inj_p (Open path)) x0) (inj_p (Read x0)) x1)
         (inj_p (Close x0)) x2
  ============================
 gen_caller_obligation fd_set_contract
   (gen_witness_update fd_set_contract
      (gen_witness_update fd_set_contract
         (gen_witness_update fd_set_contract
            (gen_witness_update fd_set_contract ω
               (inj_p (Echo ("  reading <" ++ path ++ ">... "))) x)
            (inj_p (Open path)) x0) (inj_p (Read x0)) x1)
      (inj_p (Close x0)) x2) (inj_p (Echo "done.
"))
>>

    [prove_impure] provides a much cleaner output:

<<
subgoal 1 is:
  fd_set_caller_obligation ω file (Open path)

subgoal 2 is:
 fd_set_caller_obligation (add_fd ω x0) bytes (Read x0)

subgoal 3 is:
 fd_set_caller_obligation (add_fd ω x0) unit (Close x0)
>>

    In this case, we can use the [minihttp] database that we have enriched with various [Hint]
    to conclude automatically about this. *)

Proof.
  prove impure with minihttp.
Qed.

#[global] Hint Resolve fd_set_respectful_read_content : minihttp.

(** The second property we want to prove about [read_content] is that
    it does not forget to close any [file]. *)

Lemma fd_set_preserving_read_content `{StrictProvide2 ix FILESYSTEM CONSOLE}
    (path : string)
  : fd_set_preserving (read_content path).

(** Similarly to [prove_impure], FreeSpec provides a tactic to exploit
    hypotheses about [respectful_run]. More precisely, it explore the different
    execution path that could lead to the production of the run in hypothesis,
    and clean-up as much as possible the resulting alternative goals.. We can
    explicit the tasks performed by [respectful_run] with the following
    command.

<<
  repeat match goal with
         | H : respectful_run _ _ _ _ _ |- _ => inversion H; clear H; ssubst
         end.
>>

    This produces the following goal:

<<
  path : bytes
  ω : fd_set
  x : bytes
  x0 : unit
  o_callee : gen_callee_obligation fd_set_contract ω
               (inj_p (Echo ("  reading <" ++ path ++ ">... "))) x0
  o_caller : gen_caller_obligation fd_set_contract ω
               (inj_p (Echo ("  reading <" ++ path ++ ">... ")))
  x1 : file
  o_callee0 : gen_callee_obligation fd_set_contract
                (gen_witness_update fd_set_contract ω
                   (inj_p (Echo ("  reading <" ++ path ++ ">... "))) x0)
                (inj_p (Open path)) x1
  o_caller0 : gen_caller_obligation fd_set_contract
                (gen_witness_update fd_set_contract ω
                   (inj_p (Echo ("  reading <" ++ path ++ ">... "))) x0)
                (inj_p (Open path))

                               [...]

  o_caller3 : gen_caller_obligation fd_set_contract
                (gen_witness_update fd_set_contract
                   (gen_witness_update fd_set_contract
                      (gen_witness_update fd_set_contract
                         (gen_witness_update fd_set_contract ω
                            (inj_p (Echo ("  reading <" ++ path ++ ">... "))) x0)
                         (inj_p (Open path)) x1) (inj_p (Read x1)) x)
                   (inj_p (Close x1)) x3) (inj_p (Echo "done.
"))
  o_callee3 : gen_callee_obligation fd_set_contract
                (gen_witness_update fd_set_contract
                   (gen_witness_update fd_set_contract
                      (gen_witness_update fd_set_contract
                         (gen_witness_update fd_set_contract ω
                            (inj_p (Echo ("  reading <" ++ path ++ ">... "))) x0)
                         (inj_p (Open path)) x1) (inj_p (Read x1)) x)
                   (inj_p (Close x1)) x3) (inj_p (Echo "done.
")) x4
  ============================
  forall fd : file,
  ω fd =
  gen_witness_update fd_set_contract
    (gen_witness_update fd_set_contract
       (gen_witness_update fd_set_contract
          (gen_witness_update fd_set_contract
             (gen_witness_update fd_set_contract ω
                (inj_p (Echo ("  reading <" ++ path ++ ">... "))) x0)
             (inj_p (Open path)) x1) (inj_p (Read x1)) x)
       (inj_p (Close x1)) x3) (inj_p (Echo "done.
")) x4 fd
>>

    On the contrary, [unroll_respectful_run] keeps the goal manageable, and once called, the FreeSpec
    internals are gone and we can write a “classical” Coq proof. *)

Proof.
  intros ω x ω' run.
  unroll_post run.
  intros fd'.
  unfold add_fd, del_fd.
  destruct fd_eq_dec; subst.
  + now inversion H4; ssubst.
  + reflexivity.
Qed.

(** The implementation details of [read_content] will not be relevant with our
    two freshly proven lemmas. Therefore, we make the impure computation to
    prevent [improve_impure] and [unroll_respectful_run] to unfold them. *)

#[local] Opaque read_content.

(** *** Certifying [file_exists] *)

(** We use the exact same approach for [file_exists]. Since this computation
    does not use any problematic primitives, the proofs are straightforward. *)

Lemma fd_set_respectful_file_exists `{Provide ix FILESYSTEM} (ω : fd_set) (path : string)
  : pre (to_hoare fd_set_contract (file_exists path)) ω.

Proof.
  prove impure with minihttp.
Qed.

#[global] Hint Resolve fd_set_respectful_file_exists : minihttp.

Lemma fd_set_preserving_file_exists `{Provide ix FILESYSTEM} (path : string)
  : fd_set_preserving (file_exists path).

Proof.
  intros ω x ω' run.
  now unroll_post run.
Qed.

(** Again, we make [file_exists] opaque because its concrete implementation is
    not relevant anymore. *)

#[local] Opaque file_exists.

(** *** Certifying [http_handler] *)

(** The [http_handler] is interesting, because to a large extent, it does not
    use primitives itself: it relies on other impure computations [read_content]
    and [file_exists] to do so. Interested readers can try to remove the
    vernacular commands which make these two computations opaque and see the
    outputs of [prove_impure] and [unroll_respectful_run]: in a nutshell, they
    would find themselves having to prove one more time the exact same goals, in
    more crowded contexts. *)

#[local] Opaque http_request.

Lemma fd_set_respectful_http_handler `{StrictProvide2 ix FILESYSTEM CONSOLE}
    (base : list directory_id) (req : string) (ω : fd_set)
  : pre (to_hoare  fd_set_contract (http_handler base req)) ω.

Proof.
  prove impure.
  destruct (runStateT http_request (Slice.of_string req)).
  + prove impure.
  + destruct (fst p).
    prove impure.

(** Here, [prove_impure] did not unfold [file_exists] and [read_content], but
    has leveraged FreeSpec formalism to generate two clean subgoals.
<<
subgoal 1 is:
  respectful_impure fd_set_contract ω
    (file_exists (uri_to_path (sandbox base resource)))

subgoal 2 is:
 respectful_impure fd_set_contract w
   (read_content (uri_to_path (sandbox base resource)))
>>

    Both are straightforward to prove using the [minihttp] hint database. *)

    all: eauto with minihttp.
Qed.

#[global] Hint Resolve fd_set_respectful_http_handler : minihttp.

Lemma fd_set_preserving_http_handler `{StrictProvide2 ix FILESYSTEM CONSOLE}
    (base : list directory_id) (req : string)
  : fd_set_preserving (http_handler base req).

Proof.
  intros ω x ω' run fd.
  unroll_post run.
  destruct (runStateT http_request (Slice.of_string req)).
  + now unroll_post run.
  + destruct p as [[res_id] req'].
    unroll_post run.

(** [unroll_respectful_run] uses a similar approach when in presence of opaque
    terms. *)

    ++ apply fd_set_preserving_file_exists in run0.
       apply fd_set_preserving_read_content in run.
       now transitivity (ω0 fd).
    ++ now apply fd_set_preserving_file_exists in run0.
Qed.

#[global] Hint Resolve fd_set_preserving_http_handler : minihttp.

#[local] Opaque http_handler.
#[local] Opaque response_to_string.

(** *** Certifying [repeatM] *)

From Coq Require Import FunctionalExtensionality.

Lemma fd_set_preserving_repeatM {a} `{Provide ix FILESYSTEM}
    (p : impure ix a)
    (fd_preserving : fd_set_preserving p)
    (n : nat)
  : fd_set_preserving (repeatM n p).

Proof.
  intros ω ω' fd run.
  induction n.
  + now unroll_post run.
  + unroll_post run.
    apply IHn.
    replace ω with ω0; auto.
    symmetry.
    apply functional_extensionality.
    eauto.
Qed.

#[global] Hint Resolve fd_set_preserving_repeatM : minihttp.

Lemma repeatM_preserving_respectful {a} `{Provide ix FILESYSTEM}
    (p : impure ix a) (ω : fd_set)
    (fd_trust : pre (to_hoare fd_set_contract p) ω)
    (fd_preserving : fd_set_preserving p)
    (n : nat)
  : pre (to_hoare fd_set_contract (repeatM n p)) ω.

Proof.
  revert ω fd_trust.
  induction n; intros ω fd_trust.
  + prove impure.
  + prove impure with minihttp.
    apply IHn.
    replace ω0 with ω; auto.
    apply functional_extensionality.
    intros fd.
    eapply fd_preserving.
    exact hpost.
Qed.

#[local] Opaque repeatM.

Lemma fd_set_preserving_tcp_server_repeat_routine
   `{Provide ix TCP, MayProvide ix FILESYSTEM, Distinguish ix TCP FILESYSTEM}
    (server : socket)
    (handler : string -> impure ix string)
    (preserve : forall (req : string), fd_set_preserving (handler req))
  : fd_set_preserving (let* client := accept_connection server in

                       let* req := read_socket client in
                       let* res := handler req in
                       write_socket client res;;

                       close_tcp_socket client).

Proof.
  intros ω b ω' run fd.
  unroll_post run.
  now apply preserve in run.
Qed.

#[global] Hint Resolve fd_set_preserving_tcp_server_repeat_routine : minihttp.

(** *** Certifying [http_server] *)

Lemma fd_set_respectful_http_server `{StrictProvide3 ix FILESYSTEM TCP CONSOLE}
    (ω : fd_set) (n : nat)
  : pre (to_hoare fd_set_contract (http_server n)) ω.

Proof.
  prove impure.
  apply repeatM_preserving_respectful.
  + prove impure.
    apply fd_set_respectful_http_handler.
  + intros ω' ω'' [] run fd.
    apply fd_set_preserving_tcp_server_repeat_routine in run; auto with minihttp.
    apply fd_set_preserving_http_handler.
Qed.

Lemma fd_set_preserving_http_server `{StrictProvide3 ix FILESYSTEM TCP CONSOLE}
    (n : nat)
  : fd_set_preserving (http_server n).

Proof.
  intros ω x ω' run fd.
  unroll_post run.
  apply fd_set_preserving_repeatM in run0; auto with minihttp.
  apply fd_set_preserving_tcp_server_repeat_routine.
  apply fd_set_preserving_http_handler.
Qed.
