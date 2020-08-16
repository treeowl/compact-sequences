(* Purely functional stack with efficient space consumption *)

(* In this file, we verify the amortized complexity of compact stacks in Coq. *)

(* FEATURES

   1. Space overhead is logarithmic: if storing the elements alone takes
      X space, this stack takes X + O(log n) space,
      where n is the number of elements in the stack.

   2. [push] and [pop] (LIFO order) in amortized O(log n) time.
 *)

(* CONTENTS OF THIS FILE

   1. The purely functional stack:
      a type [stack] and two functions [push] and [pop]
      (this is a manual translation of the Haskell library)

   2. Debit structure (a data type [debit] indexed by [stack])

   3. Decorating stack operations into operations on debit structures
      ([push_debit], [pop_debit])

   4. Theorems
      a. Debit preservation
      b. Debit invariant
      c. Amortized complexity bound

      ([push_debit_preservation], [pop_debit_preservation])
      ([push_debit_invariant], [pop_debit_invariant])
      ([push_acost], [pop_acost])
 *)

(* SCOPE OF THE PROOF

   A proof is only as good as the specification it proves.
   This proof assumes familiarity with Okasaki's (generalized) Banker's method
   (background summarized below). The main purpose of the present formalization
   in Coq is to ensure all the cases in the proof have been covered.

   This proof makes the following informal assumptions, which are
   therefore blind spots to look out for:

   1. The Coq implementation of the stack matches the Haskell implementation.

   2. This is an accurate implementation of the Banker's method.
      concretely, the statements of the theorems [push_acost] and [pop_acost]
      must be trusted to faithfully formalize the claim that those operations
      have logarithmic cost.

   3. The operations [push_debit] and [pop_debit] are correctly defined.
      All debits must be accounted for: debits must be generated for every
      vector operation ([concat], [split]) and they must not be discarded.
      Ideally we should use the type system to prevent that, but this is
      actually impossible in this very shallow embedding.

   To reduce gap (1), we could automate the translation using hs-to-coq
   for instance. For (2) and (3), one way is to build an operational semantics
   for a deep embedding of Haskell, from which the cost of a function
   could be defined explicitly; another way, more lightweight for still using a
   shallow embedding, is to define the operations in a monad that tracks the cost
   of operations. Laziness makes either solution quite challenging.

   This is not a proof of functional correctness (that the stack behaves
   like a stack), but that is comparatively straightforward and obvious.
 *)

(** * Overview, background *)

(** ** Amortization of lazy data structures *)

(* To amortize the cost of evaluating thunks (which use the expensive
   operations [concat] and [split]), we associate a quantity of debt, or
   _debits_, for each thunk, equal to its cost, which must be paid
   _before_ the thunk is forced.

   Operations, however expensive, are performed through the evaluation of
   lazy thunks: thunks are shared so simply redoing the operation will not
   reevaluate the thunk, and the debit payment scheme ensures sufficient time
   must pass between the creation of the thunk and its evaluation.

   Concretely, debits can be represented as another data structure which
   _decorates_ the original stack with debits.
   Then we must similarly _decorate_ the operations ([push], [pop]) into
   operations on debit structures, with the following objectives:

   - _creating_ debit for every new thunk, equal to the cost of that thunk;
   - _moving_ debit around the structure to ensure a certain debit invariant;
   - _paying_ debit, removing it from the structure.

   The amount of debits paid is the _amortized cost_ of the operation.

   We can consider that all work is performed through evaluating thunks
   (that could mean creating a thunk and evaluating it immediately).
   If we ensure that debits are fully paid before a thunk is evaluated,
   then at any point, the cumulated amortized cost of all operations
   is an upper bound on the cumulated actual time consumed by those operations.
 *)

(** ** Proof organization *)

(* After defining the debit structure, the verification is structured as
   follows:

   1. Decorate the operations ([push], [pop]) into operations on debit
      structures (as we just discussed).
      ([push_debit], [pop_debit])

   2. Prove debit preservation: every unit of debit is accounted for.
      New thunks increase the debits by an amount equal to their cost,
      and every stack operation takes away some debits which become
      the amortized cost of the operation.
      In a way, this is more of a sanity check, to make sure we didn't accidentally
      lose debits in step 1, which would make the subsequent proofs too easy.
      ([push_debit_preservation], [pop_debit_preservation])

   3. Define an invariant on the debit structure (called the debit invariant),
      which must be preserved by the operations,
      This invariant puts upper bounds on the debits, enabling the next and final step.
      (definition: [debit_invariant];
       theorems: [push_debit_invariant], [pop_debit_invariant])

   4. Prove an upper bound on the amortized cost of an operation.
      ([push_acost], [pop_acost])
 *)

From Coq Require Import
  NArith  (* Natural number arithmetic *)
  Lia     (* Solver for Linear Integer Arithmetic *)
  Eqdep.  (* Heterogeneous equality (used in proofs for [pop]) *)

Local Open Scope N_scope.

Set Implicit Arguments.
Set Strict Implicit.
Set Primitive Projections.

(** * Utilities *)

Definition bind_option {A B: Type} (oa : option A) (kb : A -> option B) : option B :=
  match oa with
  | Some a => kb a
  | None => None
  end.

(* We redefine pairs with primitive projections to make things easier:
   computation is not blocked by pattern-matching on pairs. *)

Record prod (A B : Type) : Type := pair
  { fst : A ; snd : B }.

Infix "*" := prod : type_scope.
Notation "'(' x ',' y ')'" := (pair x y).


(** * Abstract array interface *)

(* Primitives that the stack implementation relies on. *)

(* [array i]: array of length [i]. *)
Parameter array : Type -> N -> Type.

(* [sinle a]: a singleton array (length 1) containing the element [a]. *)
Parameter single : forall {A : Type}, A -> array A 1.

(* [concat x y]: concatenation of two arrays of equal length.
   (That is all we need for this implementation.) *)
Parameter concat : forall {A : Type} {i : N}, array A i -> array A i -> array A (2 * i).

(* [split xy]: break an array in half. *)
Parameter split : forall {A : Type} {i : N}, array A (2 * i) -> array A i * array A i.

(* [uniq x]: extract the element from a singleton array. *)
Parameter uniq : forall {A : Type}, array A 1 -> A.

(* Cost model:
   - [concat] and [split] cost [i] units, where [i] is half the number of elements involved
     (it makes arithmetic easier to not have to track factors of 2).
   - The cost of all other operations will be ignored.
     + [single] and [uniq] are used once per operation, and would have constant cost.
     + Pattern-matching, constructors, (recursive) function calls, have constant cost
       individually, and add up to logarithmic cost per operation ([push], [pop]).
 *)


Section STACK.

Variable A : Type.
Notation array := (array A).

(** * Purely functional stack *)

(** ** Type definition *)

(* [stack_ i]: internal representation with an index [i] to track the length of
   arrays. If [s] has type [stack_ i], we call [i] the level of the stack [s].
 *)
Inductive stack_ (i : N) : Type :=
| Empty
| One (x : array i) (s : stack_ (2 * i))
| Two (x y : array i) (s : stack_ (2 * i))
| Three (x y z : array i) (s : stack_ (2 * i))
.
Arguments Empty {i}.

(* [stack]: the top-level type of stack that users see. *)
Definition stack : Type := stack_ 1.

(* Note on naming convention: most functions and types are built in two steps:
   an internal recursive variant, suffixed with an underscord ([stack_])
   and an externally visible variant that wraps the internals in a clean
   interface ([stack]). *)


(** ** [push] and [pop] *)

(* [push a s]: put element [a] on top of stack [s]. *)

(* Auxiliary function:
   - [push_ w s]: put an array [w] (of length [i]) on top of stack [s] (at level [i]).
 *)

Fixpoint push_ {i : N} (w : array i) (s : stack_ i) : stack_ i :=
  match s with
  | Empty => One w Empty
  | One x s => Two w x s
  | Two x y s_ => Three w x y s_
  | Three x y z s => Two w x (push_ (concat y z) s)
  end.

Definition push (x : A) (s : stack) : stack :=
  push_ (single x) s.

(* [pop s]: remove the top element from stack [s]. *)

(* Auxiliary functions:
   - [pop_ s]: remove the top array of stack [s].
   - [lower z]: flatten into a [stack] the result of a recursive call to [pop_]
     (an option of a top element and a stack at level [2 * i]) into a stack
     at level [i]. *)

Definition lower {i : N} (os : option (array (2 * i) * stack_ (2 * i)))
  : stack_ i :=
  match os with
  | None => Empty
  | Some (yz, s') =>
    let '(y, z) := split yz in
    Two y z s'
  end.

Fixpoint pop_ {i : N} (s : stack_ i) : option (array i * stack_ i) :=
  match s with
  | Empty => None
  | One x s => Some (x, lower (pop_ s))
  | Two x y s => Some (x, One y s)
  | Three x y z s => Some (x, Two y z s)
  end.

Definition pop (s : stack) : option (A * stack) :=
  match pop_ s with
  | None => None
  | Some (x, s) => Some (uniq x, s)
  end.

(** ** Auxiliary definitions for proofs *)

Fixpoint count_ {i : N} (s : stack_ i) : N :=
  match s with
  | Empty => 0
  | One _ s => i + count_ s
  | Two _ _ s => 2 * i + count_ s
  | Three _ _ _ s => 3 * i + count_ s
  end.

Definition count (s : stack) : N := count_ s.

(* [depth s]: the depth of a stack. *)
Fixpoint depth_ {i : N} (s : stack_ i) : N :=
  match s with
  | Empty => 0
  | One _ s
  | Two _ _ s
  | Three _ _ _ s => 1 + depth_ s
  end.

Definition depth (s : stack) : N := depth_ s.

(* Depth is logarithmic in the size of the stack. *)

Lemma depth_log_ {i : N} (s : stack_ i) : 0 < i -> i * 2 ^ depth_ s - i <= count_ s.
Proof.
  assert (H : forall n, 2 ^ (1 + n) = 2 * 2 ^ n).
  { intros n; apply N.pow_add_r. }
  induction s; cbn [count_ depth_ N.pow]; try rewrite H; lia.
Qed.

Lemma depth_log (s : stack) : 2 ^ depth s - 1 <= count s.
Proof.
  unfold count, depth.
  pose proof (depth_log_ s).
  lia.
Qed.

(** ** Simple cost functions *)

(* The total cost of the thunks created by [push] and [pop]. *)

Fixpoint debit_push_ {i : N} (s : stack_ i) : N :=
  match s with
  | Empty => 0
  | One x s => 0
  | Two x y s => 0
  | Three x y z s => i + debit_push_ s
  end.

Definition debit_push (s : stack) : N := debit_push_ s.

Fixpoint debit_pop_ {i : N} (s : stack_ i) : N :=
  match s with
  | Empty => 0
  | One x s =>
    match pop_ s with
    | None => 0
    | Some _ => debit_pop_ s + i
    end
  | Two _ _ _ => 0
  | Three _ _ _ _ => 0
  end.

(** ** Debit structure *)

(* The following [debit_] structure is how we attach debit to stack nodes.

   Debits are represented by values of type [N].

   Note that thunks are not explicitly represented anywhere. A term [s] of type
   [stack] is an _abstract value_ which models the result of evaluating all
   thunks of its run-time representation. Debits are carried by these abstract
   values: debits are purely logical gadgets for the purpose of proving amortized
   bounds for the time the program actually takes to run.

   For this stack implementation, only [Two] nodes carry any debit.
   Strictly speaking it is attached to the tail [s] of the node [Two x y s]:
   the debit must be paid only before forcing [s].

   That is a subtle point: a different possibility would be to view the debit
   as attached to the _current_ [Two x y s] node, so it must be paid to use
   the whole node.
   The issue with that approach is that either it assumes that all nodes are
   lazy (in the Haskell version of the code this is based on, there are strictness
   annotations that imply is not the case), or the mapping between debits
   and thunks is not obvious (i.e., the soundness of this whole business is
   even more questionable than it already is, unless you prove it).
 *)
Inductive debit_ {i : N} : stack_ i -> Type :=
| debit_Empty : debit_ Empty
| debit_One {x s} : @debit_ (2 * i) s -> debit_ (One x s)
| debit_Two {x y s} : N -> @debit_ (2 * i) s -> debit_ (Two x y s)
| debit_Three {x y z s} : @debit_ (2 * i) s -> debit_ (Three x y z s)
.

Definition debit (s : stack) : Type := debit_ s.

(* [debit_sum s]: the total debit contained in a [debit_] structure. *)

Fixpoint debit_sum_ {i : N} {s : stack_ i} (d0 : debit_ s) : N :=
  match d0 with
  | debit_Empty => 0
  | debit_One d => debit_sum_ d
  | debit_Two m d => m + debit_sum_ d
  | debit_Three d => debit_sum_ d
  end.

Definition debit_sum {s : stack} : debit s -> N := debit_sum_.

(* [take amount total]: take up to [amount] out of [total],
   returning a pair of:
   - the taken amount ([<= amount])
   - the remaining total.

   The sum of the resulting pair is equal to the original total. (Lemma take_total.)

   We make sure in the functions below that every fragment of debit is used
   exactly once, possibly through this [take] function:
[[
   let '(n, p) := take i m in ...
]]
   counts as one use of [m] and the new variables [n] and [p] must then
   be used exactly once. ([i] is not a part of debit, so it is not treated linearly.)
 *)
Definition take (amount total : N) : N * N :=
  (N.min total amount, total - amount).

Lemma take_total amount total :
  let '(amount', total') := take amount total in
  amount' + total' = total.
Proof.
  cbn. lia.
Qed.


(** ** [push] lifted on debit structures *)

(* We'll keep [pop] for the end. *)

(* Main definitions:
   - [pay_debit]
   - [push_debit]
 *)

(* One important purpose of debit structures is that debits can be moved
   around within them. But debits also have a provenance: the thunk they
   are paying for. To evaluate a thunk, we must have paid for all their
   debits. How do we tell where a debit comes from? Well, we don't.
   Representing debits as mere natural numbers does not allow us to encode this
   information.

   This is one place where the formalization gets shaky.
   What we do is to only pass debits "upwards" through the stack.
   So when we reach a thunk to evaluate it, we will have paid all of the
   debits between the top of the stack and that thunk, which contain all
   the debits of that thunk.
   Sadly, that cannot be checked automatically by Coq with our formalization
   either. This is a property that is only visible in the syntax of the
   definition, but we leverage types and purity to make the inspection easier:
   - debits are used exactly once;
   - functions on debit structures only output debits,
     in particular, recursive calls don't consume debits as arguments, so they
     don't even get the opportunity to move debits "downwards" the stack.
 *)

(* Take one unit of debit from each [Two] node, returning the total debit taken
   and the updated debit structure.

   Associated theorems:
   - Debit preservation: [pay_debit_preservation]
   - Debit invariant: [pay_debit_invariant]
   - Logarithmic cost: [pay_debit_cost]
 *)
Fixpoint pay_debit {i : N} {s : stack_ i} (d0 : debit_ s) : N * debit_ s :=
  match d0 with
  | debit_Empty => (0, debit_Empty)
  | debit_One d =>
    let '(n, d') := pay_debit d in
    (n, debit_One d')
  | debit_Two m d =>
    let '(n, d') := pay_debit d in
    let '(n2, m') := take 1 m in
    (n + n2, debit_Two m' d')
  | debit_Three d =>
    let '(n, d') := pay_debit d in
    (n, debit_Three d')
  end.

(* [@push_debit a s d]: a pair of the amortized cost of [push a s] and
   remaining debit.

   Associated theorems:
   - Debit preservation: [push_debit_preservation]
   - Debit invariant: [push_debit_invariant]
   - Logarithmic cost: [push_acost]
 *)

Fixpoint push_debit_ {i : N} {w : array i} {s : stack_ i} (d0 : debit_ s)
  : N * debit_ (push_ w s) :=
  match d0 with
  | debit_Empty => (0, debit_One debit_Empty)
  | debit_One d => (0, debit_Two 0 d)
  | debit_Two m d =>
    let '(n, d') := pay_debit d in
    (m + n, debit_Three d')
  | debit_Three d =>
    let '(n, d') := push_debit_ d in
    let '(i', n') := take i n in
    (n', debit_Two (i + i') d')
  end.

Definition push_debit (a : A) {s : stack} (d0 : debit s)
  : N * debit (push a s) :=
  push_debit_ d0.

(* An auxiliary function to compute the sum of a pair,
   where the first element is an amortized cost and the second element is
   a debit structure. *)

Definition total_pair {T} (sum_ : T -> N) (p : N * T) : N := fst p + sum_ (snd p).


(** ** Debit preservation theorem for [push] *)

(* Main theorems:
   - [pay_debit_preservation]
   - [push_debit_preservation]
 *)

(* To make sure we didn't accidentally forget any debits, we prove debit preservation
   theorems: the sum of the debit after an operation and the debit taken out must be
   equal to the sum of the debit before the operation and the cost of all new thunks. *)

(* Debit preservation for [pay_debit]. ([pay_debit_preservation])

   The total debit at the beginning is equal to the sum of the
   debit taken and the total debit remaining at the end. *)

Lemma pay_debit_preservation {i : N} {s : stack_ i} (d : debit_ s)
  : total_pair debit_sum_ (pay_debit d) = debit_sum_ d.
Proof.
  unfold total_pair.
  induction d; cbn - [ N.add ] in *.
  all: try (assumption + lia).
  remember (fst _).
  remember (debit_sum_ (snd _)).
  remember (debit_sum_ d).
  lia.
Qed.

(* Debit preservation for [push_debit]. ([push_debit_preservation])

   The total debit at the beginning PLUS the additional debit generated by the
   [push] operation IS EQUAL TO the amortized cost (the amount of debit paid for
   this operation) PLUS the total debit remaining at the end. *)

Lemma push_debit_preservation_ {i : N} {w : array i} {s : stack_ i} (d : debit_ s)
  : total_pair debit_sum_ (push_debit_ (w := w) d) = debit_push_ s + debit_sum_ d.
Proof.
  unfold total_pair.
  induction d; cbn [fst snd debit_sum_ push_debit_ debit_push_].
  all: try lia.
  - pose proof (pay_debit_preservation d).
    unfold total_pair in H.
    remember (fst _).
    remember (debit_sum_ (snd _)).
    lia.
  - specialize (IHd (concat y z)).
    cbn [take].
    remember (fst _).
    remember (snd _).
    lia.
Qed.

Lemma push_debit_preservation {a : A} {s : stack} (d : debit s)
  : total_pair debit_sum (push_debit a d) = debit_push s + debit_sum d.
Proof.
  apply push_debit_preservation_.
Qed.


(** ** Debit invariant *)

(* The debit invariant puts bounds on the debit contained in a debit structure,
   and must be preserved by all stack operations ([push] and [pop]).

   Roughly, the debit on a [Two] node is less than half the total number of
   elements in that node ([i]) and all [Two] nodes preceding it ([twos]).

   The extra [1] term in the upper bound [1 + twos + i] makes our accounting
   easier: thanks to it, consecutive [Two] nodes starting from the top have a
   bound [1 + twos + i] exactly equal to a power of two.
 *)
Fixpoint debit_invariant_ {i : N} {s : stack_ i} (twos : N) (d0 : debit_ s) : Prop :=
  match d0 with
  | debit_Empty => True
  | debit_One d => debit_invariant_ twos d
  | debit_Two m d => m <= 1 + twos + i /\ debit_invariant_ (twos + i) d
  | debit_Three d => debit_invariant_ twos d
  end.

Definition debit_invariant {s : stack} : debit s -> Prop :=
  debit_invariant_ 0.

(* We can always raise the [twos] bound. *)
Lemma debit_invariant_monotone {i : N} {s : stack_ i} (twos twos' : N) (d0 : debit_ s)
    (H : twos <= twos')
  : debit_invariant_ twos d0 -> debit_invariant_ twos' d0.
Proof.
  revert twos twos' H; induction d0; cbn [debit_invariant_]; auto.
  intros twos twos' H [H1 H2]; split.
  - lia.
  - revert H2; apply IHd0; lia.
Qed.

(** ** Debit invariant theorem for [pay_debit] *)

(* Theorems:
   - [pay_debit_cost]
   - [pay_debit_invariant]
 *)

(* Logarithmic bound on the cost of [pay_debit]. *)
Lemma pay_debit_cost {i : N} (s : stack_ i) (d : debit_ s)
  : fst (pay_debit d) <= depth_ s.
Proof.
  induction d; cbn - [N.add];
    try remember (fst _);
    try remember (depth_ _);
    try lia.
Qed.

(* Debit invariant for [pay_debit]: the invariant is preserved. *)
Lemma pay_debit_invariant {i : N} (s : stack_ i) (d : debit_ s)
  : forall (twos : N), debit_invariant_ twos d -> debit_invariant_ (twos - 1) (snd (pay_debit d)).
Proof.
  induction d; cbn - [N.add].
  all: auto.
  (* Two *)
  intros twos [I J]. split; [ lia | ].
  specialize (IHd (twos + i) J).
  revert IHd.
  apply debit_invariant_monotone.
  lia.
Qed.

(** ** Debit invariant theorem for [push_debit] *)

(* Main theorems:
   - [push_debit_invariant]
   - [push_acost]
 *)

(* At the same time, we also prove the upper bound on the final cost
   (for this theorem we must prove the two results simultaneously as they depend on
   each other). *)

Lemma push_debit_invariant_ {i : N} {w : array i} {s : stack_ i} (d : debit_ s)
  : debit_invariant_ 0 d ->
    fst (push_debit_ (w := w) d) <= i + depth_ s /\ debit_invariant_ (i - 1) (snd (push_debit_ (w := w) d)).
Proof.
  induction d; cbn - [N.mul N.add N.sub].
  - split; lia.
  - intros I; split; [ | split ]; [ lia | lia | revert I; apply debit_invariant_monotone; lia ].
  - intros [I J]. split.
    + pose proof (pay_debit_cost d). remember (fst _). lia.
    + revert J; apply pay_debit_invariant.
  - intros I.
    specialize (IHd (concat y z) I).
    destruct IHd as [ J K ].
    split; [ | split ].
    + remember (fst _). lia.
    + remember (fst _). lia.
    + revert K; apply debit_invariant_monotone; lia.
Qed.

Lemma push_debit_invariant {a : A} {s : stack} (d : debit s)
  : debit_invariant d -> debit_invariant (snd (push_debit a d)).
Proof.
  apply (push_debit_invariant_ d).
Qed.

Lemma push_acost {a : A} {s : stack} (d : debit s)
  : debit_invariant d -> fst (push_debit a d) <= 1 + depth s.
Proof.
  apply (push_debit_invariant_ d).
Qed.

(** ** The case of [pop] *)

(* We use the same recipe:
   1. Decorate [pop] into a function on debit structures ([pop_debit])
   2. Prove debit preservation ([pop_debit_preservation])
   3. Prove the same debit invariant holds ([pop_debit_invariant])
   4. Prove a logarithmic upper bound on the amortized cost of [pop] ([pop_acost])
 *)

(* The story for [pop] is trickier because it returns an optional result.
   We extend the debit structure to the result type of [pop]:
   one case for [None], one case for [Some].
   It is important to make this an inductive type, to make dependent
   pattern-matching work nicely in [pop_debit_] and in proofs.

   An alternative way to define this is as a definition,
   by pattern-matching directly on the index stack, but it's somwhow
   more awkward. In particular, some uses of [destruct] may fail.

   Later, theorems will be restricted to the [Some] case.
   using the proof terms of [isSome] assumptions to unwrap the result of
   [debit_Some].

   Although there won't be a proof about the [None] case,
   it's pretty obvious that it only happens when the stack is [Empty]
   so it takes constant time.
 *)

Inductive ioption {T : Type} (F : T -> Type) : option T -> Type :=
| iNone : ioption F None
| iSome t : F t -> ioption F (Some t)
.
Arguments iNone {T F}.
Arguments iSome {T F}.

(* Debit structure indexed by the result of [pop_] *)
Definition debit_option_ {i : N} : option (array i * stack_ i) -> Type :=
  ioption (fun '(_, s) => (N * debit_ s)%type).

(* Debit structure indexed by the result of [pop] *)
Definition debit_option : option (A * stack) -> Type :=
  ioption (fun '(_, s) => (N * debit s)%type).

(** *** Dependently typed programming with option types *)

Definition isSome {T} (ox : option T) : Prop :=
  match ox with
  | None => False
  | Some _ => True
  end.

Definition isNone {T} (ox : option T) : Prop :=
  match ox with
  | None => True
  | Some _ => False
  end.

Notation absurd := (fun contra => match contra in False with end).

(* If we have a proof that an [option T] is a [Some], then we can
   extract its contents [T]. *)
Definition unwrap {T} {ox : option T} : isSome ox -> T :=
  match ox with
  | None => absurd
  | Some x => fun _ => x
  end.

Definition inv_bind_option_l {T U} {ox : option T} {k : T -> option U}
  : isSome (bind_option ox k) -> isSome ox :=
  match ox with
  | None => absurd
  | Some _ => fun _ => I
  end.

(* Unwrap a [debit_option_] which is indexed by a [Some]. *)
Definition uw {T} {i : N} {o : option (T * stack_ i)}
    (w : ioption (fun '(_, s) => (N * debit_ s)%type) o)
  : forall (SOME : isSome o), N * debit_ (snd (unwrap SOME)) :=
  match w with
  | iNone => absurd
  | iSome _ x => fun _ => x
  end.

(** *** Lifting [pop] on debit structures *)

Fixpoint pop_debit_ {i : N} {s0 : stack_ i} (d0 : debit_ s0)
  : debit_option_ (pop_ s0) :=
  match d0 with
  | debit_Empty => iNone
  | debit_One d =>
    iSome (_, _)
      match pop_debit_ d in ioption _ E return N * debit_ (lower E) with
      | iNone => (0, debit_Empty)
      | iSome _ (n, d') =>
        let '(i', n') := take i n in
        (n', debit_Two (i + i') d')
      end
  | debit_Two m d =>
    let '(n, d') := pay_debit d in
    iSome (_, _) (m + n, debit_One d')
  | debit_Three d =>
    iSome (_, _) (0, debit_Two 0 d)
  end.

Definition pop_debit {s : stack} (d : debit s)
  : debit_option (pop s) :=
  match pop_debit_ d in ioption _ E return debit_option (match E with Some _ => _ | None => _ end) with
  | iNone => iNone
  | iSome _ (n, d') => iSome (_, _) (n, d')
  end.

(** *** Debit preservation *)

Lemma pop_debit_preservation_ {i : N} {s : stack_ i} (d : debit_ s)
  : forall (SOME : isSome (pop_ s)),
     total_pair debit_sum_ (uw (pop_debit_ d) SOME) = debit_pop_ s + debit_sum_ d.
Proof.
  induction d; cbn - [ N.add N.mul ]; intros SOME.
  - contradiction.
  - assert (pop_ s = None -> eq_dep _ debit_ Empty debit_Empty s d).
    { destruct d; discriminate + constructor. }
    destruct pop_debit_; cbn - [N.mul N.add].
    + destruct (H eq_refl).
      reflexivity.
    + specialize (IHd I).
      unfold total_pair; cbn - [N.mul].
      unfold total_pair in IHd; cbn - [N.mul] in IHd.
      remember (fst _).
      remember (debit_sum_ (snd _)).
      lia.
  - pose proof (pay_debit_preservation d).
    cbv beta iota delta [ fst snd total_pair ] in *.
    cbn [debit_sum_] in *.
    lia.
  - reflexivity.
Qed.

Lemma pop_debit_preservation {s : stack} (d : debit s)
  : forall (SOME : isSome (pop s)),
      total_pair debit_sum_ (uw (pop_debit d) SOME) = debit_pop_ s + debit_sum d.
Proof.
  unfold pop_debit.
  unfold pop in *.
  pose proof (pop_debit_preservation_ d) as H.
  destruct (pop_debit_ _); cbn.
  - contradiction.
  - apply H.
Qed.

(** *** Debit invariant *)

Lemma pop_debit_invariant_ {i : N} {s : stack_ i} (d : debit_ s)
  : forall (SOME : isSome (pop_ s)),
      debit_invariant_ 0 d ->
      let f := uw (pop_debit_ d) SOME in
      debit_invariant_ (i - 1) (snd f).
Proof.
  induction d; cbn - [N.add N.mul].
  - contradiction.
  - intros _ Inv.
    destruct pop_debit_; cbn - [N.mul N.add].
    + exact I.
    + specialize (IHd I Inv).
      split; [ lia | revert IHd; apply debit_invariant_monotone; lia ].
  - intros _ [Hn Inv].
    revert Inv.
    apply pay_debit_invariant.
  - intros _ Inv.
    split; [ lia | revert Inv; apply debit_invariant_monotone; lia ].
Qed.

Lemma pop_debit_invariant {s : stack} (d : debit s)
  : forall (SOME : isSome (pop s)),
      debit_invariant d ->
      let f := uw (pop_debit d) SOME in
      debit_invariant (snd f).
Proof.
  unfold pop_debit.
  unfold pop in *.
  pose proof (pop_debit_invariant_ d) as H.
  destruct (pop_debit_ _); cbn.
  - contradiction.
  - apply H.
Qed.

(** *** Amortized cost of [pop] *)

Lemma pop_acost_ {i : N} {s : stack_ i} (d : debit_ s)
  : forall (SOME : isSome (pop_ s)),
      debit_invariant_ 0 d ->
      let pop_d := uw (pop_debit_ d) SOME in
      fst pop_d <= i + depth_ s.
Proof.
  induction d; cbn - [N.mul N.add] in *.
  - contradiction.
  - intros _ Inv.
    destruct (pop_debit_ d); cbn - [N.mul N.add] in *.
    + lia.
    + specialize (IHd I Inv).
      remember (fst _).
      lia.
  - intros _ [Hn Inv].
    pose proof (pay_debit_cost d).
    remember (fst _).
    lia.
  - lia.
Qed.

Lemma pop_acost {s : stack} (d : debit s)
  : forall (SOME : isSome (pop s)),
      debit_invariant d ->
      let pop_d := uw (pop_debit d) SOME in
      fst pop_d <= 1 + depth s.
Proof.
  unfold pop_debit.
  unfold pop in *.
  pose proof (pop_acost_ d) as H.
  destruct (pop_debit_ _); cbn.
  - contradiction.
  - apply H.
Qed.

End STACK.

Print Assumptions push_acost.
Print Assumptions pop_acost.
