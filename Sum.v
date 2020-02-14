(**
 * Import the arithmetics library
 *)
Require Import Arith.

(**
 * Import the list library
 *)
Require Import List.
Import ListNotations.

(**
 * times two
 *)
Definition double (n:nat) : nat :=
  n * 2.
Eval compute in double 4.
Eval compute in double (double 4).

(* In JS:
function double(n) {
  return n * 2;
}
console.log(double(4));
console.log(double(double(4)));
*)

(**
 * A map function on lists
 *)
Eval compute in (map double [1;2;3]).

(* In JS:
console.log([1,2,3].map(double);
*)

(**
 * Sum of a list of integers
 *)
Fixpoint sum (l:list nat) : nat :=
  match l with
  | nil => 0
  | x :: l1 => x + (sum l1)
  end.
Eval compute in sum (1::2::3::nil).
Eval compute in sum (1::2::3::4::nil).

(* In JS:
function sum(l) {
  if (l.length === 0) {
    return 0;
  } else {
    const x = l.pop();
    const l1 = l; // Because pop changes l
    return x + sum(l1);
  }
}
console.log(sum([1,2,3]));
console.log(sum([1,2,3,4]));
*)

(* Question in JS:
   can I safely replace
     sum(l.map(double))
   by
     double(sum(l))
 *)
(* Bonus question: which one is more efficient? *)

Definition f1 l := sum (map double l).
Definition f2 l := double (sum l).
Eval compute in f1([1;2;3]).
Eval compute in f2([1;2;3]).
(* In JS:
function f1(l) {
  return sum(l.map(double));
}
function f2(l) {
  return double(sum(l));
}
console.log(f1([1,2,3]));
console.log(f2([1,2,3]));
*)

Lemma sum_double:
  forall l, sum (map double l) = double (sum l).
Proof.
  intro l.
  induction l.
  - simpl.
    unfold double.
    simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    unfold double.
    Search mult.
    rewrite Nat.mul_add_distr_r.
    reflexivity.
Qed.

(**
 * Now we can "extract" our code to something more efficient like OCaml
 *)
Require Extraction.
Extraction Language OCaml.        (* Could be Haskell... *)
Require Import ExtrOcamlNatInt.   (* Coq natural numbers are OCaml integers *)

Extraction "sum" f1 f2.

