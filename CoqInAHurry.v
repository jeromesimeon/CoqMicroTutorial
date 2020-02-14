(* Check tells you the type of something *)
Check True.
Check False.
Check 3.
Check (3+4).
Check (3=5).
Check (3,4).
Check ((3=5)/\True).
Check nat -> Prop.
Check (3<=6).

Check (fun x:nat => x = 3).
Check (forall x:nat, x < 3 \/ (exists y:nat, x = y + 3)).
Check (let f := fun x => (x * 3, x) in f 3).

(* Locate tells you where something is defined *)
Locate "_ <= _".
Locate and. 

(* Eval can evaluate things *)
Eval compute in
  let f := fun x => x * 3 + x in f 3.
(* In JS:
const f = (x) => { return x * 3 + x };
console.log(f(3));
*)

Check (let f:= fun x y z a b => (x + y + z + a + b) in f 1 2 3 4 5).

Eval compute in 
  let f:= fun x y z a b => (x + y + z + a + b) in f 1 2 3 4 5.
(* In JS:
const f = (x,y,z,a,b) => { return x + y + z + a + b };
console.log(f(1,2,3,4,5));
*)

(* Global definitions *)
Definition example1 := fun x : nat => x*x+2*x+1.
Definition example11 (x : nat) := x*x+2*x+1.

Eval compute in example1 1.

(* Import a library *)
Require Import Bool.

Eval compute in if true then 3 else 5.

(* Search can tell you about lemmas *)
Search bool.

Require Import Arith.

Definition is_zero (n:nat) :=
  match n with
    0 => true
  | S p => false
  end.

Print pred.

(* This is a recursive function *)
Fixpoint sum_n n :=
  match n with
    0 => 0
  | S p => p + sum_n p
  end.

Eval compute in sum_n 2.

(* Coq functions always terminate *)
(*Fixpoint rec_bad n :=
  match n with
    0 => 0
  | S p => rec_bad (S p)
  end.*)

Fixpoint sum_n2 n s :=
  match n with
    0 => s
  | S p => sum_n2 p (p + s)
  end.

Fixpoint evenb n :=
  match n with
    0 => true
  | 1 => false
  | S (S p) => evenb p
  end.

Require Import List.

Check 1::2::3::nil.

Check nil.

Check (nil: list nat).

Eval compute in map (fun x => x + 3) (1::3::2::nil).

Eval compute in map S (1::22::3::nil).

Eval compute in
  let l := (1::2::3::nil) in l ++ map (fun x => x + 3) l.

Fixpoint tolist n:=
  match n  with
    0 => nil
  | S p => (tolist p) ++ p::nil
  end.

Eval compute in tolist 10.

Definition head_evb l :=
  match l with
    nil => false
  | a::tl => evenb a
  end.

Eval compute in head_evb (2::3::1::nil).
Eval compute in head_evb (nil).

Fixpoint sum_list l :=
  match l with
    nil => 0
  | n::tl => n + sum_list tl
  end.

Fixpoint insert n l :=
  match l with
    nil => n::nil
  | a::tl => if leb n a then n::l else a::insert n tl
  end.

Fixpoint sort l :=
  match l with
    nil => nil
  | a::tl => insert a (sort tl)
  end.

Eval compute in sort (1::4::3::22::5::16::7::nil).

Fixpoint lel l :=
  match l with
    nil => true
  | a::nil => true
  | a::b::tl => if leb a b then true else false
  end.

Fixpoint issorted l :=
  match l with
    nil => true
  | h::tl => if lel l then issorted tl else false
  end.

Eval compute in issorted (0::1::2::3::4::5::6::7::8::9::10::nil).

Print beq_nat.

Eval compute in beq_nat 1 2.
Eval compute in beq_nat 2 1.
Eval compute in beq_nat 1 1.

Fixpoint count_list l n :=
  match l with
    nil => 0
  | a::tl => if beq_nat n a then 1 + (count_list tl n) else count_list tl n
  end.

Search True.
Search le.

Lemma example2 : forall a b:Prop, a /\ b -> b /\ a.
Proof.
  intros a b H.
  split.
  destruct H as [H1 H2].
  exact H2.
  intuition.
Qed.

Lemma example3 : forall A B, A \/ B -> B \/ A.
Proof.
  intros A B H.
  destruct H as [H1 | H1].
  right; assumption.
  left; assumption.
Qed.