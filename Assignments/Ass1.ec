(* Assignment 1 - EasyCrypt's Ambient Logic

   Due Friday, February 2, at 11:59pm on Gradescope

   In this assignment, you should (for full credit) make good use of
   the advanced proof features illustrated in the labs and described
   in the slides on the Ambient Logic, with the goal of producing
   concise, elegant proofs.

   If you have trouble with a lemma or a part of a lemma, you may
   use `admit` for the proof of that lemma or lemma part. You can
   always come back later to these steps and try to complete them. *)

(*
 * Name: Shriya Thakur.
 * Start date: Saturday January 26th, 2023.
 * Status: Still incomplete
 * Note: The condensed versions follow after the comment blocks for each proof. 
 * I left it in there just so I can refer back if I need to at some point in
 * the future.
*)

require import AllCore.

require import IntDiv StdOrder.

import IntOrder.

(* QUESTION 1 (34 Points)

   In this question, two of the lemmas are proved for you, but you
   must prove the remaining four. You must prove the lemmas in order,
   as later lemmas may use earlier ones. You may not introduce
   additional lemmas.

   You may not use the `smt` or `case` tactics, or any of the lemmas
   of the EasyCrypt Library. (`smt` can also be invoked using `/#` in
   an introduction pattern or application of `rewrite`; you may not
   use that either. There is a version of `elim` that, like `case`,
   lets one work with truth tables; you may not use that version of
   `elim` either. You may use the version of `elim` for eliminating
   hypotheses (assumptions), as we did in the labs). *)

(* trivial proves this; you may use it below *)

lemma not_intro (a : bool) :
  (a => false) => ! a.
proof. trivial. qed.

(* we proved the following lemma in lab, but by using `case`, which
   you may not use *)

lemma negb_or (a b : bool) :
  ! (a \/ b) <=> ! a /\ ! b.
(* split.
(* Assume LHS is true then prove RHS *)
(* Use Intro pattern *)
move => not_or.
(* Use split tactic, will increase goals *)
split.
(* Goal looks like can be proved by proved lemma above *)
apply (not_intro (a) ).
move => a_true.
(* Have to prove false so use proof by contradiction *)
have contrad : (a \/ b).
left.
trivial.
trivial.
(* Identical case for !b *)
apply (not_intro (b) ).
move => b_true.
(* Use proof by contradiction to prove *)
have contrad : (a \/ b).
right.
trivial.
trivial.
(* Prove !a /\ !b => ! (a \/ b) *)
(* Assume LHS then prove RHS *)
move => not_and.
apply (not_intro (a \/ b) ).
move => or.
elim not_and.
(* Would really rather have conjuncts individually *)
(* If we know is false then if we know b is false then the conclusion *)
move => a_false.
move => b_false.
elim or.
move => a_true.
(* Have a and !a in the context so can use trivial *)
trivial.
move => b_true. 
(* Have b and !b in the context so can use trivial *)
trivial.
qed.
*)

(* Condensed version *)
(* BEGIN FILL IN *)
proof.
split => [not_or | [] not_a not_b].
split.
apply not_intro.
move => a_true.
have // : a \/ b by left.
apply not_intro.
move => b_true.
have // : a \/ b by right.
apply not_intro.
move => a_or_b.
by elim a_or_b.
qed.
(* END FILL IN *)

(* trivial proves this; you may use it below *)
lemma by_contradiction (a : bool) :
  (! a => false) => a.
proof. trivial. qed.

lemma excluded_middle (a : bool) :
  a \/ !a.

(*apply (by_contradiction (a \/ !a) ).
move => a_or_not_a.
have contrad : (a \/ !a).
case a. (* CANNOT USE!!! *)
move => a_true.
trivial.
move => not_a.
trivial.
trivial.
qed.*)

(* BEGIN FILL IN *)
(* Rewrite without case and condense *)
proof.
apply (by_contradiction (a \/ !a)).
move => not_a_or_not_a.
have contrad : a \/ !a.
right.
apply (not_intro(a)).
move => a_true.
by have //: a \/ !a by left.
trivial.
qed.
(* END FILL IN *)

lemma negb_and (a b : bool) :
  ! (a /\ b) <=> ! a \/ ! b.
proof.
(* Prove ! (a /\ b) => !a /\ !b *)
(*split.
move => not_and.
case a.
move => a_true.
simplify.
apply (not_intro(b)).
move => b_true.
have contrad : (a /\ b).
trivial.
(*Contradiction and hypothesis both in context so trivial *)
trivial.
case b.
move => b_true.
trivial.
trivial.
*)

(* !a \/ !b => ! (a /\ b) *)
(*move => not_or.
apply (not_intro (a /\ b) ).
move => or.
elim or.
move => a_true b_true.
elim not_or.
move => not_a.
trivial.
move => not_b.
trivial.
*)

(* BEGIN FILL IN *)

(* Without case *)
split.
move => not_and.
apply (by_contradiction (!a \/ !b)).
move => not_not_a_or_not_b.
apply not_not_a_or_not_b.
left.
apply (not_intro(a)).
move => a_true.
apply not_not_a_or_not_b.
right.
apply (not_intro(b)).
move => b_true.
apply not_and.
trivial.


(* !a \/ !b => ! (a /\ b) *)
move => not_or.
elim not_or.
move => not_a.
apply not_intro.
move => a_and_b.
elim a_and_b => a_true b_true.
trivial.

move => not_b.
apply not_intro.
move => a_and_b.
elim a_and_b => a_true b_true.
trivial.
qed.
(* END FILL IN *)


lemma negb_imply (a b : bool) :
  ! (a => b) <=> a /\ ! b.
proof.
(*split.
(* Prove ! (a => b) => a /\ !b *)
move => not_imply.
split.
case a.
trivial.
move => a_false.
have contrad : (a => b).
move => a_true.
trivial.
trivial.
apply ( not_intro(b) ).
move => b_true.
have contrad : (a => b).
move => a_true.
trivial.
trivial.

(* Prove a /\ !b => ! (a => b) *)
move => a_and_not_b.
elim a_and_not_b.
move => a_true b_false.
case a.
trivial.
trivial.
qed.*)

(* BEGIN FILL IN *)
(* Without case *)
split.
move => not_imply.
split.
apply by_contradiction.
move => not_a.
apply not_imply.
move => a_true.
trivial.
apply not_intro.
move => b_true.
apply not_imply.
move => a_true.
assumption.

(* a /\ !b => ! (a => b) *)
move => and_not.
apply not_intro.
move => imply.
elim and_not.
move => a_true.
move => b_false.
apply b_false.
trivial.
have // : a => !b.
trivial.
move => a_imply_not_b.
trivial.
apply imply.
assumption.
qed.
(* END FILL IN *)

(* QUESTION 2 (33 Points)

   In this question, you may not use `smt` (or `/#`) or any lemmas
   from the EasyCrypt Library, but you may use all other tactics. *)

lemma exists_or_iff (P Q : 'a -> bool) :
  (exists (x : 'a), P x \/ Q x) <=>
  (exists (x : 'a), P x) \/ (exists (x : 'a), Q x).
proof.
(* BEGIN FILL IN *)
split.
move => [x p_or_q].


(* elim p_or_q.
move => P_x.*)
elim p_or_q => [p_x | q_x].
left.
exists x.
trivial.
(* We know right side over here *)
right.
(* Eliminate existential here *)
exists x.
move => //.

(* Prove exists x, P x \/ exists x, Q x => exists x, P x \/ Q x *)
move => [].
move => [x P_x].
exists x.
left.
trivial.

move => [x Q_x].
exists x.
right.
trivial.
qed. 
(* END FILL IN *)

lemma forall_and_iff (P Q : 'a -> bool) :
  (forall (x : 'a), P x /\ Q x) <=>
  (forall (x : 'a), P x) /\ (forall (x : 'a), Q x).
proof.
(* BEGIN FILL IN *)
split.
move => forall_p_or_q.
(* move => x *)
split.
move => x.
(* Prove sublema without forall *)
have P_x_and_Q_x : P x /\ Q x.
apply forall_p_or_q.
elim P_x_and_Q_x.
trivial.

(* Prove for the other direction *)
move => x.
have P_x_and_q_x : P x /\ Q x.
apply forall_p_or_q.
elim P_x_and_q_x.
trivial.


(* Proving (forall (x : 'a), P x) /\ (forall (x : 'a), Q x) =>  
(forall (x : 'a), P x /\ Q x) *)
move => forall_P_x_and_forall_Q_x.
move => x.
elim forall_P_x_and_forall_Q_x.

move => forall_P_x forall_Q_x.
have P_and_Q : P x /\ Q x.
(* Eliminate and to get each conjunct *)
split.
(* apply from assumptions in context *)
apply forall_P_x.
apply forall_Q_x.
trivial.
qed.
(* END FILL IN *)


(* QUESTION 3 (33 Points)

   In this problem, you may not use `smt` (or `/#'), but you may use
   all other tactics as well as all lemmas of the EasyCrypt Library.

   You may prove whatever auxiliary lemmas you need.

   (Hint: do a `print` of the operator `odd`, and then search for
   related lemmas.) *)

(* operators and lemmas about integer division, and lemmas about the
   standard ordering on the integers *)

(*

n %/ x is the integer division of n by x.

n %% x is the remainder of integer division of n by x.

x %| n tests whether x divides n ; aka if n %% x == 0

*)

require import IntDiv StdOrder.
import IntOrder.

(* definition of being a prime number *)

op is_prime (n : int) : bool =
  2 <= n /\
  ! exists (x : int), x %| n /\ 1 < x < n.
(* n is atleast 2 or there exists an x such that x evenly divides n and 
 and lies between 1 and n 
*)

(* BEGINNING OF AUXILIARY LEMMAS *)

(* Can prove a lemma that any even prime number equals 2 then use on the goal 
below after case 
*)
lemma even_prime_equals_2 (n : int) : is_prime n /\ !odd(n) => n = 2.
proof.
move => is_prime_even.
elim is_prime_even.
move => is_prime_n.
move => not_odd.
admit.
qed.
(* END OF AUXILIARY LEMMAS *)

(* if n and n + 1 are both prime, then n = 2 *)
lemma adjacent_primes_uniq_2 (n : int) :
  is_prime n => is_prime (n + 1) => n = 2.
proof.
(* BEGIN FILL IN *)
rewrite /is_prime.
move => a [b c].
elim a => [n_geq_2 d].
(* Case: If n is even and prime *)
(* Case: if (n+1) is even and prime *)
(* Might help if I can prove a lemma for if a number is even and prime then it is 2 *)
case (odd(n)).
(* apply even_prime_equals. *)
admit.
apply by_contradiction.
progress.
admit.
(* Can prove that n is >= 3 and then prove contradiction from there *)
(*have contrad : 3 <= n.
search (<=).*)
(* END FILL IN *)
qed.



op dvdz_ge1 (x n : int) : bool =
1 <= x /\ x %| n.

lemma div_le (x n : int) :
1 <= n => dvdz_ge1 x n => x <= n.
proof.
(* Unfold the operator *)
rewrite /dvdz_ge1.
(* Move into the context *)
move => ge1_n.
move => [].
move => ge1_x.
move => x_dvdz_n.
have n_eq : n = (n %/ x) * x.
rewrite eq_sym.
rewrite -dvdz_eq.
trivial.
rewrite (lez_trans 1).
trivial.
admit.
trivial.
qed.
