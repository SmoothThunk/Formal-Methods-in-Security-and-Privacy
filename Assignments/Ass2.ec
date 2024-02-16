(* Assignment 2 - EasyCrypt's Hoare Logic

   Due Thursday, February 15, at 11:59pm on Gradescope

   In this assignment you will be proving the partial correctness of
   an efficient, iterative implementation of the Fibonacci function in
   two ways:

   * first without `smt` and `auto`; and

   * second, where you should make good use of `smt` and `auto` *)

require import AllCore List IntDiv StdOrder.
import IntOrder.

(* First we need to define Fibonacci as a mathematical function.  We
   do this using EasyCrypt's well-founded recursion theory. You don't
   need to understand the details of how this is done; you can just
   use the lemmas fib0, fib1 and fib_ge2, whose proofs you are
   given, below. *)

(* well-founded relations, induction and recursion *)

require import WF.

(* body of well-founded recursive definition of the Fibonacci
   function *)

op fib_wf_rec_def : (int, int) wf_rec_def =
  fun (n : int,            (* the input *)
       f : int -> int) =>  (* for recursive calls on strictly
                              less than natural numbers *)
  if n = 0
    then 0
  else if n = 1
    then 1
  else f (n - 1) + f (n - 2).

(* the actual recursive definition of the Fibonacci function

   `nosmt` means the `smt` tactic may not unfold the operator's
    definition *)

op nosmt fib : int -> int =
  wf_recur
  lt_nat           (* well-founded relation being used *)
  0                (* element to be returned if recursive calls
                      don't respect well-founded relation *)
  fib_wf_rec_def.  (* body of recursive definition *)

(* `nosmt` means that the `smt` tactic can't use this lemma unless
   it is explicitly included in `smt(...)` *)

lemma nosmt fib0 :
  fib 0 = 0.
proof.
by rewrite /fib wf_recur 1:wf_lt_nat /fib_wf_rec_def.
qed.

lemma nosmt fib1 :
  fib 1 = 1.
proof.
by rewrite /fib wf_recur 1:wf_lt_nat /fib_wf_rec_def.
qed.

lemma nosmt fib_ge2 (n : int) :
  2 <= n => fib n = fib (n - 1) + fib (n - 2).
proof.
move => ge2_n.
rewrite /fib {1}wf_recur 1:wf_lt_nat {1}/fib_wf_rec_def.
have -> /= : ! (n = 0) by rewrite eq_sym ltr_eqF 1:ltzE 1:(lez_trans 2).
have -> /= : ! (n = 1) by rewrite eq_sym ltr_eqF 1:ltzE.
have -> /= : lt_nat (n - 1) n.
  rewrite /lt_nat; split => [| _].
  by rewrite subr_ge0 (lez_trans 2).
  rewrite ltr_subl_addr ltzS lezz.
have -> // : lt_nat (n - 2) n.
  rewrite /lt_nat; split => [| _].
  by rewrite subr_ge0.
  by rewrite ltr_subl_addr ltr_addl.
qed.

(* efficient implementation of Fibonacci *)

module Fib = {
  proc f(n : int) : int = {
    var i, l, m, t : int;
    if (n = 0) {
      m <- 0;
    }
    else {
      l <- 0; m <- 1; i <- 1;
      while (i < n) {
        t <- l;
        l <- m;
        m <- t + m;
        i <- i + 1;
      }
    }
    return m;
  }
}.





   
(* QUESTION 1 (60 points)

   Prove the following lemma without using the tactics `smt` and
   `auto`.

   Hint: learn about the introduction pattern `/>` ("crush") and/or
   the tactic `progress` (see the slides on the Ambient Logic). *)

prover [""].  (* no use of `smt` allowed *)

lemma fib_corr1 (n_ : int) :
  hoare [Fib.f : n = n_ /\ 0 <= n ==> res = fib n_].
proof.
(* BEGIN FILL IN *)
proc.
(* Simplify pre and post conditions *)
simplify.
(* If statement at the begining so can use if tactic *)
if.
(* Push assignments into post *)
wp.
(* skip will make it an ambient logic goal  + crush the goal *)
skip => />.
by rewrite fib0.

(* While is at the end so can use while tactic *)
(* Not sure if my while invariant is correct. Also have to use 
 l, m, i somehow in this *)
while (n <> 0 /\ 0 <= n /\ i < n /\ fib n_ = fib n_).
wp ; skip => /> ; progress.
admit.
(* Push assignments at the end of the program into the post condition *)
wp.
skip => />.
(* progress.*)
rewrite lezNgt.
progress.
(* so n_ is greater than or equal to 1 *)
have : 1 < n_.
search (<).
rewrite -lez_add1r.
simplify.
admit.
trivial.
qed.
(* END FILL IN *)



(* QUESTION 2 (40 points)

   Prove the following lemma, making good use of `smt` and `auto`
   (and without using fib_corr1).

   Hint: in order to get `smt` to use fib0, fib1 and fib_ge2, you must
   explicitly include them in `smt(...)`. In a given use of `smt(...)`,
   only include the lemmas that are needed. *)

prover quorum=2 ["Z3" "Alt-Ergo"].

lemma fib_corr2 (n_ : int) :
  hoare [Fib.f : n = n_ /\ 0 <= n ==> res = fib n_].
proof.
(* BEGIN FILL IN *)
proc.
simplify.
if.
auto.
progress.
smt(fib0).
while (n <> 0 /\ 0 <= n /\ i < n /\ fib n_ = fib n).
auto.
progress.
admit.
auto.
progress.
admit.
trivial.
(* END FILL IN *)
qed.
