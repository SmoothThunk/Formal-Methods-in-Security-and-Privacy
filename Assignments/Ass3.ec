(*
 * Name: Shriya Thakur
 * Date started: Feb 15th, 2024
 * Hours worked on: took me forever, 1 day late but the proofs are complete now instead
 * of 3 admits that I had in the #3 proof in my previous submission by editing the seq
 * and while invariant
*)

(* Assignment 3 - EasyCrypt's Relational Hoare Logic and Noninterference

   Due Tuesday, February 27, at 11:59pm on Gradescope *)

require import AllCore.

prover quorum=2 ["Alt-Ergo" "Z3"].

(* QUESTION 1 (33 points)

   Prove the lemma M_noninter showing noninterference of the procedure
   `M.f`, using only the tactics

     `proc`, `seq`, `auto`, `if{1}` and `if{2}`,

   with the additional restriction that

     `auto` may only be used when both programs consist *entirely*
     of assignments

   Structure your proof so each tactic application is on a single
   line, and you don't use the tactic combinator `;`. It must be
   possible to step through your proof and check that each application
   of `auto` meets the above restriction. *)

module M = {
  var x : int  (* private *)
  var y : int  (* public *)
  var z : int  (* private *) 

  proc f() : unit = {
    y <- 1;
    z <- 0;
    if (x = 0) {
      z <- 1;
    }
    if (z = 0) {
      y <- 1;
    }
  }
}. 

lemma M_noninter :
  equiv [M.f ~ M.f : ={M.y} ==> ={M.y}].
proof.
proc.
(* Isolate assignments *)
seq 1 2: (={M.y} /\ M.y{1}=1 /\ M.y{2}=1).
(* Program consists entirely of assignments so can use auto *)
auto.
(* Handle first if statement *)
if{2}.
seq 1 1: (={M.y} /\ M.y{1}=1 /\ M.y{2}=1).
(* Just assignments so use auto *)
auto.
if{1}.
seq 1 1: (={M.y} /\ M.y{1}=1 /\ M.y{2}=1).
if{2}.
auto.
auto.
if{1}.
auto.
auto.
if{1}.
if{2}.
auto.
auto.
if{2}.
auto.
auto.

if{2}.
seq 1 1: (={M.y} /\ M.y{1}=1 /\ M.y{2}=1).
auto.
if{1}.
seq 1 1: (={M.y} /\ M.y{1}=1 /\ M.y{2}=1).
auto.
if{1}.
auto.
auto.
if{1}.
auto.
auto.
seq 1 1: (={M.y} /\ M.y{1}=1 /\ M.y{2}=1).
auto.
if{1}.
seq 1 1: (={M.y} /\ M.y{1}=1 /\ M.y{2}=1).
auto.
if{1}.
auto.
auto.
if{1}.
auto.
auto.
qed.

(* Note to self: 
 1. The assertion M.y{1}=1 is included in the intermediate 
    conditions at each step, ensuring that the value of M.y remains unchanged 
    and equal to 1 throughout the execution of the procedure M.f.

 2. The auto tactic is used to handle the straightforward case for when
    the program consists entirely of assignments.

 3. Shorten this if time permits
*)




(* QUESTION 2 (34 points)

   Prove the lemma N_noninter showing noninterference of the procedure
   N.f. *)

module N = {
  var x : int   (* private *)
  var y : int   (* private *)
  var i : int   (* public *)
  var b : bool  (* public *)

  proc f() : unit = {
    y <- 0;
    if (x < 0) {
      while (0 < i) { 
        y <- y + 1;
        i <- i - 1;
      }
    }
    else {
      while (0 < i) {
        y <- y + 2;
        i <- i - 1;
      }
    }
    b <- 0 <= y;
  }
}.

lemma N_noninter :
  equiv [N.f ~ N.f : ={N.i, N.b} ==> ={N.i, N.b}].
proof.
(* BEGIN FILL IN *)
proc.
wp.
sp.
(* seq 1 1: (={N.i, N.b}). *)
(* Just assignments so use auto *)
if{1}.
if{2}.
(* while loop invariant similar to the one in #1 *)
while(={N.i} /\ 0 <= N.y{1} /\ 0 <= N.y{2}).
auto.
progress.
smt().
smt().
auto.
progress.
smt().
while(={N.i} /\ 0 <= N.y{1} /\ 0 <= N.y{2}).
auto.
progress.
smt().
smt().
auto.
progress.
smt().
if{2}.
while(={N.i} /\ 0 <= N.y{1} /\ 0 <= N.y{2}).
auto.
progress.
smt().
smt().
auto.
progress.
smt().
while(={N.i} /\ 0 <= N.y{1} /\ 0 <= N.y{2}).
auto.
progress.
smt().
smt().
auto.
progress.
smt().
(* Not sure if there is a more elegant way than to spam relatively 
simialr code n times or more *)
qed.


(* END FILL IN *)

(* QUESTION 3 (33 points)

   Prove the lemma L_noninter, which expresses the noninterference of
   the procedure `N.f` using Hoare logic, in a style suggested in
   the last lecture on Relational Hoare Logic.

   In the module L, we have made two copies of the variables of
   module N, and the procedure L.f has two copies of the code
   of N.f, each operating on its own copy of the variables.

   Assuming L.f terminates for all memories (it does), the executions
   of the two copies proceed independently, and the lemma faithfully
   expresses noninterference. *)

module L = {
  (* variables of first copy *)
  var x  : int   (* private *)
  var y  : int   (* private *)
  var i  : int   (* public *)
  var b  : bool  (* public *)

  (* variables of second copy *)
  var x' : int   (* private *)
  var y' : int   (* private *)
  var i' : int   (* public *)
  var b' : bool  (* public *)

  proc f() : unit = {
    (* code of first copy *)
    y <- 0;
    if (x < 0) {
      while (0 < i) { 
        y <- y + 1;
        i <- i - 1;
      }
    }
    else {
      while (0 < i) {
        y <- y + 2;
        i <- i - 1;
      }
    }
    b <- 0 <= y;

    (* code of second copy *)
    y' <- 0;
    if (x' < 0) {
      while (0 < i') { 
        y' <- y' + 1;
        i' <- i' - 1;
      }
    }
    else {
      while (0 < i') {
        y' <- y' + 2;
        i' <- i' - 1;
      }
    }
    b' <- 0 <= y';
  }
}.

lemma L_noninter :
  hoare [L.f : L.i = L.i' /\ L.b = L.b' ==> L.i = L.i' /\ L.b = L.b'].
proof.
(* BEGIN FILL IN *)
proc.
(* What I know at the end and what I need to know for the scond half program *)
(* Case i is not positive so loops dont run *)
case (L.i <= 0).
seq 3: (L.i <= 0 /\ L.y = 0 /\ L.i = L.i' /\ L.b = 0 <= L.y).
wp.
sp.
if.
while(L.y=0 /\ L.i = L.i' /\ ! 0 < L.i').
auto.
auto.
progress.
smt().

while(L.y=0 /\ L.i = L.i' /\ ! 0 < L.i').
auto.
auto.
progress.
smt().

wp.
sp.
if.
while(L.y=0 /\ L.i = L.i' /\ ! 0 < L.i' /\  0 <= L.y').
auto.
auto.
progress.
smt().
smt().


while(L.y=0 /\ L.i = L.i' /\ ! 0 < L.i' /\  0 <= L.y').
auto.
auto.
progress.
smt().
smt().


(* In the next case statement *)
(* seq 3: (0 <= L.i  /\ L.b = true /\ 0 <= L.i'). *)
(* seq 3: (0 < L.i /\ L.i = L.i' /\ L.b /\ ! L.i <= 0). *)
seq 3: (0 <= L.y /\ L.i = 0 /\ 0 <= L.i'/\ L.b = 0 <= L.y).
wp.
sp.
if.
while(0 <= L.y /\ 0 <= L.i).
auto.
progress.
smt().
smt().
auto.
progress.
smt().
smt().
smt().

while(0 <= L.y /\ 0 <= L.i).
auto.
progress.
smt().
smt().
auto.
progress.
smt().
smt().
smt().

(* 2nd half of next case *)
(* Added L.i = L.i' and added precise value of L.i after first program *)
(* seq 3: (0 <= L.i' /\ L.b' = true /\ L.b = 0 <= L.y /\ L.i = 0 /\ L.i = L.i'). *)
seq 3: (0 <= L.i' /\ L.b' = true /\ L.b = true /\ L.i = 0 /\ L.i = L.i').
wp.
sp.
if.
(* Include precise value of L.i from first program *)
while(0 <= L.i' /\ 0 <= L.y'/\ L.i = 0 /\ 0 <= L.y).
auto.
progress.
smt().
smt().
auto.
progress.
smt().
smt().
smt().

while(0 <= L.i' /\ 0 <= L.y' /\ L.i = 0 /\ 0 <= L.y).
auto.
progress.
smt().
smt().
auto.
progress.
smt().
smt().
smt().
auto.
qed.
(* END FILL IN *)

