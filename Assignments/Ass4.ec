(* Assignment 4 - EasyCrypt's Probabilistic Relational Hoare Logic
   and Probabilistic Noninterference

   Due Saturday, March 9, at 11:59pm on Gradescope *)

prover quorum=2 ["Alt-Ergo" "Z3"].
timeout 2.  (* limit SMT solvers to two seconds *)

(* NOTE: In this assignment, you will probably find that using
   smt(...) with the exclusive or lemmas (below) fails to solve some
   goals involving exclusive or that you know are true. If this
   happens, increasing the above timeout will probably not help.  The
   problem is that a solver sometimes goes down the wrong path, and
   fails to recover.

   Why does this happen? Consider a formula involving the exclusive or
   of a number of values:

     x1 ^^ x2 ^^ x3 ^^ ... ^^ xn

   Unless n is very small, there are many reorganizations of the
   formula using only xorA and xorC - and when you add in xorK and
   xor_ff, the number further explodes.

   The way to work around this problem is to state, prove and use
   AUXILIARY LEMMAS. For instance, you might prove a lemma that only
   needs associativity (cutting down the search space), and then use
   that to prove another lemma.

   If you try to use smt(...) and it doesn't respond IMMEDIATELY, then
   you should figure out what auxiliary lemma or lemmas will help. *)

require import AllCore Distr.

(* a type mybool with elements tt standing for "true" and ff standing
   for "false", and an exclusive or operator ^^: *)

type mybool = [tt | ff].

(* because tt is an alias for the value () : unit, you'll sometimes
   see Top.tt in goals for the value tt of mybool *)

op (^^) : mybool -> mybool -> mybool.

(* we can write x ^^ y instead of (^^) x y

   ^^ is left associatve, so x ^^ y ^^ z means (x ^^ y) ^^ z *)

(* axioms defining exclusive or (nosmt means these axioms aren't
   available to the SMT provers): *)

axiom nosmt xor_tt_tt : tt ^^ tt = ff.
axiom nosmt xor_tt_ff : tt ^^ ff = tt.
axiom nosmt xor_ff_tt : ff ^^ tt = tt.
axiom nosmt xor_ff_ff : ff ^^ ff = ff.

(* lemmas for exclusive or: *)

(* false on the right *)
lemma xor_ff (x : mybool) : x ^^ ff = x.
proof.
case x; [apply xor_tt_ff | apply xor_ff_ff].
qed.

(* cancelling *)
lemma xorK (x : mybool) : x ^^ x = ff.
proof.
case x; [apply xor_tt_tt | apply xor_ff_ff].
qed.

(* commutativity *)
lemma xorC (x y : mybool) : x ^^ y = y ^^ x.
proof.
case x.
case y => //.
by rewrite xor_tt_ff xor_ff_tt.
case y => //.
by rewrite xor_ff_tt xor_tt_ff.
qed.


(* associativity *)
lemma xorA (x y z : mybool) : (x ^^ y) ^^ z = x ^^ (y ^^ z).
proof.
case x.
case y.
rewrite xor_tt_tt.
case z.
by rewrite xor_ff_tt xor_tt_tt xor_tt_ff.
by rewrite xor_ff_ff xor_tt_ff xor_tt_tt.
case z.
by rewrite xor_tt_ff xor_tt_tt xor_ff_tt xor_tt_tt.
by rewrite xor_tt_ff xor_tt_ff xor_ff_ff xor_tt_ff.
case y.
rewrite xor_ff_tt.
case z.
by rewrite xor_tt_tt xor_ff_ff.
by rewrite xor_tt_ff xor_ff_tt.
case z.
by rewrite xor_ff_ff xor_ff_tt xor_ff_tt.
by rewrite xor_ff_ff xor_ff_ff.
qed.

(* a sub-distribution dmybool on mybool - this means that the sum of
   the values of tt and ff in dmybool may be less than 1 *)

op dmybool : mybool distr.

(* dmybool is a distribution, i.e., the sum of the values of tt and ff
   in dmybool is 1%r *)

axiom dmybool_ll : is_lossless dmybool.

(* if d is a sub-distribution on type 'a, and E is an event
   (predicate) on 'a (E : 'a -> bool), then mu d E is the probability
   that choosing a value from d will satisfy E

   if d is a sub-distribution on type 'a, and x : 'a, then mu1 d x is
   the probablity that choosing a value from d will result in x, i.e.,
   is the value of x in d

   mu1 is defined by: mu1 d x = mu d (pred1 x), where pred1 x is the
   predicate that returns true iff its argument is x *)

(* both tt and ff have value one-half in dmybool: *)

axiom dmybool1E (b : mybool) :
  mu1 dmybool b = 1%r / 2%r.

(* then we can prove that dmybool is full, i.e., that its support is
   all of mybool, i.e., that both tt and ff have non-zero values in
   dmybool. x \in d is an abbreviation for saying that x is in the
   support of d *)

lemma dmybool_fu : is_full dmybool.
proof.
rewrite /is_full => x.
rewrite /support dmybool1E StdOrder.RealOrder.divr_gt0 //.
qed.

(* QUESTION 1 (34 points)

   Prove the lemma M_noninter, showing the probabilistic
   noninterference of the procedure M.f *)

module M = {
  var x : mybool  (* private *)
  var y : mybool  (* private *)
  var z : mybool  (* public *)

  proc f() : unit = {
    var b : mybool;
    b <$ dmybool;
    z <- x ^^ b ^^ y;
  }
}.

(* BEGIN AUXILIARY LEMMAS *)
lemma xorC_for_three (a bL p: mybool):
a ^^ bL ^^ p = a ^^ p ^^ bL.
proof.
smt(xorA xorC).
qed.

lemma distribution_preservation (a b bL p q):
a ^^ bL ^^ p = b ^^ (a ^^ p ^^ b ^^ q ^^ bL) ^^ q. 
proof.
rewrite (xorC (a ^^ p) (b)).
rewrite (xorA (b) (a ^^ p) (q)).
rewrite (xorA (a) (p) (q)).
rewrite (xorC (a) (p ^^ q)).
rewrite (xorC (b) (b ^^ (p ^^ q ^^ a) ^^ bL) ).
rewrite (xorA (b) (p ^^ q ^^ a) (bL)).
rewrite (xorA (b) (p ^^ q ^^ a ^^ bL) (b)).
rewrite (xorC (p ^^ q ^^ a ^^ bL) (b)).
rewrite (xorC(b) (b ^^ (p ^^ q ^^ a ^^ bL))).
rewrite (xorC (b) (p ^^ q ^^ a ^^ bL)).
rewrite (xorA (p ^^ q ^^ a ^^ bL) (b) (b)).
rewrite (xorK (b)).
rewrite (xor_ff).
rewrite (xorC_for_three (p) (q) (a)).
rewrite (xorC_for_three (p ^^ a) (q) (bL)).
rewrite (xorA (p ^^ a ^^ bL) (q) (q)). 
rewrite (xorK (q)).
rewrite (xor_ff).
rewrite (xorA (p) (a) (bL)).
rewrite (xorC (a ^^ bL) (p)).
reflexivity. (* Could also use smt(xorA xorC) *)
qed.

(* END AUXILIARY LEMMAS *)

lemma M_noninter :
  equiv[M.f ~ M.f : ={M.z} ==> ={M.z}].
proof.
(* BEGIN FILL IN *)
proc.
wp.
rnd(fun u => M.x{1} ^^ M.y{1} ^^ M.x{2} ^^ M.y{2} ^^ u).
skip; progress.
smt(xorC xorA xorK xor_ff).
smt(dmybool1E).
smt(xorC xorA xorK xor_ff).
smt(xorC xorA xorK xor_ff).
(* Use auxiliary lemma here *)
apply distribution_preservation.
qed.
(* END FILL IN *)

(* QUESTION 2 (33 points)

   Prove the lemma N_noninter, showing the probabilistic
   noninterference of the procedure N.f *)

module N = {
  var w : mybool  (* private *)
  var x : mybool  (* private *)
  var y : mybool  (* public *)
  var z : mybool  (* public *)

  proc f() : unit = {
    var b, c : mybool;
    b <$ dmybool;
    c <$ dmybool;
    y <- w ^^ b;
    z <- x ^^ c;
  }
}.

(* BEGIN AUXILIARY LEMMAS *)
(* NO AUXILIARY LEMMAS WERE NEEDED *)
(* END AUXILIARY LEMMAS *)

lemma lem2 :
  equiv[N.f ~ N.f : ={N.y, N.z} ==> ={N.y, N.z}].
proof.
(* BEGIN FILL IN *)
proc.
wp.
seq 1 1: (N.w{1} ^^ b{1} = N.w{2} ^^ b{2} /\ ={N.y, N.z}).
rnd(fun u => N.w{1} ^^ N.w{2} ^^ u).
skip.
progress.
smt(xorC xorK xorA xor_ff).
smt(dmybool1E).
smt(dmybool_fu).
smt(xorC xorK xorA xor_ff).
smt(xorC xorK xorA xor_ff).

rnd(fun u => N.x{1} ^^ N.x{2} ^^ u).
skip.
progress.
smt(xorC xorK xorA xor_ff).
smt(dmybool1E).
smt(dmybool_fu).
smt(xorC xorK xorA xor_ff).
smt(xorC xorK xorA xor_ff).
qed.
(* END FILL IN *)

(* QUESTION 3 (33 points)

   Prove the lemma L_noninter, showing the probabilistic
   noninterference of the procedure L.f *)

module L = {
  var x : mybool  (* private *)
  var y : mybool  (* public *)

  proc f() : unit = {
    var b, b' : mybool;
    b <$ dmybool;
    b' <$ dmybool;
    y <- x ^^ b ^^ b';
  }
}.

(* BEGIN AUXILIARY LEMMAS *)
(* Didnt need any auxiliary lemmas *)
(* END AUXILIARY LEMMAS *)

lemma lem3 :
  equiv[L.f ~ L.f : ={L.y} ==> ={L.y}].
proof.
(* BEGIN FILL IN *)
proc.
wp.
rnd (fun u => L.x{1} ^^ L.x{2} ^^ u).
auto; progress.
smt(xorC xorA xorK xor_ff).
smt(dmybool1E).
smt(dmybool_fu).
smt(xorC xorA xorK xor_ff).
smt(xorC xorA xorK xor_ff).
(* END FILL IN *)
qed.
