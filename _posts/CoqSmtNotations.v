(* begin hide *)

Require Import Coq.ZArith.BinInt.
Require Import Coq.omega.Omega.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Lemma test: forall
  (opcode rs1 rs2 funct3 simm12
  inst q q0 r1 r2
  r r0 q1 q2 q3 r3 q4 r4 q5 r5 q6 r6 q7 r7 q8 r8 q9 r9 q10 r10 q11 r11 q12
  r12 q13 r13 q14 r14 q15 r15 q16 r16: Z),
    0 <= opcode < 128 /\ 0 <= rs1 < 32 /\ 0 <= rs2 < 32 /\
    0 <= funct3 < 8 /\ - (2048) <= simm12 < 2048
  -> opcode + r1 * 128 + funct3 * 4096 + rs1 * 32768 + rs2 * 1048576 + r2 * 33554432 = inst
  -> 0 <= r16 < 2
  -> q9 = 2 * q16 + r16
  -> 0 <= r15 < 32
  -> q6 = 32 * q15 + r15
  -> 0 <= r14 < 32
  -> q5 = 32 * q14 + r14
  -> 0 <= r13 < 8
  -> q4 = 8 * q13 + r13
  -> 0 <= r12 < 128
  -> q3 = 128 * q12 + r12
  -> 0 <= r11 < 32
  -> q8 = 32 * q11 + r11
  -> 0 <= r10 < 128
  -> q7 = 128 * q10 + r10
  -> 0 <= r9 < 2048
  -> r10 * 32 + r11 = 2048 * q9 + r9
  -> 0 <= r8 < 128
  -> inst = 128 * q8 + r8
  -> 0 <= r7 < 33554432
  -> inst = 33554432 * q7 + r7
  -> 0 <= r6 < 1048576
  -> inst = 1048576 * q6 + r6
  -> 0 <= r5 < 32768
  -> inst = 32768 * q5 + r5
  -> 0 <= r4 < 4096
  -> inst = 4096 * q4 + r4
  -> 0 <= r3 < 1
  -> inst = 1 * q3 + r3
  -> 0 <= r2 < 128
  -> q0 = 128 * q2 + r2
  -> 0 <= r1 < 32
  -> q = 32 * q1 + r1
  -> 0 <= r0 < 32
  -> simm12 = 32 * q0 + r0
  -> 0 <= r < 1
  -> simm12 = 1 * q + r
  -> opcode = r12 /\ funct3 = r13 /\ rs1 = r14
     /\ rs2 = r15 /\ simm12 = r10 * 32 + r11 - r16 * 4096.
Proof.
  intros.

(* end hide *)

(**
Suppose I am despairing on a Coq proof goal about integers, and I have no idea if it
is true or not.
For instance, while trying to prove that encoding and then decoding a RISCV instruction
is the identity function, I ended up with the following proof goal:

[[
  opcode, rs1, rs2, funct3, simm12, inst, q, q0, r1, r2,
  r, r0, q1, q2, q3, r3, q4, r4, q5, r5, q6, r6, q7, r7,
  q8, r8, q9, r9, q10, r10, q11, r11, q12, r12, q13, r13,
  q14, r14, q15, r15, q16, r16 : Z
  H : 0 <= opcode < 128 /\ 0 <= rs1 < 32 /\ 0 <= rs2 < 32 /\
      0 <= funct3 < 8 /\ - (2048) <= simm12 < 2048
  H0 : opcode + r1 * 128 + funct3 * 4096 + rs1 * 32768 +
         rs2 * 1048576 + r2 * 33554432 = inst
  H1 : 0 <= r16 < 2
  H2 : q9 = 2 * q16 + r16
  H3 : 0 <= r15 < 32
  H4 : q6 = 32 * q15 + r15
  H5 : 0 <= r14 < 32
  H6 : q5 = 32 * q14 + r14
  H7 : 0 <= r13 < 8
  H8 : q4 = 8 * q13 + r13
  H9 : 0 <= r12 < 128
  H10 : q3 = 128 * q12 + r12
  H11 : 0 <= r11 < 32
  H12 : q8 = 32 * q11 + r11
  H13 : 0 <= r10 < 128
  H14 : q7 = 128 * q10 + r10
  H15 : 0 <= r9 < 2048
  H16 : r10 * 32 + r11 = 2048 * q9 + r9
  H17 : 0 <= r8 < 128
  H18 : inst = 128 * q8 + r8
  H19 : 0 <= r7 < 33554432
  H20 : inst = 33554432 * q7 + r7
  H21 : 0 <= r6 < 1048576
  H22 : inst = 1048576 * q6 + r6
  H23 : 0 <= r5 < 32768
  H24 : inst = 32768 * q5 + r5
  H25 : 0 <= r4 < 4096
  H26 : inst = 4096 * q4 + r4
  H27 : 0 <= r3 < 1
  H28 : inst = 1 * q3 + r3
  H29 : 0 <= r2 < 128
  H30 : q0 = 128 * q2 + r2
  H31 : 0 <= r1 < 32
  H32 : q = 32 * q1 + r1
  H33 : 0 <= r0 < 32
  H34 : simm12 = 32 * q0 + r0
  H35 : 0 <= r < 1
  H36 : simm12 = 1 * q + r
  ─────────────────────────────────────────────────────────
  opcode = r12 /\ funct3 = r13 /\ rs1 = r14 /\ rs2 = r15 /\
  simm12 = r10 * 32 + r11 - r16 * 4096
]]

It looks like linear arithmetic, so let's try [omega], but it fails with
[Omega can't solve this system].
*)

  Fail omega.

(**
And [lia] and [nia] don't work either:
*)

  Fail Timeout 10 lia.
  Fail Timeout 10 nia.

(**
So before continuing my proof, I'd like a quick diagnosis, by a bleeding edge tool, on
whether the goal actually is true.
But I'm lazy I don't feel like installing any plugins or additional tools.
So here's a quick and simple way to get such a diagnosis:

I open a browser and google for Samuel Gruetter's {{https://github.com/samuelgruetter/}github account}, click on the repo called {{https://github.com/samuelgruetter/coq-smt-notations}coq-smt-notations}, and then on the file {{https://github.com/samuelgruetter/coq-smt-notations/blob/master/smt_demo.v}smt_demo.v}.

There, I scroll down to the [BEGIN code to copy paste] marker, copy the code until
the [END code to copy paste] marker, and paste it right into my proof buffer.
No need to compile anything or to reprocess anything in the IDE!

The purpose of this code is to turn my proof goal into a query for an SMT solver.
It does so by reformulating the goal as the question "Is the negation of this goal satisfiable?",
which is equivalent to asking "Is there a counterexample?".

So the first part of the copy-pasted code negates the goal of the form [forall …, …] into
[~ forall …, …], and then rewrites it into [exists …, ~ …].
*)

Require Import Coq.Logic.Classical_Prop.

Definition marker(P: Prop): Prop := P.
Definition marker2(P: Prop): Prop := P.

Lemma EE: forall AA (P: AA -> Prop),
    (exists a: AA, ~ P a) <-> ~ forall (a: AA), P a.
Proof.
  intros. split.
  - intros. destruct H as [a H]. intro. apply H. auto.
  - intro.
    destruct (classic (exists a : AA, ~ P a))
      as [C | C]; [assumption|].
    exfalso. apply H. intro.
    destruct (classic (P a))
      as [D | D]; [assumption |].
    exfalso. apply C. exists a. assumption.
Qed.

Lemma K: forall (P Q: Prop),
    (~ marker (P -> Q)) <-> marker (~ (P -> Q)).
Proof.
  cbv [marker]. intros. reflexivity.
Qed.

Definition Func(A B: Type) := A -> B.

(* intro as much as we can *)
repeat intro.

(* clear everything except used vars and Props *)
repeat match goal with
       | H: ?T |- _ =>
         match type of T with
         | Prop => fail 1
         | _ => clear H
         end
       end.

(* revert all Props *)
repeat match goal with
       | H: ?T |- _ =>
         match type of T with
         | Prop => revert H
         end
       end.

(* protect functions from being treated as implications *)
repeat match goal with
       | x: ?T1 -> ?T2 |- _ => change (Func T1 T2) in x
       end.

(* mark where hyps begin *)
match goal with
| |- ?G => change (marker G)
end.

(* revert vars *)
repeat match goal with
       | x: ?T |- _ =>
         match T with
         | Type => fail 1
         | _ => idtac
         end;
           revert x
       end.

(* negate goal *)
match goal with
| |- ?P => assert (~P); [|admit]
end.

(* "not forall" to "exists such that not" *)
repeat match goal with
 | |- context[~ (forall (x: ?T), _)] =>
   (assert (forall (P: T -> Prop),
               (exists x: T, ~ P x) <-> ~ (forall x: T, P x))
    as EEE by apply EE);
   setoid_rewrite <- EEE;
   clear EEE
end.

(* push "not" into marker *)
setoid_rewrite K.

(* marker for check_sat *)
match goal with
| |- ?P => change (marker2 P)
end.

Set Printing Depth 10000.

(**
After processing this code, the proof goal looks as follows:

[[
  ───────────────────────────────────────────────────────
  marker2
    (exists
       opcode rs1 rs2 funct3 simm12 inst q q0 r1 r2 r r0
       q1 q2 q3 r3 q4 r4 q5 r5 q6 r6 q7 r7 q8 r8 q9 r9 q10
       r10 q11 r11 q12 r12 q13 r13 q14 r14 q15 r15 q16 r16 : Z,
       marker
         (~
          (0 <= opcode < 128 /\ 0 <= rs1 < 32 /\ 0 <= rs2 < 32 /\
              0 <= funct3 < 8 /\ - (2048) <= simm12 < 2048 ->
           opcode + r1 * 128 + funct3 * 4096 + rs1 * 32768 +
              rs2 * 1048576 + r2 * 33554432 = inst ->
           0 <= r16 < 2 ->
           q9 = 2 * q16 + r16 ->
           0 <= r15 < 32 ->
           q6 = 32 * q15 + r15 ->
           0 <= r14 < 32 ->
           q5 = 32 * q14 + r14 ->
           0 <= r13 < 8 ->
           q4 = 8 * q13 + r13 ->
           0 <= r12 < 128 ->
           q3 = 128 * q12 + r12 ->
           0 <= r11 < 32 ->
           q8 = 32 * q11 + r11 ->
           0 <= r10 < 128 ->
           q7 = 128 * q10 + r10 ->
           0 <= r9 < 2048 ->
           r10 * 32 + r11 = 2048 * q9 + r9 ->
           0 <= r8 < 128 ->
           inst = 128 * q8 + r8 ->
           0 <= r7 < 33554432 ->
           inst = 33554432 * q7 + r7 ->
           0 <= r6 < 1048576 ->
           inst = 1048576 * q6 + r6 ->
           0 <= r5 < 32768 ->
           inst = 32768 * q5 + r5 ->
           0 <= r4 < 4096 ->
           inst = 4096 * q4 + r4 ->
           0 <= r3 < 1 ->
           inst = 1 * q3 + r3 ->
           0 <= r2 < 128 ->
           q0 = 128 * q2 + r2 ->
           0 <= r1 < 32 ->
           q = 32 * q1 + r1 ->
           0 <= r0 < 32 ->
           simm12 = 32 * q0 + r0 ->
           0 <= r < 1 ->
           simm12 = 1 * q + r ->
           opcode = r12 /\ funct3 = r13 /\ rs1 = r14 /\
           rs2 = r15 /\ simm12 = r10 * 32 + r11 - r16 * 4096)))
]]

After that, the second part of the copy-pasted code introduces a few notations which
pretty-print the goal in smtlib2 format, which is the standard input format for SMT solvers.
*)

Notation "'and' A B" := (Logic.and A B)
  (at level 10, A at level 0, B at level 0).
Notation "'or' A B" := (Logic.or A B)
  (at level 10, A at level 0, B at level 0).
Notation "+ A B" := (Z.add A B)
  (at level 10, A at level 0, B at level 0).
Notation "< A B" := (Z.lt A B)
  (at level 10, A at level 0, B at level 0).
Notation "<= A B" := (Z.le A B)
  (at level 10, A at level 0, B at level 0).
Notation "- A B" := (Z.sub A B)
  (at level 10, A at level 0, B at level 0).
Notation "* A B" := (Z.mul A B)
  (at level 10, A at level 0, B at level 0, format " *  A  B").
Notation "^ A B" := (Z.pow A B)
  (at level 10, A at level 0, B at level 0).
Notation "= A B" := (@eq Z A B)
  (at level 10, A at level 0, B at level 0).
Notation "'not' A" := (not A)
  (at level 10, A at level 0).
Notation "'(declare-const' a 'Int)' body" :=
  (ex (fun (a: Z) => body))
    (at level 10, body at level 10,
     format "(declare-const  a  Int) '//' body").
Notation "'(assert' P ')'" := (marker P)
  (at level 10, P at level 0, format "(assert  P )").
Notation "- 0 a" := (Z.opp a)
  (at level 10, a at level 10).
Notation "'implies' A B" := (A -> B)
  (at level 10, A at level 0, B at level 0).
Notation "x '(check-sat)'" := (marker2 x)
  (at level 200, format "x '//' '(check-sat)'").

(* refresh *)
idtac.

(**
After processing that code (and going back up one step if the IDE doesn't refresh the proof
goal), the goal is printed as follows:

[[
  (declare-const opcode Int)
  (declare-const rs1 Int)
  (declare-const rs2 Int)
  (declare-const funct3 Int)
  (declare-const simm12 Int)
  (declare-const inst Int)
  (declare-const q Int)
  (declare-const q0 Int)
  (declare-const r1 Int)
  (declare-const r2 Int)
  (declare-const r Int)
  (declare-const r0 Int)
  (declare-const q1 Int)
  (declare-const q2 Int)
  (declare-const q3 Int)
  (declare-const r3 Int)
  (declare-const q4 Int)
  (declare-const r4 Int)
  (declare-const q5 Int)
  (declare-const r5 Int)
  (declare-const q6 Int)
  (declare-const r6 Int)
  (declare-const q7 Int)
  (declare-const r7 Int)
  (declare-const q8 Int)
  (declare-const r8 Int)
  (declare-const q9 Int)
  (declare-const r9 Int)
  (declare-const q10 Int)
  (declare-const r10 Int)
  (declare-const q11 Int)
  (declare-const r11 Int)
  (declare-const q12 Int)
  (declare-const r12 Int)
  (declare-const q13 Int)
  (declare-const r13 Int)
  (declare-const q14 Int)
  (declare-const r14 Int)
  (declare-const q15 Int)
  (declare-const r15 Int)
  (declare-const q16 Int)
  (declare-const r16 Int)
  (assert (not (implies
                (and (and (<= 0 opcode) (< opcode 128))
                 (and (and (<= 0 rs1) (< rs1 32))
                  (and (and (<= 0 rs2) (< rs2 32))
                   (and (and (<= 0 funct3) (< funct3 8))
                    (and (<= (- 0 2048) simm12) (< simm12 2048))))))
                (implies (= (+ (+ (+ (+ (+ opcode ( * r1 128))
                           ( * funct3 4096)) ( * rs1 32768))
                            ( * rs2 1048576)) ( * r2 33554432)) inst)
                 (implies (and (<= 0 r16) (< r16 2))
                 (implies (= q9 (+ ( * 2 q16) r16))
                 (implies (and (<= 0 r15) (< r15 32))
                 (implies (= q6 (+ ( * 32 q15) r15))
                 (implies (and (<= 0 r14) (< r14 32))
                 (implies (= q5 (+ ( * 32 q14) r14))
                 (implies (and (<= 0 r13) (< r13 8))
                 (implies (= q4 (+ ( * 8 q13) r13))
                 (implies (and (<= 0 r12) (< r12 128))
                 (implies (= q3 (+ ( * 128 q12) r12))
                 (implies (and (<= 0 r11) (< r11 32))
                 (implies (= q8 (+ ( * 32 q11) r11))
                 (implies (and (<= 0 r10) (< r10 128))
                 (implies (= q7 (+ ( * 128 q10) r10))
                 (implies (and (<= 0 r9) (< r9 2048))
                 (implies (= (+ ( * r10 32) r11) (+ ( * 2048 q9) r9))
                 (implies (and (<= 0 r8) (< r8 128))
                 (implies (= inst (+ ( * 128 q8) r8))
                 (implies (and (<= 0 r7) (< r7 33554432))
                 (implies (= inst (+ ( * 33554432 q7) r7))
                 (implies (and (<= 0 r6) (< r6 1048576))
                 (implies (= inst (+ ( * 1048576 q6) r6))
                 (implies (and (<= 0 r5) (< r5 32768))
                 (implies (= inst (+ ( * 32768 q5) r5))
                 (implies (and (<= 0 r4) (< r4 4096))
                 (implies (= inst (+ ( * 4096 q4) r4))
                 (implies (and (<= 0 r3) (< r3 1))
                 (implies (= inst (+ ( * 1 q3) r3))
                 (implies (and (<= 0 r2) (< r2 128))
                 (implies (= q0 (+ ( * 128 q2) r2))
                 (implies (and (<= 0 r1) (< r1 32))
                 (implies (= q (+ ( * 32 q1) r1))
                 (implies (and (<= 0 r0) (< r0 32))
                 (implies (= simm12 (+ ( * 32 q0) r0))
                 (implies (and (<= 0 r) (< r 1))
                 (implies (= simm12 (+ ( * 1 q) r))
                          (and (= opcode r12)
                          (and (= funct3 r13)
                          (and (= rs1 r14)
                          (and (= rs2 r15)
                          (= simm12
                          (- (+ ( * r10 32) r11) ( * r16 4096))))))))
  )))))))))))))))))))))))))))))))))))))))
  (check-sat)
]]

Now I want to feed this into an SMT solver, but I'm too lazy to install one, so I just google
for "Z3 online" and click on the top result, which takes me to {{https://rise4fun.com/z3}}.

I can copy-paste the above smtlib code into the text field on this web interface, click on
the ▶ button, and after a few seconds, it answers [unsat], which means that there's
no counterexample, so the goal holds, and I know that it makes sense to try to prove it.

On the other hand, if the goal was not true, Z3 will answer [sat].
For instance, replacing [8] by [9] in the line

[[
(implies (and (<= 0 r13) (< r13 8))
]]

can illustrate this, and if [(get-model)] is appended at the end of the input, it will print the following counterexample:

[[
(model
  (define-fun r1 () Int
    31)
  (define-fun q13 () Int
    833)
  (define-fun r12 () Int
    74)
  (define-fun q15 () Int
    0)
  (define-fun rs1 () Int
    2)
  (define-fun q11 () Int
    6672)
  (define-fun opcode () Int
    74)
  (define-fun q10 () Int
    0)
  (define-fun r10 () Int
    0)
  (define-fun r0 () Int
    31)
  (define-fun q14 () Int
    26)
  (define-fun q1 () Int
    0)
  (define-fun r2 () Int
    0)
  (define-fun rs2 () Int
    26)
  (define-fun r16 () Int
    0)
  (define-fun r14 () Int
    2)
  (define-fun q2 () Int
    0)
  (define-fun q16 () Int
    0)
  (define-fun r9 () Int
    31)
  (define-fun funct3 () Int
    0)
  (define-fun q12 () Int
    213535)
  (define-fun r15 () Int
    26)
  (define-fun r13 () Int
    8)
  (define-fun r () Int
    0)
  (define-fun simm12 () Int
    31)
  (define-fun q () Int
    31)
  (define-fun q0 () Int
    0)
  (define-fun r3 () Int
    0)
  (define-fun r4 () Int
    4042)
  (define-fun r5 () Int
    4042)
  (define-fun r6 () Int
    69578)
  (define-fun r7 () Int
    27332554)
  (define-fun r8 () Int
    74)
  (define-fun q7 () Int
    0)
  (define-fun q8 () Int
    213535)
  (define-fun r11 () Int
    31)
  (define-fun q3 () Int
    27332554)
  (define-fun q4 () Int
    6672)
  (define-fun q5 () Int
    834)
  (define-fun q6 () Int
    26)
  (define-fun q9 () Int
    0)
  (define-fun inst () Int
    27332554)
)
]]

Knowing a counterexample can be helpful in figuring out how to strenghten the hypotheses of
a lemma to make it true.
For instance, in the above counterexample, [r13] is assigned the value [8], so the above
relaxation was indeed exploited by Z3 in order to find the counterexample.

So that's it: A quick and simple way to diagnose if a Coq goal about integers is true,
which requires no installation of additional tools, and not even requires to reprocess
the current proof buffer.
All you need to do to use it is to copy-paste some code from {{https://github.com/samuelgruetter/coq-smt-notations/blob/master/smt_demo.v}this file}.
*)

(* begin hide *)
Abort.
(* end hide *)
