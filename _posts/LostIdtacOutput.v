(* begin hide *)
Require Import Coq.Lists.List. Import ListNotations.

Goal forall (U: Type) (a b c z: U) (P Q R: U -> Prop),
    (forall (y: U), y = a \/ y = b \/ y = c) ->
    (forall y: U, P y -> Q y) ->
    R z.
Proof.
intros.
(* end hide *)

(** Let's illustrate this with an example: Suppose we're in a goal like

[[
  U : Type
  a, b, c, z : U
  P, Q, R : U -> Prop
  H : forall y : U, y = a \/ y = b \/ y = c
  H0 : forall y : U, P y -> Q y
  ─────────────────────────────────────────────────────────
  R z
]]

where we have a hypothesis like [H] whose disjunction tells us what values
variables of type [U] can take, and suppose we want to write a tactic which
collects a list of all possible values for variables of type [U],
i.e. it should return the list [[a; b; c]].

We could write it as follows:
*)

Ltac disjunction_to_list d :=
  lazymatch d with
    | (_ = ?v \/ ?rest) =>
      let s := disjunction_to_list rest in
      constr:(v :: s)
    | (_ = ?v) => constr:(v :: nil)
    | _ => fail "did not expect" d
  end.

(** And if we test it with

[[
let d := type of (H z) in let r := disjunction_to_list d in idtac r.
]]

we get back [[a; b; c]], as expected. On the other hand, if we use it on a
hypothesis which is not a disjunction,

[[
let d := type of (H0 z) in let r := disjunction_to_list d in idtac r.
]]

we get back our custom error message, as expected:

[[
Error: Ltac call to "disjunction_to_list" failed.
       Tactic failure: did not expect (P z -> Q z).
]]

Now, let's not hard code [H], but find it with a [match goal]:

[[
match goal with
| H: forall (x: U), ?d |- _ =>
    let r := disjunction_to_list d in idtac r
end.
]]

But this results in an unhelpful error message:

[[
Error: No matching clauses for match.
]]

So let's add some debug output with [idtac] to check which hypotheses are being tested:

[[
match goal with
| H: forall (x: U), ?d |- _ =>
    idtac "Trying" H;
    let r := disjunction_to_list d in idtac r
end.
]]

But unfortunately, we don't get any debug output, the only thing displayed in
ProofGeneral's response window is

[[
Error: No matching clauses for match.
]]

Now here's the trick: ProofGeneral also has a buffer named [*coq*], and if we
open it, we find the raw output of the coqtop process, which contains all the
debug output:

[[
<infomsg>Trying H0</infomsg>
<infomsg>Trying H</infomsg>
<infomsg>Trying R</infomsg>
<infomsg>Trying Q</infomsg>
<infomsg>Trying P</infomsg>
]]

An alternative way to get all output is, surprisingly, to use the [Fail] command:

[[
Fail match goal with
| H: forall (x: U), ?d |- _ =>
    idtac "Trying" H;
    let r := disjunction_to_list d in idtac r
end.
]]

It prints all we want into the response buffer:

[[
Trying H0
Trying H
Trying R
Trying Q
Trying P
The command has indeed failed with message:
         No matching clauses for match.
]]

So we now know how to debug our tactic, but we still need to find why the above failed.
It turns out that the [d] we were passing to [disjunction_to_list] contains an
unbound variable [x], so matching on it is not allowed and fails.
We can fix it as follows:

[[
match goal with
| A: forall (x: U), ?d |- _ =>
  idtac "Trying" d;
  let A' := type of (A z) in
  let r := disjunction_to_list A' in idtac r
end.
]]

Whose output is as expected:

[[
Trying (P x -> Q x)
Trying (x = a \/ x = b \/ x = c)
[a; b; c]
]]

So, long story short:
In order to find lost debug output, it might help to look at the [*coq*] buffer or to
precede a failing command with [Fail].

You can find the Coq source of this blog post {{https://github.com/samuelgruetter/samuelgruetter.github.io/blob/master/_posts/LostIdtacOutput.v}here}.
*)

(* begin hide *)
Abort.
(* end hide *)
