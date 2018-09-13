(** In the following, I will use OCaml extraction instead of JSON extraction,
    because the puzzlers are the same, but OCaml code is much more concise than
    JSON code.

    The original puzzler was the following:
*)

Require Extraction.
Definition foo(a b: bool): bool := orb a b.
Extraction Language OCaml.
Extraction foo.

(** It outputs

[[
let foo a b =
  match a with
  | True -> True
  | False -> b
]]

so [orb] got silently unfolded, even though we never told Coq to do so.

Let's try another extraction language:
*)

Extraction Language Haskell.
Extraction foo.

(** And suddenly we get what we want:

[[
foo :: Bool -> Bool -> Bool
foo =
  orb
]]

What if we define our own [orb]?
*)

Definition myorb(b1 b2 : bool) := if b1 then true else b2.
Definition foo'(a b: bool): bool := myorb a b.
Extraction Language OCaml.
Extraction foo'.

(** We also get what we want:

[[
let foo' =
  myorb
]]

What if we mark [foo] as opaque?
*)

Opaque foo.
Extraction foo.

(** No luck:

[[
let foo a b =
  match a with
  | True -> True
  | False -> b
]]

So we entered a clone of the Coq source code and played with some [grep] commands like

[[
grep -R . --include='*.ml' -e '[^a-zA-Z]orb[^A-Za-z]' -C3
]]

which eventually pointed us to the file [plugins/extraction/mlutil.ml], which contains
a list of hard-coded always-inlined constants:

[[
let manual_inline_set =
  List.fold_right (fun x -> Cset_env.add (con_of_string x))
    [ "Coq.Init.Wf.well_founded_induction_type";
      "Coq.Init.Wf.well_founded_induction";
      "Coq.Init.Wf.Acc_iter";
      "Coq.Init.Wf.Fix_F";
      "Coq.Init.Wf.Fix";
      "Coq.Init.Datatypes.andb";
      "Coq.Init.Datatypes.orb";
      "Coq.Init.Logic.eq_rec_r";
      "Coq.Init.Logic.eq_rect_r";
      "Coq.Init.Specif.proj1_sig";
    ]
    Cset_env.empty
]]

So that's why [orb] was inlined, but [myorb] was not!

And further down in that file, we see

[[
let inline r t =
  not (to_keep r) (* The user DOES want to keep it *)
  && not (is_inline_custom r)
  && (to_inline r (* The user DOES want to inline it *)
     || (lang () != Haskell && not (is_projection r) &&
         (is_recursor r || manual_inline r || inline_test r t)))
]]

so there's a special case for Haskell, which is why we got the desired result in Haskell,
but not in OCaml.

Now, _why_ are things so surprising and non-uniform? Is this a bug or a feature?
After some thinking, I concluded that it's a feature:

In OCaml, which has strict evaluation semantics, we want to enable short-circuiting of
boolean expressions. For instance, if the Coq source contains [orb somethingTrue expensiveCalculation],
the [expensiveCalculation] should not be evaluated in OCaml.
This can be achieved by always inlining [orb], so that the OCaml code is
[if somethingTrue then true else expensiveCalculation].

On the other hand, Haskell has lazy evaluation semantics, so we don't need to do anything
special in Haskell, but can just extract it to [orb somethingTrue expensiveCalculation],
and [expensiveCalculation] will be wrapped inside a thunk which is never evaluated.

So we now understand what's going on, but how do we get our example to behave the way it
should?

It turns out that reading the {{https://coq.inria.fr/refman/addendum/extraction.html}manual page for Extraction} helps: It tells us about the vernac command [Extraction NoInline qualid], so
we can do the following:
*)

Extraction NoInline orb.
Extraction foo.

(** and woohoo, we get what we want:

[[
let foo =
  orb
]]

Problem solved!
*)
