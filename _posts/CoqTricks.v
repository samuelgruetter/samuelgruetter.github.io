(* begin hide *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* end hide *)

(**
For instance, if I want to simplify a multiplication out of a modulo, I can find the
right lemma using
*)

Search ((_ * ?x) mod ?x).

(** which will return exactly the right lemmas:

[[
Z_mod_mult: forall a b : Z, (a * b) mod b = 0
Z.mod_mul: forall a b : Z, b <> 0 -> (a * b) mod b = 0
]]

Two caveats:
I have to [Require] the modules containing these lemmas before, so in order to make the above
work, I had to [Require Import Coq.ZArith.ZArith.]
And I have to make sure the notations are interpreted in the right scope, either by
[Open Scope Z_scope.], or by specifying the scope delimiter like [((_ * ?x) mod ?x)%Z].

Moreover, [Search] also accepts multiple patterns.
For instance, to find all lemmas involving list equalities mentioning [skipn], I can do
*)

Search skipn (@eq (list _) _).

(** which will return

[[
firstn_skipn: forall (A : Type) (n : nat) (l : list A), firstn n l ++ skipn n l = l
]]

There's much more information for [Search] in the {{https://coq.inria.fr/refman/proof-engine/vernacular-commands.html#coq:cmd.search}reference manual}.

I'm collecting a list of more Coq tricks {{https://github.com/samuelgruetter/coq-tricks}here}, and later I learned that other people collect their tricks as well.
For instance, Tej Chajed's list is {{https://github.com/tchajed/coq-tricks}here}.
If you have a collection of Coq tricks as well, please let me know!
*)

(* TODO Santiago Cuellar? *)
