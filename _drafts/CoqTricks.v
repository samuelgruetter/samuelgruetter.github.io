(** Between 2014 and 2016, I was using Coq regularly, but did not know that its
    [Search] command accepts patterns.
    If only I had learnt this earlier, this would have saved me so much time!

*)

(**#<!--more-->#*)

(* begin hide *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* end hide *)

Search ((_ * ?x) mod ?x).

Search skipn (@eq (list _) _).

(** There's much more to discover, and I encourage everyone to have a look at the
    [reference manual for "Search"](https://coq.inria.fr/refman/proof-engine/vernacular-commands.html#coq:cmd.search). *)

(**
[here](https://github.com/samuelgruetter/coq-tricks)

Santiago Cuellar

Tej Chajed has [a whole collection](https://github.com/tchajed/coq-tricks) too
 *)
