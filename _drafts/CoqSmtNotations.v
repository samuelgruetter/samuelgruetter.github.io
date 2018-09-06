(**
Suppose I am despairing on a Coq proof goal about integers,
*)

Goal 1 = 1. reflexivity. Qed.

(**
but [omega], [lia], [nia] etc don't work, and I don't even know if my goal is true at all.
Before
continuing my proof, I'd like a quick diagnosis, by a bleeding edge tool, on
whether the goal actually is true, but I don't feel like installing any
plugins or additional tools.
In this talk, I will demo a quick way to achieve this: I will go to
{{https://github.com/samuelgruetter/coq-smt-notations}}, copy-paste a few lines
of Ltac and Coq notations right into my proof buffer (no need to compile
anything or to reprocess anything in the IDE), and I get the negation of my
goal printed in smtlib format. I don't even need to install an SMT solver,
but I can just copy-paste this into the online Z3 solver available at
{{https://rise4fun.com/z3}}, and immediately get [unsat], which means I should
continue my proof, or a counterexample, which helps me figure out what's
wrong.
*)
