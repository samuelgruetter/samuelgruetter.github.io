---
layout:        post
title:         Omnisemantics in a nutshell
description:   "An alternative style of programming language semantics that works much better in the presence of undefined behavior and nondeterminism than using traditional smallstep or bigstep operational semantics"
twitter_card:
   type:       summary_large_image
   image:      /assets/omnisemantics/omnisemantics_sim.png
---

With my collaborators [Arthur Charguéraud](https://www.chargueraud.org/), [Adam Chlipala](http://adam.chlipala.net/) and [Andres Erbsen](https://andres.systems/), we came up with a new style of programming language semantics that we find works much better in the presence of undefined behavior and nondeterminism than traditional bigstep and smallstep operational semantics do.
We called it *omnisemantics* because *one* derivation talks about *all* (omni) possible nondeterministic executions at once.

Yesterday, I gave a talk about it at the [NEPLS workshop](https://www.nepls.org/Events/33/), and because I enjoyed giving that talk so much, I decided to take some screenshots of my slides and turn the talk into a blog post.

If you saw the talk, or have already heard about omnisemantics and you want to learn (almost) everything we have to say about it, I'd recommend reading the preprint of our paper that you can find [here](https://hal.archives-ouvertes.fr/hal-03255472). On the other hand, if you prefer just a quick intro, at the level of detail of a workshop talk, this blog post might be for you!

<!--more-->

This post is about how to *define* and *use* programming language semantics in the presence of *undefined behavior* and *nondeterminism*.

![](/assets/omnisemantics/0100_ub_and_nondet.svg)

In a state transition diagram, undefined behavior just means a non-final state without any outgoing transitions, and nondeterminism means that there's a state with several possible next states.

Once we combine undefined behavior and nondeterminism, we run into a few problems.

## Problem 1

The first problem is how to concisely formalize the following statement:

![](/assets/omnisemantics/0200_statement.svg)

In a deterministic language, this is easy: We just need to give a final state s' and prove either of these:

![](/assets/omnisemantics/0300_deterministic_traditional.svg)

However, in a nondeterministic language, merely exhibiting one path through the state transition diagram leading to a state satisfying P is not enough, because there could be other nondeterministic branches that get stuck:

![](/assets/omnisemantics/0400_oops.svg)

(Side remark: In this post, I use an imperative language to explain our new style of semantics, but omnisemantics are also applicable to more high-level functional languages, so if you don't like state, it's still worth to keep reading)

Using traditional bigstep or smallstep semantics, there are several ways to fix this problem, but all of them are quite cumbersome:

One of them is to define a separate safety judgment, which requires us to duplicate the number of rules. Shown here is the rule for sequencing two commands:

![](/assets/omnisemantics/0500_separate_safety_judgment.svg)

Another solution would be to use error markers and to add error propagation rules like the following ones, but this one requires even more additional rules (several added rules per original rule).

![](/assets/omnisemantics/0600_error_markers.svg)

Or if you're working with smallstep rules, you could use the following long formula:

![](/assets/omnisemantics/0700_smallstep_long_formula.svg)

It says that for all s' reachable from s, either s' already satisfies P, in which case we prove the second multistep using 0 steps, or else, there exists a path from s' to an s'' that satisfies P.

However, all of these fixes are quite verbose, and do not consist of one single inductively defined judgment over which you could easily do induction, so we would like to find a nicer, more concise jugment.

## Problem 2

Another problem is that compiler correctness proof writers prefer *forward simulations* over *backward simulations*.

![](/assets/omnisemantics/0800_det_fw_bw_sim.svg)

In a forward simulation, you prove that given an execution of the source language program, there exists a corresponding execution of the target language program, whereas in a backward simulation, you prove that for each target language execution, there exists a source language execution justifying the behavior of the target language program. (Note that to simplify the presentation in this post, I assume that the source and target languages use the same state representation. In the actual work, they use different formats, and we use a relation R(s<sub>source</sub>, s<sub>target</sub>) to translate between the two. See [paper](https://hal.archives-ouvertes.fr/hal-03255472) for details).

Forward simulations are easy to prove:
* We do induction on the source language execution
* This results in a case distinction over the source language construct, which allows us to simplify compile(c) to obtain the target program
* We symbolically execute the target program and show that it behaves like the source program

On the other hand, backward simulations are usually much harder to prove, because given a snippet of the target program, you'd need to consider all possible source program snippets that could have been compiled to that target program snippet, so you'd basically have to invert the compilation function.

Unfortunately, in the presence of nondeterminism, the forward simulations that we like so much do not work any more: If we just prove that one target language execution exists, this does not exclude that there are other executions that might get stuck, so the statement of the forward simulation becomes meaningless. And in the special case where the target language happens to be deterministic, but the source language is nondeterministic, we simply can't prove a forward simulation, because the target language does not have enough choice to simulate all the possible executions of the source language.

![](/assets/omnisemantics/1000_nondet_fw_bw_sim.svg)

So, the question is: Can we fix forward simulations so that they are still meaningful in the presence of nondeterminism? As we will see, the answer is yes!

## CompCert's Trick

But before presenting our solution, let's briefly discuss how CompCert avoids this problem (but creates new problems while doing so): Instead of dealing with the nondeterminism, CompCert just made the target language and all intermediate languages deterministic!

In the case of memory allocation, this looks as follows:

![](/assets/omnisemantics/1100_compcert_determinization.svg)

In C, the pointer p obtained from allocating n bytes of memory can be any pointer, so expressed as a state transition diagram, you could get one possible next state for each possible pointer value. CompCert, however, decided that pointers are tuples of a blockID and an offset, and that the returned blockID is always deterministically the previous blockID plus 1, so expressed as a state transition diagram, there's only one possible next state.
If you're ok with this more high-level model of the memory, that's a fine thing to do, but it does lead to further problems if there are compiler phases that *introduce or remove allocation*.
For example, in a spilling phase that saves variables which don't fit into registers on the stack, the target program will introduce new memory allocations for the spilled variables, so compared to the source program, all blockIDs will get shifted!

![](/assets/omnisemantics/1200_memory_shift.svg)

So the addresses of the target memory will be shifted compared to the addresses of the source memory, and since the values in the memory can also contain addresses, these need to be shifted as well, which requires defining a complex relation between the source memory and the target memory, the famous *memory injection*.

## Our Solution: Omnisemantics

So, to solve the two above problems, we came up with a judgment that relates a command and a starting state to a *set of outcomes* (aka postcondition) rather than to one individual outcome.

![](/assets/omnisemantics/1300_omnibigstep_meaning.svg)

Here are a few sample rules:
The rule for assignment of a variable y to variable x requires that the postcondition P holds for the updated state:

![](/assets/omnisemantics/1400_assign_rule.svg)

The rule for sequence requires us to pick a middle postcondition Q, and to show that for all s' in that Q, running c2 will lead to a state satisfying P:

![](/assets/omnisemantics/1500_seq_rule.svg)

And finally, here's a rule involving nondeterminism, for a pseudo random number generator function returning a number between 0 and n:

![](/assets/omnisemantics/1600_rand_rule.svg)

Note how the omni-bigstep rule needs to prove P for *all* possible nondeterministic choices of v, whereas the traditional bigstep rule only needs to consider *one* possible value of v.

If we imagine the forall in the premise of this rule as creating one premise for each possible value of v, we can think of the proof tree as having a shape like this:

![](/assets/omnisemantics/1700_forall_expanded.svg)

In this representation, we really see how *one derivation* contains *all possible executions*.
For writing proofs, this is crucial, because now, if we do induction over a derivation, we can *cover all possible executions in one induction*.

## Relationship to Traditional Semantics

Omni-bigstep semantics are equivalent to traditional bigstep semantics in the following sense:

![](/assets/omnisemantics/1800_omnibigstep_to_traditional.svg)

So if you (or your audience) doesn't quite trust this new style of semantics yet, you can state your toplevel theorem in terms of traditional semantics, and just use omnisemantics as a proof device.

Omni-bigstep semantics are also equivalent to weakest-precondition semantics:

![](/assets/omnisemantics/1900_wp_equiv.svg)

So their meaning is exactly the same, and even their definitions look quite similar, but there are a few key differences:

![](/assets/omnisemantics/2000_wp_vs_omnibigstep_table.svg)

Note that in the above table, "do not need invariants" does not mean that we've solved the problem of finding loop invariants for you: If you have a concrete program that you want to prove correct, you still need to come up with loop invariants for its loops.
But once you *have* an omnisemantics derivation, it does not contain any invariants any more, so if you're transforming it into other omnisemantics derivations (such as eg in a compiler correctness proof), you only need to deal with one outermost inductive hypothesis, and won't encounter any nested inductions and invariants for the loops.

## Back to the Problems

So now, let's see how omnisemantics solve Problem 1 and 2 introduced above.

Problem 1 is solved trivially, because we simply defined our judgment to mean exactly what we want it to mean:

![](/assets/omnisemantics/1300_omnibigstep_meaning.svg)

And for problem 2, let's compare the traditional forward simulation (which we saw doesn't work with nondeterminism) to the omnisemantics forward simulation:

![](/assets/omnisemantics/2100_omni_fwd_sim.svg)

The traditional forward simulation only gives us one possible target language execution, whereas the target omnisemantics derivation talks about all possible target executions, so we can't miss any stuck nondeterministic branches in the way the traditional forward simulation could.

In fact, with omnisemantics forward simulations, compiler phases can easily *introduce* nondeterminism, *eliminate* (resolve) nondeterminism, and *preserve* nondeterminism:
* In a phase that introduces nondeterminism, the rule for the relevant *target*-language construct has a forall-quantified premise, so the compiler correctness proof needs to show that for *all* nondeterministic choices, the rest of target program behaves correctly.
* In a phase that eliminates (resolves) nondeterminism, the rule for the relevant *source*-language construct has a forall-quantified premise, so the compiler correctness proof can *pick one* choice to instantiate this forall.
* And in a phase that preserves the nondeterminism, *both source and target* language have a forall-quantified premise, so the compiler correctness proof can *instantiate* the source forall with the value that it introduced from the target forall.

## Omni-Smallstep Semantics

We can also define a small-step version of omnisemantics:

![](/assets/omnisemantics/2400_omni_smallstep.svg)

In traditional smallstep semantics, the judgment for one step is lifted to multiple steps using the transitive closure operator (star), whereas in omni-smallstep semantics, the lifting is done using the *eventually operator* (diamond):

![](/assets/omnisemantics/2500_eventually_operator.svg)

## Type Safety Proofs

Another area where omnisemantics are useful is in type safety proofs.
Traditionally, one proves the well-known progress and preservation theorems:

![](/assets/omnisemantics/2600_progress_and_preservation.svg)

However, this requires us to do two proofs (one for progress, one for preservation) by induction on the typing derivation, so in a mechanized proof, we have to do all the induction-related bookkeeping twice.
And moreover, in proof assistants based on proof terms, the proof of preservation creates a proof term whose size is quadratic in the number of language constructs: For each case of the typing derivation, you have to invert the execution step, just to conclude that only one or two execution steps are possible. Proof assistants like Coq have an inversion tactic that can solve all these contradictory cases automatically, but the generated proof term still inspects each of these cases individually, resulting in a proof term of quadratic size, which can become a problem in large languages.

For these two reasons, when using deterministic languages, people sometimes prefer to prove the following equivalent statement instead of progress and preservation:

![](/assets/omnisemantics/2700_combined_safety.svg)

However, in the same way as in Problem 1 and 2 above, as soon as you add nondeterminism, the statement becomes meaningless, because it doesn't cover all possible nondeterministic executions.

But luckily, using omnisemantics (and set comprehension notation for postconditions viewed as sets of outcomes), we can state type soundness as follows:

![](/assets/omnisemantics/2800_omni_typesafety.svg)

This statement can be proven by induction on the typing derivation, and we show a few representative cases of such a typesafety proof for a stateful functional language in the paper.

## Conclusion

*One* omnisemantics derivation talks about *all* possible executions, therefore solving several problems arising from the combination of undefined behavior and nondeterminism:
* How to express that program c, when run in state s, safely terminates, and all final states satisfy&nbsp;P
* How to enable compiler proofs to use forward simulations
* How to prove progress and preservation in one combined linear-proof-size type soundness proof
* How to easily derive termination-sensitive program logic rules from operational semantics (not explained in this post, see paper)

This blog post was meant to just give a brief overview of omnisemantics, and I encourage you to read our [preprint](https://hal.archives-ouvertes.fr/hal-03255472), which contains a much more detailed treatment of the topic.
