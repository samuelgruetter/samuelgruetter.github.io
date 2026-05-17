---
layout: default
title: Samuel Gruetter
---

<style>
  .rightbox {
    display: inline-block;
    width: 55%;
    padding-bottom: .7em;
  }
</style>

<div style="width: 40%">
  <img style="float: left; padding-right: 10px; padding-bottom: 10px" src="{{ "/assets/2026-05_samuel_gruetter.jpg" | absolute_url }}">
</div>

<div class="rightbox">
  <b>Email:</b> firstname dot lastname at inf dot ethz dot ch<br/>
</div>

<div class="rightbox">
    <b>Office address:</b><br/>
    ETH Zurich Systems Group<br/>
    STF H 313<br/>
    Stampfenbachstrasse 114<br/>
    8092 Zürich<br/>
    Switzerland<br/>
</div>

<div class="rightbox">
  <b>Full CV:</b> <a href="{{ "/cv/" | absolute_url }}">here</a><br/>
</div>

<div style="clear: both; display: table;"></div>

I am a postdoc in [Prof. Timothy (Mothy) Roscoe](https://people.inf.ethz.ch/troscoe/)'s group, in the [Systems Group](http://www.systems.ethz.ch/) of the [Department of Computer Science](http://www.inf.ethz.ch) at [ETH Zürich](http://www.ethz.ch).

My background is in formal methods.
I did my PhD at [MIT](https://web.mit.edu/) in [Prof. Adam Chlipala](http://adam.chlipala.net)'s group, working on machine-checked end&#8209;to&#8209;end proofs about software-hardware stacks.

Now, as a postdoc in Mothy's group, I am excited to learn about [real operating systems](https://dl.acm.org/doi/10.1145/3593856.3595903) and to apply formal methods to systems research.

Currently, I am leading the development of **Sockeye**, a domain-specific [language](https://arxiv.org/abs/2510.27485) and [analysis tool](https://gitlab.inf.ethz.ch/project-opensockeye/sockeye) to formalize and analyze hardware reference manuals of Systems-on-a-Chip (SoCs).
It supports both automated bug finding as well as proving security properties about hardware platforms and their configurations,
and comes with a growing [library](https://gitlab.inf.ethz.ch/project-opensockeye/sockeye/-/tree/main/specs?ref_type=heads) of specifications of a diverse range of hardware platforms, unifying code by more than a dozen contributors.


## Past Projects

- I invented **Live Verification**, a [software development method](https://doi.org/10.1145/3656439) that enables programmers to formally verify their code *at the time they write it*. After each line of code that the programmer wrote, the tool displays a concise summary of everything it knows about the current state of the program, which can inform the programmer on what the next line of code should be, and once the programmer is done writing a function, the displayed summary of the symbolic state can be turned into a proof of a postcondition. I implemented the tool in the interactive theorem prover Coq (now called Rocq), so in order to trust proofs about programs written in it, one only needs to trust the language semantics and Coq's proof-checking kernel, but not the implementation of the Live Verification tool itself.
- **Trouble combining undefined behavior and nondeterminism? ➔&nbsp;Try [omnisemantics](/blog/2022/09/30/omnisemantics/)!**<br>
While working on [Bedrock2](https://github.com/mit-plv/bedrock2), my colleague [Andres Erbsen](https://andres.systems/) and me came up with a style of programming language semantics that we think works much better in the presence of *undefined&nbsp;behavior* and *nondeterminism* than using traditional smallstep or bigstep operational semantics would.
A little later, our advisor [Adam Chlipala](http://adam.chlipala.net/) chatted with [Arthur Charguéraud](https://www.chargueraud.org/) and they found out that he had discovered the same style of semantics as well, but was using it for functional languages, while we were using it for imperative languages.
Together, we wrote a [paper](https://dl.acm.org/doi/10.1145/3579834) about it, or if you prefer just a short introduction, you can also check out this [blog post](/blog/2022/09/30/omnisemantics/).
- With my colleague [Andres Erbsen](https://andres.systems/), I developed [Bedrock2](https://github.com/mit-plv/bedrock2), **a program logic to formally verify systems code**.
- I developed **formal RISC-V ISA semantics** in Coq that support a [wide range of use cases](https://doi.org/10.1145/3607833).
- I wrote a **formally verified compiler** in Coq from a small subset of C (as specified by [Bedrock2](https://github.com/mit-plv/bedrock2)) to RISC-V machine code (as specified by [riscv-coq](https://github.com/mit-plv/riscv-coq)). It enabled several research projects of me as well as of my colleagues, including
end-to-end systems proofs that [cross the software-hardware boundary](https://doi.org/10.1145/3453483.3454065),
a formally verified [cryptographic server](https://doi.org/10.1145/3656446),
proofs about a [trap handler](https://doi.org/10.4230/LIPIcs.ITP.2024.17) combining C and assembly,
a compiler extension to support proving [running-time bounds](https://doi.org/10.1145/3779031.3779088),
another extension to prove [cryptographic constant time](https://dl.acm.org/doi/10.1145/3729318),
and it also served as a case study to illustrate the advantages of [omnisemantics](https://doi.org/10.1145/3579834).
I wrote up its design considerations in Chapter 3 of [my thesis](/assets/thesis.pdf).
- I was visiting [Dr. Toby Murray](https://people.eng.unimelb.edu.au/tobym/) at the [University of Melbourne](https://www.unimelb.edu.au/) for 10 weeks to work on **information flow control proofs for C**.
- For a six months master thesis internship, I was working with [Prof. Andrew Appel](https://www.cs.princeton.edu/~appel/)'s group at Princeton, improving the proof automation tactics of their **Verified Software Toolchain**. ([VST](https://github.com/PrincetonUniversity/VST)), and using it to verify the AES encryption [implementation](https://github.com/ARMmbed/mbedtls/blob/development/library/aes.c) of mbed TLS.
- During my master's at EPFL, I was working with Prof. Martin Odersky's [Scala lab](https://lamp.epfl.ch/) on the **Dependent Object Types** project, a formalization of the core of Scala's type system, writing proofs on paper and using the proof assistants [Twelf](http://twelf.org) and [Coq](https://coq.inria.fr/).
- For a class project at EPFL, I contributed to the function **termination checker** of [Leon](http://lara.epfl.ch/w/leon), a tool for verification and synthesis of Scala programs by Prof. Viktor Kuncak's [group](http://lara.epfl.ch/w/).
- While working at the Scala lab, I contributed to [dotty](http://dotty.epfl.ch/), a new **Scala compiler** serving as a research platform to investigate new language concepts and compiler technologies for Scala, which eventually became the compiler for Scala 3.
- For my bachelor thesis, I designed, explored and implemented a simple **structurally typed language** in [PLT redex](https://redex.racket-lang.org/).


<style>
.bibtexnumber a, .bibtexnumber a:hover {
    color: #000;
    text-decoration: none;
}
</style>

## Publications

{% include_relative publications.html %}


## Preprints, Theses, Reports

{% include_relative reports.html %}


## Education

- September 2024: PhD in Computer Science at MIT with [Prof. Adam Chlipala](http://adam.chlipala.net/)'s Programming Languages and Verification Group
- April 2017: MSc in Computer Science from [EPFL](https://www.epfl.ch/) in Lausanne, Switzerland
- July 2013: BSc in Computer Science from EPFL


## Industry Experience

- Summer 2021: At Google Research, worked on the [Silver Oak Project](https://github.com/project-oak/silveroak), using [Bedrock2](https://github.com/mit-plv/bedrock2) to formally verify drivers for peripherals used in the [OpenTitan](https://opentitan.org/) root of trust, and connected software correctness proofs to hardware correctness proofs
- Summer 2019: Worked with [Rustan Leino](http://leino.science/) at Amazon's Automated Reasoning Group on a prototype rewrite of [Amazon's S3 Encryption Client](https://aws.amazon.com/articles/client-side-data-encryption-with-the-aws-sdk-for-java-and-amazon-s3/) in Dafny, a verification-aware programming language. Wrote and proved specifications for software interacting with real-world systems such as Amazon's S3 storage service
- Fall 2015: 6 months Software Engineering Internship at Netcetera AG, Berne, working in a scrum team, developing a Web Application with a Java/Oracle DB/Spring backend and an AngularJS/TypeScript frontend
- Summer 2012: Java Internship at Accenture in Bangalore (India), developed a web interface with JSF/Enterprise JavaBeans monitoring hundreds of servers and databases
