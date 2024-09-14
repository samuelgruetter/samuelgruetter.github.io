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
  <img style="float: left; padding-right: 10px; padding-bottom: 10px" src="{{ "/assets/2024_samuel_gruetter.jpg" | absolute_url }}">
</div>

<div class="rightbox">
  I recently completed my PhD at <a href="https://www.csail.mit.edu/">MIT CSAIL</a>, advised by <a href="http://adam.chlipala.net/">Prof. Adam Chlipala</a>. More website updates following soon!
</div>

<div class="rightbox">
  <b>Email:</b> My last name at mit dot edu <br/>
</div>

<!-- commented out because not physically there any more
<div class="rightbox">
    <b>Office address:</b><br/>
    <a href="https://www.csail.mit.edu/sites/default/files/resources/maps/8G/G886.gif">32-G886</a><br/>
    MIT CSAIL, Stata Center<br/>
    32 Vassar Street<br/>
    Cambridge MA 02139<br/>
    USA<br/>
</div>
-->

<div class="rightbox">
  <b>Full CV:</b> <a href="{{ "/cv/" | absolute_url }}">here</a><br/>
</div>

<div style="clear: both; display: table;"></div>

## Research Interests

I'm interested in Programming Languages and Verification, Interactive Theorem Proving, Language Design, Compilers, Specifications, and Software Engineering.

Currently, I'm working on the [Bedrock2](https://github.com/mit-plv/bedrock2/) project.
It includes a very simple C-like source language, a program logic for it, and a compiler to [RISC-V](https://riscv.org/) machine code, as specified by [riscv-coq](https://github.com/mit-plv/riscv-coq). Another project of our group, [Kami](http://plv.csail.mit.edu/kami/), developed a RISC-V processor and proved it correct against the same [riscv-coq](https://github.com/mit-plv/riscv-coq) spec, which enabled us to prove an end-to-end theorem about the behavior of a whole software-hardware stack.
The first milestone of this project is the IoT lightbulb, which we presented at PLDI'21 (see [paper](https://dl.acm.org/doi/10.1145/3453483.3454065) and [video](https://www.pldi21.org/poster_pldi.244.html#tab-extended)). Earlier, I also gave a talk about it at the [RISC-V Summit 2019](https://riscv.org/2019/12/risc-v-summit-2019-proceedings/), and you can find the video recording [here](https://www.youtube.com/watch?v=FmWZKRScs-o).


## Trouble combining undefined behavior and nondeterminism? ➔&nbsp;Try [omnisemantics](/blog/2022/09/30/omnisemantics/)!

While working on Bedrock2, my colleague [Andres Erbsen](https://andres.systems/) and me came up with a style of programming language semantics that we think works much better in the presence of **undefined&nbsp;behavior** and **nondeterminism** than using traditional smallstep or bigstep operational semantics would.
A little later, our advisor [Adam Chlipala](http://adam.chlipala.net/) chatted with [Arthur Charguéraud](https://www.chargueraud.org/) and they found out that he had discovered the same style of semantics as well, but was using it for functional languages, while we were using it for imperative languages.
Together, we wrote a paper about it, and you can find a preprint [here](https://hal.archives-ouvertes.fr/hal-03255472), or if you prefer just a short introduction, you can also check out this [blog post](/blog/2022/09/30/omnisemantics/).


## Past Projects

- I was visiting [Dr. Toby Murray](https://people.eng.unimelb.edu.au/tobym/) at the [University of Melbourne](https://www.unimelb.edu.au/) for 10 weeks to work on information flow control proofs for C
- For a six months master thesis internship, I was working with [Prof. Andrew Appel](https://www.cs.princeton.edu/~appel/)'s group at Princeton, improving the proof automation tactics of their [Verified Software Toolchain](https://github.com/PrincetonUniversity/VST), and using it to verify the AES encryption [implementation](https://github.com/ARMmbed/mbedtls/blob/development/library/aes.c) of mbed TLS
- During my master's at EPFL, I was working with Prof. Martin Odersky's [Scala lab](https://lamp.epfl.ch/) on the *Dependent Object Types* project, a formalization of the core of Scala's type system, writing proofs on paper and using the proof assistants [Twelf](http://twelf.org) and [Coq](https://coq.inria.fr/)
- For a class project at EPFL, I contributed to the function termination checker of [Leon](http://lara.epfl.ch/w/leon), a tool for verification and synthesis of Scala programs by Prof. Viktor Kuncak's [group](http://lara.epfl.ch/w/)
- While working at the Scala lab, I contributed to [dotty](http://dotty.epfl.ch/), a new Scala compiler serving as a research platform to investigate new language concepts and compiler technologies for Scala
- For my bachelor thesis, I designed, explored and implemented a simple structurally typed language in [PLT redex](https://redex.racket-lang.org/)


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
- April 2017: MSc in Computer Science from [EPFL](www.epfl.ch) in Lausanne, Switzerland
- July 2013: BSc in Computer Science from EPFL


## Industry Experience

- Summer 2021: At Google Research, worked on the [Silver Oak Project](https://github.com/project-oak/silveroak), using [Bedrock2](https://github.com/mit-plv/bedrock2) to formally verify drivers for peripherals used in the [OpenTitan](https://opentitan.org/) root of trust, and connected software correctness proofs to hardware correctness proofs
- Summer 2019: Worked with [Rustan Leino](http://leino.science/) at Amazon's Automated Reasoning Group on a prototype rewrite of [Amazon's S3 Encryption Client](https://aws.amazon.com/articles/client-side-data-encryption-with-the-aws-sdk-for-java-and-amazon-s3/) in Dafny, a verification-aware programming language. Wrote and proved specifications for software interacting with real-world systems such as Amazon's S3 storage service
- Fall 2015: 6 months Software Engineering Internship at Netcetera AG, Berne, working in a scrum team, developing a Web Application with a Java/Oracle DB/Spring backend and an AngularJS/TypeScript frontend
- Summer 2012: Java Internship at Accenture in Bangalore (India), developed a web interface with JSF/Enterprise JavaBeans monitoring hundreds of servers and databases
