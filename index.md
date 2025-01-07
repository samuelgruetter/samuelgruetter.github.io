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
  <b>CV:</b> <a href="{{ "/cv/" | absolute_url }}">HTML</a> | <a href="{{ "/assets/cv-samuel-gruetter-v2024-10-14.pdf" | absolute_url }}">PDF</a> <br/>
</div>

<div style="clear: both; display: table;"></div>

I am a postdoc working with [Prof. Timothy (Mothy) Roscoe](https://people.inf.ethz.ch/troscoe/)'s group, in the [Systems Group](http://www.systems.ethz.ch/) of the [Department of Computer Science](http://www.inf.ethz.ch) at [ETH Zürich](http://www.ethz.ch).

I did my PhD at [MIT CSAIL](https://www.csail.mit.edu/) with [Prof. Adam Chlipala](http://adam.chlipala.net)'s group, working on machine-checked end&#8209;to&#8209;end proofs about software-hardware stacks for simple bare-metal embedded systems.

Now, as a postdoc in Mothy's group, I am excited to learn about [real operating systems](https://dl.acm.org/doi/10.1145/3593856.3595903) and to apply formal methods to systems research.


## Trouble combining undefined behavior and nondeterminism? ➔&nbsp;Try [omnisemantics](/blog/2022/09/30/omnisemantics/)!

While working on [Bedrock2](https://github.com/mit-plv/bedrock2), my colleague [Andres Erbsen](https://andres.systems/) and me came up with a style of programming language semantics that we think works much better in the presence of **undefined&nbsp;behavior** and **nondeterminism** than using traditional smallstep or bigstep operational semantics would.
A little later, our advisor [Adam Chlipala](http://adam.chlipala.net/) chatted with [Arthur Charguéraud](https://www.chargueraud.org/) and they found out that he had discovered the same style of semantics as well, but was using it for functional languages, while we were using it for imperative languages.
Together, we wrote a [paper](https://dl.acm.org/doi/10.1145/3579834) about it, or if you prefer just a short introduction, you can also check out this [blog post](/blog/2022/09/30/omnisemantics/).


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
- April 2017: MSc in Computer Science from [EPFL](https://www.epfl.ch/) in Lausanne, Switzerland
- July 2013: BSc in Computer Science from EPFL


## Industry Experience

- Summer 2021: At Google Research, worked on the [Silver Oak Project](https://github.com/project-oak/silveroak), using [Bedrock2](https://github.com/mit-plv/bedrock2) to formally verify drivers for peripherals used in the [OpenTitan](https://opentitan.org/) root of trust, and connected software correctness proofs to hardware correctness proofs
- Summer 2019: Worked with [Rustan Leino](http://leino.science/) at Amazon's Automated Reasoning Group on a prototype rewrite of [Amazon's S3 Encryption Client](https://aws.amazon.com/articles/client-side-data-encryption-with-the-aws-sdk-for-java-and-amazon-s3/) in Dafny, a verification-aware programming language. Wrote and proved specifications for software interacting with real-world systems such as Amazon's S3 storage service
- Fall 2015: 6 months Software Engineering Internship at Netcetera AG, Berne, working in a scrum team, developing a Web Application with a Java/Oracle DB/Spring backend and an AngularJS/TypeScript frontend
- Summer 2012: Java Internship at Accenture in Bangalore (India), developed a web interface with JSF/Enterprise JavaBeans monitoring hundreds of servers and databases
