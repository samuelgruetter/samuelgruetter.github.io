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
  <img style="float: left; padding-right: 10px; padding-bottom: 10px" src="{{ "/assets/gruetter_samuel_2.jpg" | absolute_url }}">
</div>

<div class="rightbox">
  I'm a PhD student at <a href="https://www.csail.mit.edu/">MIT CSAIL</a>, advised by <a href="http://adam.chlipala.net/">Prof. Adam Chlipala</a>.
</div>

<div class="rightbox">
  <b>Email:</b> My last name at mit dot edu <br/>
</div>

<div class="rightbox">
    <b>Office address:</b><br/>
    <a href="https://www.csail.mit.edu/sites/default/files/resources/maps/8G/G822.gif">32-G822</a><br/>
    MIT CSAIL, Stata Center<br/>
    32 Vassar Street<br/>
    Cambridge MA 02139<br/>
    USA<br/>
</div>

{% comment %}
TODO Link to full CV
{% endcomment %}

<div style="clear: both; display: table;"></div>

## Research Interests

I'm interested in Programming Languages and Verification, Interactive Theorem Proving, Language Design, Compilers, Specifications, and Software Engineering.

Currently, I'm working on a [verified compiler](https://github.com/mit-plv/bedrock2/) from a very simple C-like language to [RISC-V](https://riscv.org/) machine code.


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


## Reports

{% include_relative reports.html %}


## Education

- Since September 2017: Pursuing a PhD in Computer Science at MIT with [Prof. Adam Chlipala](http://adam.chlipala.net/)'s Programming Languages and Verification Group
- April 2017: MSc in Computer Science from [EPFL](www.epfl.ch) in Lausanne, Switzerland
- July 2013: BSc in Computer Science from EPFL


## Industry Experience

- Fall 2015: 6 months Software Engineering Internship at Netcetera AG, Berne, working in a scrum team, developing a Web Application with a Java/Oracle DB/Spring backend and an AngularJS/TypeScript frontend
- Summer 2012: Java Internship at Accenture in Bangalore (India), developed a web interface with JSF/Enterprise JavaBeans monitoring hundreds of servers and databases
