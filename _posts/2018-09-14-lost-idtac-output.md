---
layout: post
title:  "Ltac: Where did my idtac debug output go?"
---

<div class="doc">

When debugging Ltac tactics in Coq, one can use <span class="inlinecode"><span class="id" title="keyword">idtac</span></span> to print debug messages. However, when a tactic invocation fails, ProofGeneral will not display any of the debug output in the <span class="inlinecode"><span class="id" title="keyword">*response*</span></span> buffer, so in order to read our debug output, we have to read the <span class="inlinecode"><span class="id" title="keyword">*coq*</span></span> buffer or precede the failing command with <span class="inlinecode"><span class="id" title="keyword">Fail</span></span>.

</div>

<!--more-->

{% include_relative LostIdtacOutput.v.html %}
