+++
id = "rem-sf-trace-coherence"
kind = "remark"
title = "Why this coherence is not in the axiom list"
order = 2334
uses = ["def-sf-datum", "lem-trf-trace-map-exchange", "lem-trf-trace-source-exchange", "prop-compactification-coherence-detailed"]
+++
The identity of [lem-trf-trace-map-exchange] is not a consequence of
[def-sf-datum](A1)–(A6) as they are stated there: the isomorphism
$Lg'^*f^!\cong f'^!Lg^*$ that produces it is base change for $f^!$
*against pullback*, not the adjoint form [thm-sf-dual-base-change],
which concerns $Rf^!Rg_*$ and is unconditional. The identity is nevertheless
a theorem of the blueprint, proved where the trace is constructed
([lem-trf-trace-map-exchange], [lem-trf-trace-source-exchange]); the
geometric reason is that both the exchange and the trace are mates of the same
structure maps of the compactification
([prop-compactification-coherence-detailed]). A reader who works axiomatically
from [def-sf-datum] alone must therefore import this coherence from the
trace-formula chapter. It is not an additional axiom, and no statement of
this chapter is left unproved on account of it: the framework-level form is
[lem-trf-trace-map-exchange].
