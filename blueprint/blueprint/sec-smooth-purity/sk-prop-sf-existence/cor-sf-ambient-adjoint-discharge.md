+++
id = "cor-sf-ambient-adjoint-discharge"
kind = "theorem"
title = "The ambient datum relative to the bounded comparison class"
order = 1808
tags = ["latex:corollary"]
uses = ["def-weil-ambient-exceptional-adjoint", "def-weil-exceptional-adjoint-admissibility", "thm-sf-ambient-adjoint-class", "thm-sf-fullcd-class"]
+++
For the bounded constructible coefficient class at $A=A_{E,n}$, the
vanishing input is [thm-sf-fullcd-class] and the exceptional adjoint
relative to that class is [thm-sf-ambient-adjoint-class]. Thus the
bounded-class uses of clause (1) of
[def-weil-exceptional-adjoint-admissibility] have this concrete
interpretation. The unrestricted ambient datum of
[def-weil-ambient-exceptional-adjoint] is not asserted here; it is false in
general (an elliptic curve over $\overline{\mathbf F}_p$ with
$A=\mathbf F_r$, rem:sf-ambient-counterexample in the six-functors chapter),
and the constructible exceptional adjoint of
def-weil-exceptional-inverse-image is what the blueprint uses.

## Proof

Combine [thm-sf-fullcd-class] and
[thm-sf-ambient-adjoint-class]. The latter quantifies over
bounded-below inputs in the comparison class and bounded-below targets;
this includes the bounded constructible instances of
[def-weil-exceptional-adjoint-admissibility]. It does not supply
the all-object quantifiers of [def-weil-ambient-exceptional-adjoint].
