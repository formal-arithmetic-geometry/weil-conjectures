+++
id = "cor-exc-base-change-open-immersion-general"
kind = "theorem"
title = "Base change for an arbitrary morphism, against an open immersion"
order = 1815
tags = ["latex:corollary"]
uses = ["cor-exc-base-change-reduces-to-proper", "cor-sf-ambient-adjoint-discharge", "def-sf-fullcd-used-class", "def-weil-ambient-exceptional-adjoint", "prop-exc-base-change-proper", "thm-nagata-compactification"]
+++
Let $f:X\to Y$ be separated finite type carrying the ambient exceptional
right adjoint datum of [def-weil-ambient-exceptional-adjoint], and let
$g:Y'\hookrightarrow Y$ be an *open immersion*. Then the
base-change comparison $Lg'^*Rf^{\times}\to Rf'^{\times}Lg^*$ is an
isomorphism. In particular the base-change comparison holds for the
passage from an affine open of the base to the base, which is what an
assembly on affine charts requires. On the blueprint's coefficient class
[def-sf-fullcd-used-class] the ambient datum displayed as the hypothesis
is the theorem [cor-sf-ambient-adjoint-discharge], so the comparison is
an isomorphism on that class without hypothesis, and it is on that class that
the assembly of [thm-pur-general-admissibility] consumes it.

## Proof

Choose a compactification $X\xrightarrow{j_0}\overline X\xrightarrow{p}Y$
of [thm-nagata-compactification], with $p$ proper. By
[prop-exc-base-change-proper] the comparison holds for $p$ against
the open immersion $g$, and by
[cor-exc-base-change-reduces-to-proper] the comparison for $f$
follows from that for $p$.
