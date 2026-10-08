+++
id = "thm-fin-proper-constructibility-complete"
kind = "theorem"
title = "Proper direct-image constructibility"
order = 1621
uses = ["def-finrepair-property-c", "def-weil-pbc-scheme-conventions", "lem-fin-noetherian-chow-modification", "lem-finrepair-modification-c", "lem-weil-pbc-noetherian-finite-components", "thm-fin-projective-constructibility-complete", "thm-weil-pbc-universal-homeomorphism-invariance"]
+++
Every proper morphism
between schemes of finite type over $k$ satisfies
$\mathcal C(f)$ of [def-finrepair-property-c].

## Proof

The assertion is local on the target in the Zariski topology:
restriction to an open commutes with derived direct image because
open restriction has exact extension by zero as a left adjoint and
thus preserves injectives. Constructibility glues on a finite
open cover by refining finite partitions. We may assume $S$ affine.

Fix $f:X\to S$ and use Noetherian induction on closed subsets
$Z\subset X$, with their reduced structures.
For the empty set there is nothing to prove.
For nonempty $Z$, the morphism $f_Z:Z\to S$ is proper.
By [lem-fin-noetherian-chow-modification], choose
$\pi:Y\to Z$ proper, an isomorphism over a dense open $U\subset Z$,
with $Y\to S$ projective.
Its direct images are constructible by
[thm-fin-projective-constructibility-complete].
The complement $Z\setminus U$ is a proper closed subset, so its
proper map to $S$ has the desired property by induction.
Apply [lem-finrepair-modification-c].
That lemma uses $R\pi_*j'_!=j_!$, proved by proper base change,
rather than dropping the positive direct images of a general
pullback. It gives the assertion for $Z$.
This completes Noetherian induction.

The nilpotent closed immersion $X_{\mathrm{red}}\hookrightarrow X$
induces the etale equivalence of
[thm-weil-pbc-universal-homeomorphism-invariance], compatible
with direct image, so the result for $Z=X_{\mathrm{red}}$ proves
it for $X$.
The spaces used are Noetherian and have finitely many components
by [lem-weil-pbc-noetherian-finite-components]; hence every
partition and target cover in this argument can be taken finite.
