+++
id = "thm-exc-curve-open-dimension-general"
kind = "theorem"
title = "Open direct-image dimension on arbitrary curves"
order = 1919
uses = ["def-weil-pbc-direct-image", "def-weil-pbc-scheme-conventions", "lem-exc-dvr-galois", "lem-exc-field-discrete-modules", "lem-exc-punctured-curve-branches", "lemma-weil-pbc-geometric-stalk-conservative", "prop-weil-pbc-strict-henselization-stalk-formula", "thm-weil-pbc-universal-homeomorphism-invariance"]
+++
Let $T$ be of finite type of dimension at most one over
a finite field or its algebraic closure, and let
$j:U\hookrightarrow T$ be any
open immersion.
Let $A$ be a finite commutative ring killed by a power
of a prime $\ell$ invertible on $T$. Then
$R^qj_*M$ is zero
for $q>1$ and every etale $A$-module sheaf $M$.

## Proof

Restriction to $U$ is exact and $j^*j_*$ is the
identity by [def-weil-pbc-direct-image], so all positive
direct-image stalks there vanish. Outside $U$, use the
stalk formula of
[prop-weil-pbc-strict-henselization-stalk-formula].
At a generic point belonging to the closed complement,
the strict local spectrum has dimension zero and its
pullback of $U$ is empty, giving zero.

For a closed point $t$, put
$R=\mathcal O^{\rm sh}_{T,\bar t}$.
This ring is excellent and Noetherian of dimension at
most one: finite-type field algebras are excellent, and
localization and strict henselization preserve excellence,
Noetherianness and local dimension. These are the ordinary
local-algebra permanence theorems. Its residue field is
algebraically closed, since the ground field is finite or
algebraically closed and $t$ is closed.
Replace $R$ by $R_{\rm red}$, which changes neither
the etale site nor its cohomology, by
[thm-weil-pbc-universal-homeomorphism-invariance].
If its dimension is zero, the open above $U$ is empty.
Otherwise that open is contained in the punctured spectrum
and hence, by [lem-exc-punctured-curve-branches], is a
disjoint union of a subset of the finitely many branch fields.

For every such field, [lem-exc-field-discrete-modules]
identifies etale cohomology, including for arbitrary $M$,
with continuous Galois cohomology. The DVR computation
[lem-exc-dvr-galois] makes it zero above degree one.
A finite disjoint union has the finite product of these
cohomology groups. Thus every stalk vanishes for $q>1$,
and [lemma-weil-pbc-geometric-stalk-conservative] proves
the asserted sheafwise vanishing.
