+++
id = "lemma-nagata-separate-constructible-closed"
kind = "lemma"
title = "Properties of constructible-boundary separation"
order = 251
lean = ["AlgebraicGeometry.exists_admissibleBlowup_disjoint_closures"]
uses = ["def-nagata-admissible-blowup", "def-nagata-constructible-closed-support", "def-nagata-extended-ideal", "def-nagata-finite-type-ideal-extension", "def-nagata-global-blowup", "def-nagata-qc-open-complement-ideal", "def-nagata-scheme-image-factor", "def-nagata-separate-closed-subschemes", "def-nagata-separate-constructible-closed", "def-nagata-strict-transform", "lemma-nagata-constructible-closed-support", "lemma-nagata-extend-finite-type-ideal", "lemma-nagata-qc-open-complement-ideal", "lemma-nagata-qc-open-complement-ideal-exists", "lemma-nagata-separate-closed-subschemes", "lemma-nagata-strict-transform-closure-characterization", "prop-nagata-global-blowup-cover-independent"]
+++
The constructed blow-up $\mathsf{CSepBl}_U(T_1,T_2)\to X$ is
$U$-admissible, and the closures of the inverse images of $T_1$ and $T_2$
are disjoint.

## Proof

By [lemma-nagata-constructible-closed-support],
$V(\mathcal J_i)=T_i$ in $U$. The restriction equality from
[lemma-nagata-extend-finite-type-ideal] consequently gives
$|Z_i\cap U|=T_i$, so $Z_1\cap Z_2\cap U=\varnothing$. Apply
[lemma-nagata-separate-closed-subschemes]. In the resulting
$U$-admissible blow-up $\pi\colon X'\to X$, the closure of
$\pi^{-1}(T_i)$ is contained in the underlying set of the strict transform
of $Z_i$: the strict transform is closed in $X'$, and it contains every
point lying both over the preserved open and over $Z_i$ — in particular
every point of $\pi^{-1}(T_i)$. The two strict transforms are disjoint,
so these two closures are disjoint as claimed.
