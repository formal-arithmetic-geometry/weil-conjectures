+++
id = "lemma-weil-pbc-universal-homeomorphism-coverings"
kind = "lemma"
title = "Covering compatibility for universal homeomorphisms"
order = 1111
lean = ["AlgebraicGeometry.Scheme.Hom.functorPushforward_mem_smallEtaleTopology_iff"]
+++
Let $u:X_0\to X$ be a universal homeomorphism. A family $\{U_i\to U\}$ of
etale $X$-schemes is jointly surjective if and only if its base change along
$u$ is jointly surjective.

## Proof

This is the topology half, the omission in Tag `03SI`. For a
family $\{U_i\to U\}$ of etale $X$-schemes, set
$Z=|U|\setminus\bigcup_i\operatorname{im}(|U_i|\to|U|)$. Base change gives
a homeomorphism $|U\times_XX_0|\to|U|$, and its inverse image of $Z$ is
exactly the complement of the union of the base-changed images. Hence
$Z=\varnothing$ if and only if that inverse image is empty. This proves
joint surjectivity in both directions. The identity and composition
compatibilities already proved show that this correspondence of covering
families respects refinements and composite coverings.
