+++
id = "lem-fin-closed-immersion"
kind = "theorem"
title = "Closed immersions preserve constructibility"
order = 1593
tags = ["latex:corollary"]
lean = ["AlgebraicGeometry.Scheme.IsConstructibleSheaf.lowerStar_of_isClosedImmersion"]
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-scheme-conventions", "lem-fin-finite-morphism"]
+++
Let $i:Z\hookrightarrow X$ be a closed immersion with $X$ of finite type over $k$, and let $G$ be a constructible $\Lambda$-sheaf on $Z_{{\mathrm{et}}}$. Then $i_*G$ is constructible on $X_{{\mathrm{et}}}$ and $R^qi_*G=0$ for $q>0$.

## Proof

A closed immersion is affine and induced locally by a surjective ring
homomorphism, so $i_*\mathcal O_Z$ is a finite $\mathcal O_X$-algebra:
the source is a finite module over the target locally, which is the
finiteness condition of [def-weil-pbc-scheme-conventions].
Hence $i$ is finite in the sense of
[def-weil-pbc-scheme-conventions] and
[lem-fin-finite-morphism] applies.
