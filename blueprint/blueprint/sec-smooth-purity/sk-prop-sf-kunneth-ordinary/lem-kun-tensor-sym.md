+++
id = "lem-kun-tensor-sym"
kind = "lemma"
title = "Symmetry of the derived tensor product"
order = 1710
uses = ["def-kun-derived-tensor", "def-weil-pbc-derived-categories"]
+++
For a commutative ring $\Lambda$ and $A,B\in D(T_{\Et},\Lambda)$
there is a canonical isomorphism

$$
A\kunotimes{\Lambda}B\cong B\kunotimes{\Lambda}A
$$

in $D(T_{\Et},\Lambda)$, natural in $A$ and $B$.

## Proof

Choose K-flat resolutions $P\to A$ and $Q\to B$; both derived
products are computed as $P\otimes_\Lambda B$ and
$Q\otimes_\Lambda A$, and the canonical symmetry of the ordinary
tensor product induces, after K-flat replacement, the displayed
canonical isomorphism (the two routes agree because the comparison
maps between K-flat resolutions become quasi-isomorphisms after
tensoring, see [def-kun-derived-tensor]).
