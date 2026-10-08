+++
id = "lem-fin-extension-by-zero"
kind = "lemma"
title = "Extension by zero preserves constructibility"
order = 1590
lean = ["AlgebraicGeometry.Scheme.IsConstructibleSheaf.openImmersionLowerShriek"]
uses = ["def-constructible-constant", "def-constructible-constructible", "def-constructible-finite", "def-constructible-finite-locally-constant", "def-constructible-locally-constant", "def-constructible-stratification", "def-kun-separably-closed", "def-weil-pbc-constructible-complexes", "def-weil-pbc-extension-by-zero", "def-weil-pbc-scheme-conventions", "lemma-constructible-iso-invariance", "lemma-constructible-pullback-locally-constant", "lemma-openclosed-vanishing-lowershriek", "prop-constructible-open-closed", "sbc-def-coefficient-conventions"]
+++
Let $X$ be of finite type over $k$, let $j:U\hookrightarrow X$ be an
open immersion, and let $F$
be a constructible
$\Lambda$-sheaf on $U_{{\mathrm{et}}}$. Then $j_!F$ of
[def-weil-pbc-extension-by-zero] is constructible on
$X_{{\mathrm{et}}}$.

## Proof

By [def-weil-pbc-constructible-complexes] $U$ has a finite
partition $U=\bigsqcup_\alpha U_\alpha$ into locally closed
constructible subschemes with $F|_{U_\alpha}$ lisse. The pieces
$U_\alpha$ are locally closed constructible subschemes of $X$ (locally
closed in the open subscheme $U$), and $X$ is the disjoint union of
$X\setminus U$ and the $U_\alpha$. By the stalk description of
[def-weil-pbc-extension-by-zero] the restriction of $j_!F$ to
$U_\alpha$ is the lisse $F|_{U_\alpha}$ and its restriction to
$X\setminus U$ is the zero sheaf, which is lisse; this is the finite
partition with lisse restrictions of
[def-weil-pbc-constructible-complexes].
