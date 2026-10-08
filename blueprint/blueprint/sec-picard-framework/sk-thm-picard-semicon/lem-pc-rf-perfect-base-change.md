+++
id = "lem-pc-rf-perfect-base-change"
kind = "lemma"
title = "Perfectness of $Rf_*\\mathcal{G}$ and base change"
order = 675
uses = ["def-pc-base-change", "def-pc-derived-category", "def-pc-derived-direct-image", "def-pc-derived-pullback", "def-pc-morphism-conventions", "def-pc-perfect-complex", "lem-pc-projective-noetherian-rf-perfect", "lem-pc-rf-base-change-flat-module"]
+++
Let $S$ be a scheme, $f:X\to S$ a proper morphism of finite
presentation, and let $\mathcal{G}$ be an $\mathcal{O}_X$-module of finite presentation
and flat over $S$. Then $Rf_*\mathcal{G}$ is a perfect object of $D(\mathcal{O}_S)$,
and its formation commutes with arbitrary base change: for every
morphism $g:T\to S$ the canonical map

$$
Lg^*(Rf_*\mathcal{G})\;\longrightarrow\;Rf_{T,*}\mathcal{G}_T
$$

is an isomorphism in $D(\mathcal{O}_T)$.

## Proof

The base-change assertion is
[lem-pc-rf-base-change-flat-module]; proper morphisms are
quasi-compact and separated. If the base is locally Noetherian
and $f$ is projective, the perfectness assertion follows from
[lem-pc-projective-noetherian-rf-perfect].
For a general proper $f$ of finite presentation the perfectness
assertion is the recorded classical input: Derived Categories of Schemes,
Lemma 36.30.4 (Tag [0B91](https://stacks.math.columbia.edu/tag/0B91))
reads, in clause (2), ``Let $S$ be a scheme. Let $f:X\to S$ be a
proper morphism of finite presentation. ... Let $\mathcal{G}$ be an
$\mathcal{O}_X$-module of finite presentation, flat over $S$. Then
$Rf_*\mathcal{G}$ is a perfect object of $D(\mathcal{O}_S)$ and its
formation commutes with arbitrary base change.'', which is this lemma;
its proof is the cohomology-and-base-change theorem of the same section
(Lemma 36.30.1, Tag [0A1H](https://stacks.math.columbia.edu/tag/0A1H)),
not decomposed here.
