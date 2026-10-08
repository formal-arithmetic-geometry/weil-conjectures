+++
id = "lem-pd-picard-base-change"
kind = "lemma"
title = "The Picard functor is compatible with base change"
order = 854
uses = ["def-pc-base-change", "def-pc-fppf-site", "def-pc-picard-functor", "def-pc-picard-presheaf", "lem-pc-pic-presheaf-functorial"]
+++
Let $f:X\to S$ be a morphism of schemes and let $g:S'\to S$ be a morphism,
with base change $f':X_{S'}\to S'$ of $f$ along
$g$. Then the restriction of the
Picard functor
$\operatorname{Pic}_{X/S}$ to the slice site
$(\mathit{Sch}/S')_{fppf}\subseteq(\mathit{Sch}/S)_{fppf}$ of
[def-pc-fppf-site] is the Picard functor
$\operatorname{Pic}_{X_{S'}/S'}$.

## Proof

For $T\in\mathit{Ob}((\mathit{Sch}/S')_{fppf})$ the base changes agree:
$X_T=(X_{S'})_T$ as schemes over $T$, by the transitivity of the fibre product
in [def-pc-base-change]. Hence the Picard *presheaves*
$T\mapsto\operatorname{Pic}(X_T)$ and $T\mapsto\operatorname{Pic}((X_{S'})_T)$
of [def-pc-picard-presheaf] (functors by [lem-pc-pic-presheaf-functorial]) are literally the same functor on the slice.
Sheafification of a presheaf on a site is computed by applying the plus
construction to the restriction of the presheaf to the slice categories of the
coverings, and the coverings of $(\mathit{Sch}/S')_{fppf}$ are exactly the
fppf coverings in $(\mathit{Sch}/S)_{fppf}$ of [def-pc-fppf-site] whose
objects lie over $S'$; since the two presheaves coincide on the whole slice, so
do their sheafifications, and the resulting restriction is the Picard functor
$\operatorname{Pic}_{X_{S'}/S'}$ of [def-pc-picard-functor].
This is the assertion, and it is the remark following Stacks Project,
Definition 44.4.1, Tag [0B9K](https://stacks.math.columbia.edu/tag/0B9K).
