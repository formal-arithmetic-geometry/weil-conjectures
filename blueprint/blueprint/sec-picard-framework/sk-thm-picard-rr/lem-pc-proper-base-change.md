+++
id = "lem-pc-proper-base-change"
kind = "lemma"
title = "Proper and smooth morphisms are stable under base change"
order = 732
uses = ["def-pc-base-change", "def-pc-morphism-conventions", "def-pc-scheme", "def-weil-scheme-morphism-properties"]
+++
Let $f:X\to S$ be a proper morphism, let $g:S'\to S$ be arbitrary, and
let $f':X'=X\times_SS'\to S'$ be the base change. Then $f'$ is
proper. If $f$ is smooth, then $f'$ is smooth.

## Proof

*Properness.* $f'$ is separated and of finite type (base changes
of separated and finite type morphisms have these properties: the
diagonal of $f'$ is the base change of the diagonal of $f$, and the
base changes of finite type morphisms are of finite type, both by the
definitions of the properties, being Zariski-local and stable under
composition with the projections). For the universal closedness, use
the valuative criterion for properness ([lem-pc-projective-proper]
cites it, Tag 0BX4): a valuation square
a valuation square

$$
\operatorname{Spec} K \longrightarrow X'
$$

oindent over

$$
\operatorname{Spec} V \longrightarrow S'
$$

gives, by composition, the outer square
$\operatorname{Spec} K\to X\to S$ and $\operatorname{Spec} V\to S' \to S$; the criterion for the
proper $f$ gives the (unique) lift $\operatorname{Spec} V\to X$; its base change
along $g$ restricted... the maps $\operatorname{Spec} V\to S'$ and $\operatorname{Spec} V\to X$
(both over $S$) give the product morphism $\operatorname{Spec} V\to X\times_SS'=X'$
(the morphism into the fibre product from the two legs over $S$),
i.e. the required lift; uniqueness is inherited from the uniqueness
for $f$. Hence $f'$ satisfies the valuative criterion, and is proper.

*Smoothness.* Smoothness is Zariski-local on the base and the
target; affine-locally, a smooth ring map $R\to A$ remains smooth
after base change $R\to R'$: Algebra, Lemma 10.137.3, Tag
[00T4](https://stacks.math.columbia.edu/tag/00T4) (the proof: the
naive cotangent complex base changes, and the base change of a finite
projective module is finite projective, so the defining property of
Definition 10.137.1 (Tag
[00T2](https://stacks.math.columbia.edu/tag/00T2)) is preserved;
the finite presentation property is preserved by base change).
Hence $f'$ is smooth.
