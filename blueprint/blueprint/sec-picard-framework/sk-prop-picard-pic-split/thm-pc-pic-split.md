+++
id = "thm-pc-pic-split"
kind = "theorem"
title = "The split exact sequence for the Picard functor"
order = 815
uses = ["def-pc-pic-sigma-functor", "def-pc-picard-functor", "def-pc-subfunctor", "lem-pc-k-sheaf", "lem-pc-pic-exact"]
lean = ["AlgebraicGeometry.injective_pic_map_snd", "AlgebraicGeometry.pic_map_sectionBaseChange_snd", "AlgebraicGeometry.bijective_toPicardFunctor_picardFunctorNormalized", "AlgebraicGeometry.bijective_pic_split"]
+++
(Picard Schemes of Curves, Lemma 44.4.3, Tag
[0B9N](https://stacks.math.columbia.edu/tag/0B9N).)
Let $f:X\to S$ be a morphism of schemes as in
Definition [def-pc-picard-functor].
Assume $f$ has a section $\sigma$ and that
$\mathcal{O}_T\to f_{T,*}\mathcal{O}_{X_T}$ is an isomorphism for all
$T\in\operatorname{Ob}((\mathit{Sch}/S)_{fppf})$. Then the sequence

$$
0\longrightarrow\operatorname{Pic}(T)\xrightarrow{\ f_T^*\ }\operatorname{Pic}(X_T)
\xrightarrow{\ }\operatorname{Pic}_{X/S}(T)\longrightarrow 0
$$

is exact and split, the splitting being given by
$\sigma_T^*:\operatorname{Pic}(X_T)\to\operatorname{Pic}(T)$ (i.e. for every $T$,
$\operatorname{Pic}(X_T)=\operatorname{Pic}(T)\oplus K(T)$ with
$K(T)=\operatorname{Ker}\sigma_T^*$, and $\operatorname{Pic}_{X/S}$ is the fppf
sheafification of the presheaf $K$).

## Proof

Since $\sigma$ is a section of $f$, we have
$\sigma_T^*\circ f_T^*=\mathrm{id}_{\operatorname{Pic}(T)}$; hence $f_T^*$ is injective and, by
the splitting lemma for abelian groups,
$\operatorname{Pic}(X_T)=f_T^*(\operatorname{Pic}(T))\oplus K(T)$ (for $\mathcal{L}\in\operatorname{Pic}(X_T)$,
$\mathcal{L}=f_T^*\sigma_T^*\mathcal{L}\otimes(\mathcal{L}\otimes f_T^*\sigma_T^*\mathcal{L}^{-1})$ with
the second factor in $K(T)$). By [lem-pc-pic-exact] the kernel of
$\operatorname{Pic}(X_T)\to\operatorname{Pic}_{X/S}(T)$ is exactly $f_T^*(\operatorname{Pic}(T))$, in particular
$K(T)\subseteq\operatorname{Pic}_{X/S}(T)$ (already as a subset, compatibly with the
restriction maps). By [lem-pc-k-sheaf] the presheaf $K$ is an fppf
sheaf, and it is clear from the construction (the sheafification of the
pointwise split presheaf $T\mapsto\operatorname{Pic}(X_T)$ is its splitting, the first
summand $T\mapsto\operatorname{Pic}(T)$ being fppf-locally trivializable exactly
through the descent condition, cf. the argument of
[lem-pc-k-sheaf]) that $\operatorname{Pic}_{X/S}$ is the sheafification of $K$.
Consequently the third map is surjective and the sequence is split.
