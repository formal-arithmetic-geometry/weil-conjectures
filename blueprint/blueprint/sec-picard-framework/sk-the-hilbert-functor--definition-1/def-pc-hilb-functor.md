+++
id = "def-pc-hilb-functor"
kind = "definition"
title = "The Hilbert functor $\\operatorname{Hilb}^d_{X/S}$"
order = 767
uses = ["def-pc-base-change", "def-pc-finite-locally-free", "def-pc-representable-functor"]
lean = ["AlgebraicGeometry.hilbertPresheaf"]
+++
Let $X\to S$ be a morphism of schemes and $d\geq0$. For a scheme $T$
over $S$ put

$$
\operatorname{Hilb}^d_{X/S}(T):=\bigl\{Z\subset X_T\ \text{a closed subscheme}:\
Z\to T\text{ is finite locally free of degree }d\bigr\},
$$

where ``finite locally free of degree $d$'' is
Definition [def-pc-finite-locally-free] and $X_T$ is the base change of
[def-pc-base-change]. If this functor is representable
([def-pc-representable-functor]), the representing scheme is
$\underline{\operatorname{Hilb}}^d_{X/S}$ (Stacks Project, Picard Schemes of Curves,
Chapter 44, Section 44.2, Tag
[0B94](https://stacks.math.columbia.edu/tag/0B94)).
