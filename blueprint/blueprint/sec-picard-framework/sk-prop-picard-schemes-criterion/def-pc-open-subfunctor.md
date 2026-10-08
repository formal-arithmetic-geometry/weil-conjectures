+++
id = "def-pc-open-subfunctor"
kind = "definition"
title = "Subfunctors representable by open immersions"
order = 779
uses = ["def-pc-scheme", "def-pc-subfunctor"]
+++
Let $F:(\mathit{Sch})^{\mathrm{op}}\to\textit{Sets}$ be a functor and
$H\subseteq F$ a subfunctor. $H\subseteq F$ is *representable by open immersions* if for all pairs
$(T,\xi)$ with $T$ a scheme and $\xi\in F(T)$ there is an open
subscheme $U_\xi\subseteq T$ such that a morphism $f:T'\to T$ factors
through $U_\xi$ if and only if $f^*\xi\in H(T')$ (Schemes,
Definition 26.15.3, Tag
[01JI](https://stacks.math.columbia.edu/tag/01JI)).
