+++
id = "def-pc-zariski-sheaf-property"
kind = "definition"
title = "Zariski sheaf property of a functor"
order = 778
uses = ["def-pc-scheme"]
+++
Let $F:(\mathit{Sch})^{\mathrm{op}}\to\textit{Sets}$ be a functor. $F$
*satisfies the sheaf property for the Zariski topology* if for every
scheme $T$, every open covering $T=\bigcup_{i\in I}U_i$ and every
collection $\xi_i\in F(U_i)$ with
$\xi_i|_{U_i\cap U_j}=\xi_j|_{U_i\cap U_j}$ there is a unique
$\xi\in F(T)$ with $\xi|_{U_i}=\xi_i$ (Schemes, Definition 26.15.3, Tag
[01JI](https://stacks.math.columbia.edu/tag/01JI)).
