+++
id = "def-pc-euler-characteristic"
kind = "definition"
title = "The Euler characteristic"
order = 724
uses = ["def-pc-derived-direct-image", "def-pc-morphism-conventions", "def-pc-scheme"]
+++
Let $k$ be a field, $X$ a proper scheme over $k$ and $\mathcal{F}$ a coherent
$\mathcal{O}_X$-module. The *Euler characteristic* of $\mathcal{F}$ is

$$
\chi(X,\mathcal{F}):=\sum_i(-1)^i\dim_kH^i(X,\mathcal{F})\in\Z ,
$$

where $H^i(X,\mathcal{F})$ are the
higher direct images of
$\mathcal{F}$ for the structure morphism.
