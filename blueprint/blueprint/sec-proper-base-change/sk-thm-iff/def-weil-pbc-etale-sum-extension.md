+++
id = "def-weil-pbc-etale-sum-extension"
kind = "definition"
title = "Extension by zero along an etale map"
order = 1069
uses = ["def-weil-pbc-etale-sheaves", "def-weil-pbc-etale-site"]
+++
Let $v:W\to X$ be etale [def-weil-pbc-etale-site] and let $M$ be a sheaf of
modules over a constant ring $A$ on $W_{\Et}$, as in
[def-weil-pbc-etale-sheaves]. Define $v_!M$ by sheafifying the presheaf

$$
 V\longmapsto\bigoplus_{s\in\operatorname{Hom}_X(V,W)}M(V,s).
$$

Here $(V,s)$ denotes $V$ as an etale $W$-scheme, and restriction sends the
summand indexed by $s$ to the summand indexed by its restriction. When $v$ is
an open immersion this is the usual extension by zero: there is at most one
such lift.
