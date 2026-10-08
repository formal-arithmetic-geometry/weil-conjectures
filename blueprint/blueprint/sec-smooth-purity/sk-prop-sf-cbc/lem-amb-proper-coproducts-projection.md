+++
id = "lem-amb-proper-coproducts-projection"
kind = "lemma"
title = "The proper projection formula on the ambient category"
order = 1563
uses = ["def-weil-derived-tensor", "def-weil-pbc-derived-categories", "def-weil-pbc-direct-image", "def-weil-pbc-inverse-image", "def-weil-pbc-projection-formula-map", "def-weil-scheme-morphism-properties", "lem-amb-proper-coproducts", "lemma-weil-pbc-geometric-stalk-conservative"]
+++
Let $r:V\to T$ be a proper
morphism of finite type between Noetherian schemes. For all complexes
$L$ on $V$ and $K$ on $T$, the canonical
derived tensor projection map is an
isomorphism in the ordinary
derived category:

$$
K\otimes_A^LRr_*L\longrightarrow Rr_*(r^*K\otimes_A^LL).
$$

The notation refers to derived direct images, and inverse images.

## Proof

Test the projection map of
[def-weil-pbc-projection-formula-map] at a geometric point
$\bar t$. It becomes the constant-coefficient map

$$
K_{\bar t}\otimes_A^LR\Gamma(V_{\bar t},L|_{V_{\bar t}})
\longrightarrow
R\Gamma(V_{\bar t},\underline{K_{\bar t}}\otimes_A^LL|_{V_{\bar t}}).
$$

Both sides, as functors of $K_{\bar t}\in D(A)$, are exact
and preserve coproducts. This follows on the right from the coproduct result
[lem-amb-proper-coproducts] applied over the geometric point. The comparison is the
identity for $K_{\bar t}=A$. The shifts of $A$ generate
$D(A)$ under coproducts and cones: free resolutions and their
truncations give the usual explicit construction. Hence the map
is an isomorphism for every $K_{\bar t}$. [lemma-weil-pbc-geometric-stalk-conservative] proves the assertion on $T$.
