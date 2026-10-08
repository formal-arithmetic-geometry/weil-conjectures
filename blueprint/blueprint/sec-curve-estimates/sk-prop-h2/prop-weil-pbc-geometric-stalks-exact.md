+++
id = "prop-weil-pbc-geometric-stalks-exact"
kind = "theorem"
title = "Exactness of geometric stalks"
order = 932
uses = ["def-weil-pbc-etale-sheaves", "def-weil-pbc-geometric-stalks"]
tags = ["latex:proposition"]
+++
For every geometric point $\bar t$ of $T$, the stalk functor $F\mapsto
F_{\bar t}$ of [def-weil-pbc-geometric-stalks]

$$
 \Ab(T_{\Et})\longrightarrow\Ab,\qquad F\longmapsto F_{\bar t}
$$

is exact (filtered colimits are exact and a stalk is a filtered colimit of
sections over pointed etale neighbourhoods).

## Proof

By [def-weil-pbc-geometric-stalks] the stalk $F_{\bar t}$ is the filtered
colimit of the section groups over pointed etale neighbourhoods. The category
of [def-weil-pbc-etale-sheaves] on $T_{\Et}$ is Grothendieck abelian, so
filtered colimits of sheaves are exact: kernels and images of the colimit are
the colimits of the kernels and images. Applied to a short exact sequence
$0\to F\to G\to H\to0$ this gives exactness of the sequence of colimits over
the filtered index category of pointed neighbourhoods on the kernel and image
parts, and for the cokernel part a section of $H$ over a pointed
neighbourhood which lifts over an etale cover of it still represents a
section of the filtered colimit after composing the index with a pointed
etale refinement; hence the sequence of stalks is exact.
