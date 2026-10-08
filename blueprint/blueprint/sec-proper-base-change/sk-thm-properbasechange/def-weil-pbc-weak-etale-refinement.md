+++
id = "def-weil-pbc-weak-etale-refinement"
kind = "definition"
title = "An affine refinement of a weakly etale algebra"
order = 1231
uses = ["def-weil-pbc-ind-etale-algebra", "def-weil-pbc-retained-localization", "def-weil-pbc-strict-w-cover", "lem-weil-pbc-strict-w-cover"]
+++
For a weakly etale [def-weil-pbc-ind-etale-algebra] map $A\to B$, take
$C=C_A$ from [def-weil-pbc-strict-w-cover], and let $J$ be the radical ideal
of its closed point subset, supplied by
[lem-weil-pbc-strict-w-cover]. Define

$$
 D_0=B\otimes_AC,\qquad
 B'= (D_0)_{[V(JD_0)]}
$$

using [def-weil-pbc-retained-localization].
