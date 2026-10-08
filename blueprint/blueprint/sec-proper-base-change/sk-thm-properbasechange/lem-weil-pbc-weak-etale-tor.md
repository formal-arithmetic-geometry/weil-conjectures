+++
id = "lem-weil-pbc-weak-etale-tor"
kind = "lemma"
title = "Flat diagonal and Tor groups"
order = 1216
uses = ["def-weil-pbc-ind-etale-algebra"]
+++
If $A\to B$ is weakly etale [def-weil-pbc-ind-etale-algebra], then for
$B$-modules $M,N$ there are natural identifications

$$
 \operatorname{Tor}^B_i(M,N)=
 B\otimes_{B\otimes_AB}\operatorname{Tor}^A_i(M,N).
$$

In particular, a common bound on the flat resolution lengths of all
$A$-modules is also such a bound for $B$-modules.

## Proof

Take free $B$-module resolutions $P\to M$, $Q\to N$, in nonnegative
homological degrees. They are flat resolutions over $A$, by the flatness
condition in [def-weil-pbc-ind-etale-algebra]. The double complex
$P\otimes_AQ$ therefore computes $\operatorname{Tor}^A(M,N)$. The two factors
give it an action of $B\otimes_AB$. Tensoring over that ring with $B$ is
exact, by the other flatness condition. It commutes with homology and
identifies the double complex with $P\otimes_BQ$, which computes the left
side. This proves the formula. The bound follows from the usual
characterization of flat dimension by vanishing of Tor.
