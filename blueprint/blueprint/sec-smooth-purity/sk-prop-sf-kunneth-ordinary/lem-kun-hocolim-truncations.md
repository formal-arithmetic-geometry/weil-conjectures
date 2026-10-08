+++
id = "lem-kun-hocolim-truncations"
kind = "lemma"
title = "Recovery from bounded-above truncations"
order = 1720
uses = ["def-kun-truncations", "def-weil-pbc-derived-categories", "lem-kun-complex-colimit-hocolim"]
+++
For every $E\in D(T_{\Et},\Lambda)$, the canonical morphism

$$
\operatorname{hocolim}_{N\to+\infty}\tau_{\le N}E\longrightarrow E
$$

is an isomorphism, where the homotopy colimit is that of
[def-kun-truncations].

## Proof

By [lem-kun-complex-colimit-hocolim] the homotopy colimit is
computed by the termwise colimit of the complexes
$\tau_{\le N}E$, and cohomology commutes with termwise filtered
colimits of complexes. For each fixed $q$ one has
$\mathcal H^q(\tau_{\le N}E)=\mathcal H^q(E)$ for all $N\ge q$ by
[def-kun-truncations], so
$\mathcal H^q(\operatorname{hocolim}_N\tau_{\le N}E) =\varinjlim_N\mathcal H^q(\tau_{\le N}E)=\mathcal H^q(E)$. As this
holds for every $q$, the canonical morphism is a quasi-isomorphism,
hence an isomorphism of the derived category by
[def-weil-pbc-derived-categories].
