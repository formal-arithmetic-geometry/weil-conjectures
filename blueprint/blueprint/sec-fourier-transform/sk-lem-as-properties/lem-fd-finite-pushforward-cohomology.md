+++
id = "lem-fd-finite-pushforward-cohomology"
kind = "lemma"
title = "Cohomology of a finite pushforward"
order = 2683
uses = ["def-fd-artin-schreier-sheaf", "lem-weil-pbc-grothendieck-spectral-sequence", "lemma-weil-pbc-finite-direct-image-exact"]
+++
For a finite morphism $\pi:Y\to X_0$ and a torsion etale sheaf $\mathcal F$ on $Y$,

$$
H^q(X_0,\pi_*\mathcal F)\cong H^q(Y,\mathcal F)\qquad(q\geq0).
$$

## Proof

By [lemma-weil-pbc-finite-direct-image-exact] the functor $\pi_*$ is exact and $R^q\pi_*=0$ for $q>0$, so the Grothendieck spectral sequence of [lem-weil-pbc-grothendieck-spectral-sequence] for the composite $\Gamma\circ\pi_*$ degenerates and computes the cohomology of $\pi_*\mathcal F$ as the cohomology of $\mathcal F$; explicitly $H^q(X_0,\pi_*\mathcal F)=H^q(\Gamma\circ\pi_*\mathcal F)=H^q(\Gamma_Y\mathcal F)=H^q(Y,\mathcal F)$.
