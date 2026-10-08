+++
id = "lem-sc-ga-cohomology"
kind = "lemma"
title = "Etale and Zariski cohomology agree for quasi-coherent sheaves"
order = 1003
uses = ["def-sc-curves", "def-sc-etale-qcoherent-module", "lem-pc-affine-vanishing", "lem-sc-affine-open-proper", "lem-sc-cech-spectral", "lem-sc-compactification", "lem-sc-etale-affine-qcoherent"]
+++
Let $C$ be a curve and $\mathcal F$ a
quasi-coherent module. For the
associated etale sheaf,

$$
H^q(C_{\mathrm{et}},\mathcal F_{\mathrm{et}})
\cong H^q(C_{\mathrm{Zar}},\mathcal F)\quad(q\geq0).
$$

In particular $H^q(C_{\mathrm{et}},\mathbf G_a)=H^q(C,\mathcal O_C)$,
and these groups vanish for $q\geq2$ when $C$ is a smooth connected curve.

## Proof

Take a finite affine Zariski open cover of the separated curve $C$.
Its intersections are affine. The Cech spectral sequence of
[lem-sc-cech-spectral] on the etale site has only row zero,
by [lem-sc-etale-affine-qcoherent]. The corresponding Zariski
spectral sequence also has only row zero, by
[lem-pc-affine-vanishing]. Both row-zero complexes have terms
$\Gamma(U_J,\mathcal F)$ and the same differentials, so their
cohomology groups agree naturally.

For smooth $C$, choose a compactification $\overline C$ by
[lem-sc-compactification]. Choose distinct closed points
$P,Q\in\overline C$, which exist because a positive-dimensional
variety over an algebraically closed field has infinitely many
closed points. Both $C\setminus\{P\}$ and $C\setminus\{Q\}$
are proper open subschemes of $\overline C$, hence affine by
[lem-sc-affine-open-proper]. They cover $C$, and their
intersection is affine for the same reason. The alternating
Cech complex has only degrees zero and one. Its cohomology
therefore vanishes in degrees at least two, proving the assertion.
