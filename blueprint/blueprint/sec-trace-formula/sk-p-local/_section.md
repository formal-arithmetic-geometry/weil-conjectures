+++
id = "sk-p-local"
kind = "section"
title = "Decomposition into local terms"
order = 2347
uses = ["sk-d-corr", "sk-d-integral", "sk-d-local-term", "sk-d-pairing", "sk-p-pairing", "sk-thm-sf-package"]
lean = ["AlgebraicGeometry.ProEtale.GeometricOperations.integral_eq_sum_localTerm"]
+++
*Proposition (sketch).*

Suppose the intersection support of an opposite pair is
a finite disjoint union $E=\coprod_{\beta\in B}\beta$ of clopen
subschemes, each proper over $s$. Then integration
of the pairing is the sum of its
local terms:

$$
\int_E\langle u,v\rangle_{\mathrm{LV}}
=\sum_{\beta\in B}\LT_\beta(u,v).
$$

## Proof

First $E$ is proper: after any base change, the image of a closed set
is the finite union of its closed images from the proper pieces.
Each $j_\beta$ is both open and closed, so
[sk-thm-sf-package] identifies $Rj_{\beta!}=Rj_{\beta*}$ and
$j_\beta^!=j_\beta^*$.
For $L=A_E,\omega_E$ define the two specified maps

$$
R_L:\bigoplus_\beta Rj_{\beta*}j_\beta^*L\longrightarrow L,
\qquad S_L:L\longrightarrow\bigoplus_\beta Rj_{\beta*}j_\beta^*L
$$

by exceptional counits and ordinary units, respectively.
Base change gives $j_\gamma^*Rj_{\beta*}=0$ for
$\beta\ne\gamma$ and the identity for $\beta=\gamma$.
Thus $R_L$ is an isomorphism by local detection. To identify its
inverse, take the ordinary $j_\gamma$-adjoint of each matrix entry
of $S_LR_L$. Off the diagonal its source is zero; on the diagonal
the triangle identity and open-counit compatibility make it the
transpose of the identity. Hence $S_L=R_L^{-1}$.

Let $\alpha=\langle u,v\rangle_{\mathrm{LV}}$ from [sk-d-pairing].
Naturality of the counits and the finite biproduct identity now give

$$
\alpha=R_{\omega_E}\Bigl(\bigoplus_\beta Rj_{\beta*}(\alpha|_\beta)\Bigr)S_{A_E}
=\sum_\beta(j_\beta)_*(\alpha|_\beta).
$$

The last pushforwards are precisely those in [sk-d-integral];
this proves an equality of global morphisms, not merely equality
after open restriction.

Integration in [sk-d-integral] is additive, since direct image
is additive and composition is bilinear. Moreover, for proper
$h:T\to T'$ between proper schemes, the identities

$$
\eta_{a_{T'}h}^*=Ra_{T'*}\eta_h^*\,\eta_{a_{T'}}^*,\qquad
\varepsilon_{a_{T'}h}^!=\varepsilon_{a_{T'}}^!\,Ra_{T'!}\varepsilon_h^!
$$

from [sk-thm-sf-package] give $\int_{T'}h_*\gamma=\int_T\gamma$.
Consequently

$$
\int_E\alpha=\sum_\beta\int_E(j_\beta)_*(\alpha|_\beta)
=\sum_\beta\int_\beta\alpha|_\beta
=\sum_\beta\LT_\beta(u,v)
$$

by [sk-d-local-term]. Empty support gives the empty sum $0$.
For $s$, its structure map and the inclusion of its sole component
are identities. Both integration adjunction maps are identities,
so the normalization of [sk-p-pairing] also gives
$\LT_s(w)=\tr_A(w)$ for a perfect complex.

Uses: [sk-d-corr], [sk-d-integral], [sk-d-local-term], [sk-d-pairing], [sk-p-pairing], [sk-thm-sf-package]
