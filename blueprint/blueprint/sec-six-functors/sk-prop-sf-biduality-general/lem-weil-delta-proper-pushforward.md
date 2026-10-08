+++
id = "lem-weil-delta-proper-pushforward"
kind = "lemma"
title = "The double-dual morphism under a proper push-forward"
order = 2123
uses = ["lem-amb-proper-coproducts-projection", "lem-weil-duality-pairing", "prop-asd-internal-adjunction", "thm-amb-etale-exceptional-adjoint"]
+++
Let $f:X\to Y$ be a proper morphism of separated finite-type
schemes over a field, and use finite coefficients invertible there.
On the ambient etale derived categories let
$\omega_T=Ra_T^{\times}A$ and
$D_T=R\mathcal Hom_A(-,\omega_T)$. For every complex $K$,
the ambient exchange $D_YRf_*\cong Rf_*D_X$ identifies
$Rf_*\delta_K$ with $\delta_{Rf_*K}$. In particular, if the
latter is an isomorphism then so is the former.
Neither exceptional-adjoint admissibility on a constructible
subcategory nor geometric biduality is assumed.

## Proof

Composition of the ambient right adjoints of
[thm-amb-etale-exceptional-adjoint] gives
$f^{\times}\omega_Y=\omega_X$. As $f$ is proper,
$Rf_!=Rf_*$; the ambient internal adjunction of
[prop-asd-internal-adjunction], valid for arbitrary complexes,
therefore gives $D_YRf_*\cong Rf_*D_X$.

Push forward the evaluation of [lem-weil-duality-pairing] and
compose with the projection morphism of
[lem-amb-proper-coproducts-projection] and the exceptional counit.
The resulting pairing is

$$
Rf_*K\otimes_A^LRf_*D_XK
\longrightarrow Rf_*(K\otimes_A^LD_XK)
\longrightarrow Rf_*\omega_X\longrightarrow\omega_Y.
$$

The isomorphism of [prop-asd-internal-adjunction] is exactly the
adjoint of this pairing. Transpose evaluation twice. Its first
transpose is the double-dual arrow by definition, while its second
transpose is evaluation for the dual precomposed with that arrow.
Tensor symmetry includes its Koszul signs. Naturality of the
projection morphism and counit therefore identifies the two
transposes after push-forward with the same transposes of the
displayed pairing. Equivalently, the canonical composite

$$
Rf_*D_XD_XK\cong D_YRf_*D_XK
\cong D_YD_YRf_*K
$$

carries $Rf_*\delta_K$ to $\delta_{Rf_*K}$. Both comparison
maps are isomorphisms independently of biduality, proving the last
assertion as well.
