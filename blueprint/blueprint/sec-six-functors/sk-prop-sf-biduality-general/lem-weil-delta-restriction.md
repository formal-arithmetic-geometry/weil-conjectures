+++
id = "lem-weil-delta-restriction"
kind = "lemma"
title = "The double-dual morphism restricts"
order = 2124
uses = ["def-weil-derived-pullback-tensor-hom", "lem-amb-etale-adjoint-locality", "lem-weil-duality-pairing"]
+++
Let $j:W\to Y$ be etale between separated finite-type schemes over
a field, with finite coefficients invertible there. For the ambient
etale dualizing objects, the canonical identifications
$j^*\omega_Y=\omega_W$ and $j^*D_Y=D_Wj^*$ identify
$j^*\delta_K$ with $\delta_{j^*K}$. Thus biduality is local
for the etale topology. The same restriction calculation applies
to the finite pro-etale realization.

## Proof

Etale locality of the ambient adjoint,
[lem-amb-etale-adjoint-locality], identifies
$j^*\omega_Y$ with $\omega_W$. Restriction to the etale
slice commutes with derived internal Hom. Indeed, its left adjoint
is exact etale extension by zero, so restriction preserves injective
resolutions, and ordinary internal Hom restricts to the internal Hom
on that slice. Applying exact monoidal restriction to the evaluation
of [lem-weil-duality-pairing] therefore gives evaluation for
$j^*K$. Transpose with the tensor–Hom adjunction of
[def-weil-derived-pullback-tensor-hom]; this gives the claimed
identity of double-dual maps. An isomorphism is detected by a covering
family. The proof is a slice-site argument and also applies on the
pro-etale realization; it does not apply to ordinary restriction
along a closed immersion.
