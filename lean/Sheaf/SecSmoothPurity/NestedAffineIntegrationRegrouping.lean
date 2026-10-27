module

public import Sheaf.SecSmoothPurity.NestedAffineFormulaData

/-! # Regrouping ordered affine integration in ordinary coordinates

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/sk-prop-sp-composition-factors.proof.md, proof (1).
(blueprint: lem-sp-nested-affine-integration-regrouping).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.NestedAffine

/-- Regrouping ordered affine integration in ordinary coordinates.

Source: composition-factors proof (1).
(blueprint: lem-sp-nested-affine-integration-regrouping).

Proof:
1. If both ranks are positive, use affineSpacePurityComposition with the
   coefficient unit and its canonical ordinary finite-Tor presentation. Transport
   its tower through blockEq and blockProjection; the comparison is the canonical
   one because both exceptional compositors are adjunction conjugates of the
   same compact-support compositor.
2. The finite-site comparison preserves pullback, tensor, the normalized trace
   and exceptional adjunction transposes. Consequently its images of total and
   iterated are exactly the two arrows of that composition equation. Cancel the
   comparison isomorphisms and reflect equality by full faithfulness.
3. If either rank is zero, use orderedAdjointTower_regrouping with a repeated
   endpoint. The empty tower has the identity adjunction and identity comparison;
   source and target unit constraints cancel by the triangle identities. If both
   ranks are zero this is the same identity equation. No nonempty-scheme
   assumption is used, and the coordinate order is always the d-block then e-block.
-/
theorem nested_affine_integration_regrouping (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (d e : ℕ) (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    letI := P.noetherian aB
    total P B aB d e N = iterated P B aB d e := by sorry

end WeilConjectures.PurityFiniteSetting.NestedAffine
