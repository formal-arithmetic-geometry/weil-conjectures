module

public import Sheaf.Paper.AffineDiagonalIntegrationConstructions

/-! # Affine diagonal integration translation split -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- This is a strictly smaller component of the translation comparison for affine diagonal
coordinates. It is one conjunct of the parent theorem.
Source: Agreement on the model, translation clause
(blueprint: lem-pur-affine-diagonal-integration-translation-integration).
The proof is the compact-support exchange and normalized Tate transport for the
tautological translation, followed by the coordinate comparison. -/
theorem affineDiagonalIntegration_translation_integration (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : P.Coefficient) = 0) :
    let p := affineDiagonalProjection Y d
    let aX := p ≫ aY
    let p₁ := pullback.fst p p
    letI := affineDiagonalProjection_smooth Y d
    letI := SmoothOfRelativeDimension.smooth d p
    letI := Dnc.compactifiable P p₁ aX
    letI := (affineDiagonalProductCoordinates_spec Y d).1
    letI := (affineDiagonalTranslatedCoordinates_spec Y d).1
    let e := asIso (affineDiagonalProductCoordinates Y d)
    let h := asIso (affineDiagonalTranslatedCoordinates Y d)
    let he := (affineDiagonalProductCoordinates_spec Y d).2
    let hh := (affineDiagonalTranslatedCoordinates_spec Y d).2.1
    P.affineDiagonalPresentedIntegration d p₁ aX r hA e he =
        P.affineDiagonalPresentedIntegration d p₁ aX r hA h hh := by
  sorry

end WeilConjectures.PurityFiniteSetting
