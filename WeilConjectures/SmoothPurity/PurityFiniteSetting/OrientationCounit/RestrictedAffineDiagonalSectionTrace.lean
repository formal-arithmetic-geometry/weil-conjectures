/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationCounit.DiagonalCounitComparisonData
public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction

/-! # Integration on the restricted affine diagonal section

Source: smooth-purity, Agreement on the model, self-product and integration paragraphs.
(blueprint: def-pur-restricted-affine-diagonal-section-trace).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
namespace OrientationCounit

/-- The self-product over an open is the ordered affine tower over its first factor.
Both sides are limits of the same cospan, so this construction chooses no frame.
Source: Agreement on the model, self-product of the affine projection
(blueprint: def-pur-restricted-affine-diagonal-section-trace). -/
def restrictedAffineDiagonalCoordinates (Y : Scheme.{u}) (d : ℕ) (V : Y.Opens) :
    pullback (affineTraceProjection Y d ∣_ V) (affineTraceProjection Y d ∣_ V) ≅
      affineTraceTower (affineTraceProjection Y d ⁻¹ᵁ V).toScheme d :=
  let p := affineTraceProjection Y d
  let h := p ∣_ V
  let sq := (IsPullback.of_hasPullback h h).flip.paste_horiz
    (isPullback_morphismRestrict p V).flip
  sq.isoIsPullback _ _ (affineTraceMap_isPullback (h ≫ V.ι) d)

/-- The coordinate identification preserves the first projection.
Source: the universal property of the same cospan
(blueprint: def-pur-restricted-affine-diagonal-section-trace). -/
theorem restrictedAffineDiagonalCoordinates_over (Y : Scheme.{u}) (d : ℕ) (V : Y.Opens) :
    (restrictedAffineDiagonalCoordinates Y d V).hom ≫
        affineTraceProjection (affineTraceProjection Y d ⁻¹ᵁ V).toScheme d =
      pullback.fst (affineTraceProjection Y d ∣_ V) (affineTraceProjection Y d ∣_ V) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- Restrict the actual affine counit mate over B to the image of the diagonal section,
then transport the section invariant back along the coordinate isomorphism. Here B is
p inverse V; the affine trace used in this construction is over B, rather than over Y.
Neither the DNC specialization nor alpha nor rho enters the construction.
Source: Agreement on the model, integration on the self-product
(blueprint: def-pur-restricted-affine-diagonal-section-trace). -/
@[irreducible]
def restrictedAffineDiagonalSectionTrace (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (d : ℕ)
    [SmoothOfRelativeDimension d (affineTraceProjection Y d)]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens)
    (H : P.AffineDiagonalGeometry (affineTraceProjection Y d) aY d V)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT) :
    P.diagonalTwist (affineTraceProjection Y d ⁻¹ᵁ V.1).toScheme d ⟶
      OrientationRefinement.source P (affineTraceProjection Y d) aY d V H := by
  letI := H.separated
  letI := H.finiteType
  letI := H.quasiCompact
  letI := H.smoothDimension
  letI := H.baseFiniteType
  letI := H.baseQuasiCompact
  letI := H.sourceSeparated
  letI := H.sourceFiniteType
  letI := H.sourceQuasiCompact
  let h := affineTraceProjection Y d ∣_ V.1
  let B := (affineTraceProjection Y d ⁻¹ᵁ V.1).toScheme
  let aB := h ≫ V.1.ι ≫ aY
  letI := P.noetherian aB
  letI := SmoothOfRelativeDimension.smooth d h
  let g := pullback.fst h h
  let s := pullback.diagonal h
  let e := restrictedAffineDiagonalCoordinates Y d V.1
  let q := affineTraceProjection B d
  letI := Dnc.compactifiable P q aB
  let r := s ≫ e.hom
  have he : e.hom ≫ q = g := restrictedAffineDiagonalCoordinates_over Y d V.1
  let sq : IsPullback e.hom g q (𝟙 B) :=
    IsPullback.of_horiz_isIso ⟨he.trans (Category.comp_id g).symm⟩
  letI : SmoothOfRelativeDimension d q :=
    (MorphismProperty.cancel_left_of_respectsIso
      (P := @SmoothOfRelativeDimension d) e.hom q).1 (by rw [he]; infer_instance)
  letI := Dnc.invertibleExponent P (q ≫ aB)
  let c := Dnc.sectionBaseChange P.Coefficient d q sq r s
    (Category.id_comp r).symm
  let m := P.diagonalAffineMate t D B (P.diagonalExponent_isUnit aB) d ≫
    (unitChange P q).inv
  exact (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.map
        ((Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t r
          (P.diagonalExponent_isUnit (q ≫ aB)) d).inv ≫
          (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) r).leftDerivedFunctor.map m ≫
          (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).inv.app _ ≫
          c.hom) ≫
    (Dnc.sourceComparison P d g aB s).inv

end OrientationCounit
end WeilConjectures.PurityFiniteSetting
