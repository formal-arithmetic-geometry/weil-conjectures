/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineConjugateExponentsLe
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.IntegrationProjectiveExponentSquare
import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineSourceTransitionCompatibility
import all WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineCounitTensor

/-! Ordered projective and open counit transport for the coordinate line. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CoordinateLine
open AffineLinePurity VectorIntegrationSite

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] AffineLinePurity.coefficientRing
  AffineLinePurity.etaleSource AffineLinePurity.etaleCoefficient
  Scheme.finiteEtaleTateTwist Etale.ordinaryFiniteLine
  CoordinateLine.sourceCoordinates CoordinateLine.rightCoordinates
  right Etale.ordinaryFiniteP1Right
  Etale.ordinaryFiniteTwistedPullback Etale.derivedTensorRight
  Etale.ordinaryFinitePullback AffineLinePurity.ordinarySourceObject

private theorem right_comparison_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (Nr Ns : ℕ) (hr : (Nr : A) = 0) (hs : (Ns : A) = 0)
    (K : Etale.DerivedCategoryModule A T)
    (c : (Etale.ordinaryFiniteLine A Nr hr (ProjectiveLine T))⟦(2 : ℤ)⟧ ⟶
      (Etale.ordinaryFiniteLine A Ns hs (ProjectiveLine T))⟦(2 : ℤ)⟧) :
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) (AffineSpace PUnit.{u + 1} T)).obj
      ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj K)).map
        ((Etale.ordinaryFinitePullback A (ProjectiveLine.affineChart T)).map c) ≫
      (rightComparison A Ns hs T).inv.app K =
    (rightComparison A Nr hr T).inv.app K ≫
      (Etale.ordinaryFinitePullback A (ProjectiveLine.affineChart T)).map
        (((Etale.derivedTensor (ModuleCat.{u + 1} A) (ProjectiveLine T)).obj
          ((Etale.ordinaryFinitePullback A (ProjectiveLine T ↘ T)).obj K)).map c) := by
  let j := ProjectiveLine.affineChart T
  let M := (Etale.ordinaryFinitePullback A (ProjectiveLine T ↘ T)).obj K
  let η := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j
    (ProjectiveLine T ↘ T) (AffineSpace PUnit.{u + 1} T ↘ T)
    (ProjectiveLine.affineChart_over T).symm).hom.app K
  have hn := Etale.leftDerivedUpperStarTensorIso_hom_naturality_right j M c
  have hi :
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) (AffineSpace PUnit.{u + 1} T)).obj
        ((Etale.ordinaryFinitePullback A j).obj M)).map
          ((Etale.ordinaryFinitePullback A j).map c) ≫
        (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) j M _).inv =
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) j M _).inv ≫
        (Etale.ordinaryFinitePullback A j).map
          (((Etale.derivedTensor (ModuleCat.{u + 1} A) (ProjectiveLine T)).obj M).map c) := by
    apply (cancel_epi
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) j M _).hom).mp
    dsimp only [Etale.ordinaryFinitePullback] at hn ⊢
    rw [← Category.assoc, ← hn]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rw [right_comparison_inv_wrapped, right_comparison_inv_wrapped]
  have ht := ((Etale.derivedTensor (ModuleCat.{u + 1} A)
    (AffineSpace PUnit.{u + 1} T)).map η).naturality
      ((Etale.ordinaryFinitePullback A j).map c)
  dsimp only [j, M, η, line, Etale.ordinaryFinitePullback,
    Etale.affineTraceLineRight, Etale.ordinaryFiniteP1Right,
    Etale.ordinaryFiniteTwistedPullback, Etale.derivedTensorRight,
    Functor.comp_obj] at hi ht ⊢
  rw [← Category.assoc, ht, Category.assoc, hi]
  simp only [Category.assoc]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

private theorem ordered_right_counit
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (l : Γ(T, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) T) :
    (Etale.affineTraceLineLeft _ T).map
      (((Etale.derivedTensor (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
        (AffineSpace PUnit.{u + 1} T)).obj
          ((Etale.ordinaryFinitePullback _ (AffineSpace PUnit.{u + 1} T ↘ T)).obj K)).map
            ((Etale.ordinaryFinitePullback _ (ProjectiveLine.affineChart T)).map
              (integrationLineTransition l E n (ProjectiveLine T)
                (by simpa using hT.map (ProjectiveLine T ↘ T).appTop.hom)
                r s hrs hr hs).hom)) ≫
      (adjunction _ (l ^ (r + 1)) hr T (pow_pos (Fact.out : l.Prime).pos _)
        (by simpa only [Nat.cast_pow] using hT.pow (r + 1))).counit.app K =
    (adjunction _ (l ^ (s + 1)) hs T (pow_pos (Fact.out : l.Prime).pos _)
      (by simpa only [Nat.cast_pow] using hT.pow (s + 1))).counit.app K := by
  have hn := right_comparison_naturality (Scheme.finiteTateCoefficient l E n) T
    (l ^ (s + 1)) (l ^ (r + 1)) hs hr K
    (integrationLineTransition l E n (ProjectiveLine T)
      (by simpa using hT.map (ProjectiveLine T ↘ T).appTop.hom) r s hrs hr hs).hom
  unfold adjunction
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerRight_app]
  rw [← Functor.map_comp_assoc, hn, Functor.map_comp, Category.assoc]
  exact congrArg (fun f =>
    (Etale.affineTraceLineLeft (Scheme.finiteTateCoefficient l E n) T).map
      ((rightComparison (Scheme.finiteTateCoefficient l E n)
        (l ^ (s + 1)) hs T).inv.app K) ≫ f)
    (root_line_counit l E n T hT r s hrs hr hs K)

set_option maxHeartbeats 2000000 in
-- The common-exponent comparison expands the cached tensor-source coordinates.
/-- The root-power transition preserves the actual ordinary affine-line counit.
Source: the final transpose paragraph of
`cor-pur-affine-space-zero-section-purity.proof.md`
(blueprint: lem-route-coordinate-line-adjunction-counit-transition).

Proof: the normalized projective decomposition square identifies the traces after
root projection. Projection naturality gives the projective counit identity on any
complex; open-counit naturality gives the affine counit identity. Tensor/pullback
naturality transports it through rightComparison. Apply the two ordered equations
through max r r', and cancel the common-level isomorphism. The sourceCoordinates
maps merely change the endpoints, and their inverse pairs cancel. -/
theorem coordinate_line_adjunction_counit_transition
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] [IsNoetherian T]
    (r r' : ℕ)
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : Ring P) = 0)
    (Ke : Etale.DerivedCategoryModule (Ring P) T) :
    let q := coordinate_line_ordinary_source_transition P T aT r r' hA hA' Ke
    let u := (sourceCoordinates P T r hA Ke).inv ≫ q.hom ≫
      (sourceCoordinates P T r' hA' Ke).hom
    (Etale.affineTraceLineLeft (Ring P) T).map u ≫
        (adjunction (Ring P) (P.coefficients.l ^ (r' + 1)) hA' T
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
          (by simpa only [Nat.cast_pow] using (primeUnit P T aT).pow (r' + 1))).counit.app Ke =
      (adjunction (Ring P) (P.coefficients.l ^ (r + 1)) hA T
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
        (by simpa only [Nat.cast_pow] using (primeUnit P T aT).pow (r + 1))).counit.app Ke := by
  let A := Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1)
  let M := max r r'
  let hM : ((P.coefficients.l ^ (M + 1) : ℕ) : A) = 0 :=
    (Nat.cast_pow P.coefficients.l (M + 1)).trans
      (pow_eq_zero_of_le (Nat.add_le_add_right (Nat.le_max_left r r') 1)
        ((Nat.cast_pow P.coefficients.l (r + 1)).symm.trans hA))
  let F := Etale.ordinaryFinitePullback A (ProjectiveLine.affineChart T) ⋙
    (Etale.derivedTensor (ModuleCat.{u + 1} A) (AffineSpace PUnit.{u + 1} T)).obj
      ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj Ke)
  let cr := integrationLineTransition P.coefficients.l P.extension (P.level - 1)
    (ProjectiveLine T) (primeUnit P _ ((ProjectiveLine T ↘ T) ≫ aT))
    r M (Nat.le_max_left r r') hA hM
  let cs := integrationLineTransition P.coefficients.l P.extension (P.level - 1)
    (ProjectiveLine T) (primeUnit P _ ((ProjectiveLine T ↘ T) ≫ aT))
    r' M (Nat.le_max_right r r') hA' hM
  have hr := ordered_right_counit P.coefficients.l P.extension
    (P.level - 1) T (primeUnit P T aT) r M (Nat.le_max_left r r') hA hM Ke
  have hs := ordered_right_counit P.coefficients.l P.extension
    (P.level - 1) T (primeUnit P T aT) r' M (Nat.le_max_right r r') hA' hM Ke
  let L := Etale.affineTraceLineLeft A T
  have he : L.map (F.map cr.inv ≫ F.map cs.hom) ≫
      (adjunction A (P.coefficients.l ^ (r' + 1)) hA' T
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
        (by simpa only [Nat.cast_pow] using (primeUnit P T aT).pow (r' + 1))).counit.app Ke =
    (adjunction A (P.coefficients.l ^ (r + 1)) hA T
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
      (by simpa only [Nat.cast_pow] using (primeUnit P T aT).pow (r + 1))).counit.app Ke := by
    apply (cancel_epi (L.map (F.map cr.hom))).mp
    have hc : L.map (F.map cr.hom) ≫ L.map (F.map cr.inv) = 𝟙 _ := by
      rw [← L.map_comp, ← F.map_comp, Iso.hom_inv_id, F.map_id, L.map_id]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc (L.map (F.map cr.hom)) (L.map (F.map cr.inv)),
      hc, Category.id_comp]
    exact hs.trans hr.symm
  have hu := coordinate_line_source_transition_integration_compatibility
    P T aT r r' hA hA' Ke
  change L.map _ ≫ _ = _
  rw [hu]
  exact he

end AlgebraicGeometry.ProEtale.CoordinateLine
