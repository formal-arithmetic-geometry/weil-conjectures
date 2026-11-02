/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineConjugateExponentsLe
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.IntegrationExponentTransposeData

/-! Source-coordinate transport through a common finite Kummer exponent. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CoordinateLine
open AffineLinePurity VectorIntegrationSite
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] AffineLinePurity.coefficientRing
  AffineLinePurity.etaleSource AffineLinePurity.etaleCoefficient
  AffineLinePurity.ordinarySourceObject CoordinateLine.line CoordinateLine.right
  Scheme.finiteEtaleTateTwist Etale.ordinaryFiniteLine Etale.ordinaryFinitePullback
  Etale.ordinaryFiniteTwistedPullback Etale.derivedTensorRight
  Scheme.finiteEtaleTateLine Etale.ordinaryFiniteDegreeZero Etale.ordinaryFiniteSingleFunctor

private theorem native_power_comparison_eq
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) (r s : ℕ) (hrs : r ≤ s)
    (hr : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hs : ((P.coefficients.l ^ (s + 1) : ℕ) : Ring P) = 0) :
    NativeCoordinateLine.powerComparison P Y aY r s hrs hr hs =
      exponentTransition P.coefficients.l P.extension (P.level - 1) Y
        (primeUnit P Y aY) r s hrs hr hs 1 := by
  have ht := (twistCompatibility P.coefficients.l P.extension (P.level - 1)).2.2
    Y (primeUnit P Y aY) r s hrs hr hs 1
  apply ht.unique
  · exact ht.exists.choose_spec
  · simpa -implicitDefEqProofs only [exponentTransition, twistComparison] using
      ((Scheme.finite_tate_site_descent P.coefficients.l P.extension
        (P.level - 1)).choose_spec.2.2.1
          Y (primeUnit P Y aY) r s hrs hr hs 1).exists.choose_spec

set_option maxHeartbeats 2000000 in
-- Normalize the cached tensor and shift coordinate changes without a global transparency change.
/-- The native arbitrary-exponent source transition agrees with the composite of
ordered finite-site transitions through the common exponent.
Source: the root-power coordinate identification in the final paragraph of
`cor-pur-affine-space-zero-section-purity.proof.md`
(blueprint: lem-route-coordinate-line-source-transition-integration-compatibility).

Proof: unfold `sourceCoordinates`, `coordinate_line_ordinary_source_transition`,
and `integrationLineTransition`. The equality transports cancel by proof
irrelevance. The remaining shifted degree-one transition is the unique
root-power-normalized finite Tate transition at each ordered leg; uniqueness
from the finite Tate descent comparison identifies the native max-level
composite with the two ordered transitions. Functoriality of pullback and
derived tensor then gives the displayed source equality. -/
theorem coordinate_line_source_transition_integration_compatibility
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] [IsNoetherian T]
    (r r' : ℕ)
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : Ring P) = 0)
    (Ke : Etale.DerivedCategoryModule (Ring P) T) :
    let A := Ring P
    let M := max r r'
    let hM : ((P.coefficients.l ^ (M + 1) : ℕ) : A) = 0 :=
      (Nat.cast_pow P.coefficients.l (M + 1)).trans
        (pow_eq_zero_of_le (Nat.add_le_add_right (Nat.le_max_left r r') 1)
          ((Nat.cast_pow P.coefficients.l (r + 1)).symm.trans hA))
    let F := Etale.ordinaryFinitePullback A (ProjectiveLine.affineChart T) ⋙
      (Etale.derivedTensor (ModuleCat.{u + 1} A)
        (AffineSpace PUnit.{u + 1} T)).obj
        ((Etale.ordinaryFinitePullback A
          (AffineSpace PUnit.{u + 1} T ↘ T)).obj Ke)
    let cr := integrationLineTransition P.coefficients.l P.extension
      (P.level - 1) (ProjectiveLine T)
      (primeUnit P _ ((ProjectiveLine T ↘ T) ≫ aT)) r M
      (Nat.le_max_left r r') hA hM
    let cs := integrationLineTransition P.coefficients.l P.extension
      (P.level - 1) (ProjectiveLine T)
      (primeUnit P _ ((ProjectiveLine T ↘ T) ≫ aT)) r' M
      (Nat.le_max_right r r') hA' hM
    (sourceCoordinates P T r hA Ke).inv ≫
        (coordinate_line_ordinary_source_transition P T aT r r' hA hA' Ke).hom ≫
        (sourceCoordinates P T r' hA' Ke).hom = F.map cr.inv ≫ F.map cs.hom := by
  simp -implicitDefEqProofs only [sourceCoordinates, rightCoordinates,
    coordinate_line_ordinary_source_transition, NativeCoordinateLine.transition,
    integrationLineTransition, Iso.trans_hom, Iso.trans_inv, id_eq]
  dsimp only [AffineLinePurity.etaleSource, AffineLinePurity.etaleCoefficient,
    AffineLinePurity.ordinarySourceObject, CoordinateLine.line,
    Etale.ordinaryFiniteLine, AffineLinePurity.coefficientRing]
  simp -implicitDefEqProofs only [native_power_comparison_eq, Functor.comp_map,
    Functor.map_comp, Functor.mapIso_hom, Functor.mapIso_inv, eqToIso_refl,
    Etale.ordinaryFiniteDegreeZero, Scheme.finiteEtaleTateLine, Functor.comp_obj,
    Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, Iso.refl_inv,
    Category.assoc, Category.id_comp, Category.comp_id]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]

end AlgebraicGeometry.ProEtale.CoordinateLine
