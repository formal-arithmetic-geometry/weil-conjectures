/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TransportIntegralCounitData
import WeilConjectures.AlgebraicGeometry.CondensedIntegralEndpoints
import WeilConjectures.CategoryTheory.EquivalenceAdjunctionComparisonSupplement

/-! # Condensed realization of the integral stage

Source: purity-transport, the existing integral realization argument.
(blueprint: lem-pur-condensed-stage-realization). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCompletedTensor WeilConjectures.integralDerivedPullback

-- Keep the canonical small-site sheafification instance ahead of generic alternatives.
attribute [local instance high]
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

private theorem unit_comparison_cancel
    {C D : Type*} [Category C] [Category D] (J : C ⥤ D)
    {X Y : C} (c : X ≅ Y) {N M : D}
    (a : N ⟶ J.obj Y) (b : N ⟶ M) (r : M ⟶ J.obj X)
    (h : a ≫ J.map c.inv = b ≫ r) : b ≫ r ≫ J.map c.hom = a := by
  rw [← Category.assoc, ← h, Category.assoc, c.map_inv_hom_id J, Category.comp_id]

namespace AlgebraicGeometry.ProEtale.TransportIntegralCounit

variable (P : PurityFiniteSetting.{u}) (D : FieldShriekSystem.Models P)
  {X Z Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [(j ≫ p).IsOver (Spec (.of P.field.k))] (d : ℕ)
  [CompactSpace X] [QuasiSeparatedSpace Y]

/-- The integral tower adjunction realizes on condensed modules with its fixed counit.
Source: latest blueprint, purity-transport Steps 2--3.
(blueprint: lem-pur-condensed-stage-realization).

Proof: apply integral-models to the normalized coefficient-ring identification and
the exact section/internal equivalence. This identifies precisely Dctf with the
derived-complete integral constructible subcategory, including all morphisms.
Integral-direct-image-tower identifies the left functor with Rp_* j_! and its
reduction comparison, and identifies pullback and tensor by the specified Tate line.
Restrict those comparisons and transport the Hom bijection of integral_stage through
the two equivalences. Its unit and counit are the displayed formulas there, conjugated
by these canonical comparisons. Right-adjoint uniqueness therefore identifies this
adjunction with the specified restricted exceptional adjunction and gives
t = F(gammaT) epsilon. No Brown adjoint is replaced by an arbitrary functor. -/
theorem condensed_stage (E : FieldShriekSystem.Index P)
    (m : FieldExtensionTowers.IntegralModel P D E j p d)
    (A : Stage P D j p d E m) :
    Nonempty (CondensedStage P D j p d E m A) := by
  obtain ⟨eX, eY, ⟨nX⟩, ⟨nY⟩, hF, hJ, ⟨l⟩, ⟨r⟩⟩ :=
    condensed_integral_endpoints P D j p d E m
  let F := condensedRestriction P E
    (IntegralDirectImageTower.shriek P.coefficients.l E.val
      (SpTowerGamma.factorization j p)) hF
  let J := condensedRestriction P E (condensedSource P D j p d E m) hJ
  let left : (eX.inverse ⋙ FieldExtensionTowers.support P D j p d m) ⋙ eY.functor ≅ F :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft eX.inverse l ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eX.counitIso F ≪≫
      F.leftUnitor
  let right : eY.inverse ⋙ (FieldExtensionTowers.puritySource P D j p d m ⋙ eX.functor) ≅
      J :=
    Functor.isoWhiskerLeft eY.inverse r ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eY.counitIso J ≪≫ J.leftUnitor
  let adj : F ⊣ J :=
    (((eX.symm.toAdjunction.comp A.adjunction).comp eY.toAdjunction).ofNatIsoLeft
      left).ofNatIsoRight right
  obtain ⟨c, _, _, _, hu, hc⟩ :=
    exists_equivalenceAdjunctionComparison eX eY A.adjunction adj r
  refine ⟨{
    encodingX := eX
    encodingY := eY
    encodingX_normalized := nX
    encodingY_normalized := nY
    supportClosed := hF
    sourceClosed := hJ
    F := F
    F_eq := rfl
    J := J
    J_eq := rfl
    adjunction := adj
    supportComparison := c
    sourceComparison := r
    unitComparison := ?_
    counitComparison := fun K ↦ (hc K).symm
    fixed_counit := fun _ a K ↦ (adj.rightAdjointUniq_hom_app_counit a K).symm }⟩
  intro N
  exact unit_comparison_cancel J (c.app N) _ _ _ (hu N)


end AlgebraicGeometry.ProEtale.TransportIntegralCounit
