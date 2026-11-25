/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.InternalCompletionSectionTransport
import all WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
import WeilConjectures.SixFunctors.ProEtale.InternalKoszulQuotientResolution
import WeilConjectures.SixFunctors.ProEtale.InternalQuotientRoosLimit

/-! # Normalized quotient to Koszul augmentation comparison

## References

* [Stacks, Tag 099I](https://stacks.math.columbia.edu/tag/099I)
* [Stacks, Tag 099L](https://stacks.math.columbia.edu/tag/099L)
* [Stacks, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks, Tag 099M](https://stacks.math.columbia.edu/tag/099M)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.InternalCompletionTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

local instance internalQuotientKoszulUnitComparisonInst1
    : HasDerivedCategory (ConstantCompletion.Mod (ring l E X)) :=
  HasDerivedCategory.standard _
local instance internalQuotientKoszulUnitComparisonInst2
    : HasDerivedCategory (ℕᵒᵖ ⥤ ConstantCompletion.Mod (ring l E X)) :=
  HasDerivedCategory.standard _

/-- Comparison of augmented actual quotient Roos complexes with the singleton
Koszul completion, after the specified exact constant-coefficient transport. -/
theorem quotient_koszul_unit_comparison [IsNoetherian X]
    (a : ((ring l E X).obj ⋙ forget CommRingCat).sections)
    (ha : ∀ U : Scheme.coefficientProEtaleSiteModel.{u, u} X,
      IsRingedIdealGeneratingList (ring l E X)
        (ConstantCompletion.kernelIdeal (residue l E X)).module
        (ConstantCompletion.kernelIdeal (residue l E X)).inclusion U 1
        (fun _ ↦ a.val (op U)))
    (P : CochainComplex (AdicCompletion.Modules l E X) ℤ)
    (hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E X) (.up ℤ)).kFlat P)
    (D : RingedKoszulLimitPresentation (ring l E X) 1 (fun _ ↦ a)) :
    ∃ e : (functor l E X).obj (DerivedCategory.Q.obj (AdicCompletion.roos l E X P)) ≅
        D.completion.obj ((functor l E X).obj (DerivedCategory.Q.obj P)),
      (functor l E X).map (DerivedCategory.Q.map (AdicCompletion.augmentation l E X P)) ≫
        e.hom = D.unit ((functor l E X).obj (DerivedCategory.Q.obj P)) := by
  obtain ⟨q, hq, hu⟩ := koszul_quotient_resolution l E X a ha P hP
  obtain ⟨e, he⟩ := quotient_roos_limit l E X P D.inverseLimit D.comparison
    D.isRightDerived D.comparison_isIso
  let N := complex l E X P
  let t := complexIso l E X P
  have : QuasiIso q := hq
  let b : D.completion.obj ((functor l E X).obj (DerivedCategory.Q.obj P)) ≅
      D.inverseLimit.obj (DerivedCategory.Q.obj (quotientComplex l E X P)) :=
    D.completion.mapIso t ≪≫
      D.inverseLimit.mapIso (D.tensorFactors.app N) ≪≫
      D.inverseLimit.mapIso (asIso (DerivedCategory.Q.map q))
  have hb : D.unit ((functor l E X).obj (DerivedCategory.Q.obj P)) ≫ b.hom =
      (functor l E X).map (DerivedCategory.Q.map (AdicCompletion.augmentation l E X P)) ≫
        e.hom := by
    rw [he]
    dsimp only [b, N, t, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
    rw [← Category.assoc, ← Category.assoc,
      ← CategoryTheory.FlatScalarKoszul.unit_naturality (ring l E X) D t.hom,
      CategoryTheory.FlatScalarKoszul.unit_app_Q]
    dsimp only [RingedKoszulLimitPresentation.unitOnComplex]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Category.id_comp]
    have hn := D.comparison.naturality q
    dsimp only [Functor.comp_map] at hn
    rw [← hn]
    simp only [← Functor.map_comp, ← Category.assoc]
    rw [hu]
  refine ⟨e ≪≫ b.symm, ?_⟩
  change _ ≫ (e.hom ≫ b.inv) = _
  rw [← Category.assoc, ← hb, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.ProEtale.InternalCompletionTransport
