/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorColimits
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import WeilConjectures.Algebra.Homology.KFlatTensorConeTwoOutOfThree
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions

/-!
# Closure of K-flat complexes under countable sums and cones

## Main statements

- `CochainComplex.isKFlat_coproduct_nat`: a countable direct sum of K-flat complexes is K-flat.
- `CochainComplex.isKFlat_mappingCone`: the cone of a map of K-flat complexes is K-flat.

## References

* Stacks Project, Cohomology on Sites, Tags 06YR and 07A3
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}

private theorem acyclic_coproduct_nat
    {D : Type (u + 1)} [Category.{u} D] [Abelian D] [IsGrothendieckAbelian.{u} D]
    (L : ℕ → CochainComplex D ℤ) (hL : ∀ n, (L n).Acyclic) :
    (∐ L).Acyclic := by
  let _ : AB4OfSize.{u} D := inferInstance
  let _ : HasCoproducts.{0} D := hasCoproducts_shrink.{0, u}
  let _ : AB4OfSize.{0} D := AB4OfSize_shrink.{0, u} D
  let Z : ℕ → CochainComplex D ℤ := fun _ ↦ HomologicalComplex.zero
  let f : ∀ n, Z n ⟶ L n := fun _ ↦ 0
  have hf (n : ℕ) : QuasiIso (f n) := by
    rw [quasiIso_iff]
    intro i
    exact (quasiIsoAt_iff_exactAt (f n) i
      ((HomologicalComplex.acyclic_of_isZero _ HomologicalComplex.isZero_zero) i)).2 (hL n i)
  have hq : QuasiIso (Limits.Sigma.map f) :=
    MorphismProperty.colimMap (W := HomologicalComplex.quasiIso D (.up ℤ))
      (show Discrete.functor Z ⟶ Discrete.functor L from
        Discrete.natTrans fun n ↦ f n.as) (fun ⟨n⟩ ↦ hf n)
  have hz : IsZero (∐ Z) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply Sigma.hom_ext
    intro n
    exact HomologicalComplex.isZero_zero.eq_of_src _ _
  intro i
  exact (quasiIsoAt_iff_exactAt (Limits.Sigma.map f) i
    ((HomologicalComplex.acyclic_of_isZero _ hz) i)).1 inferInstance

set_option synthInstance.maxSize 512 in
/-- The countable direct sum of K-flat complexes of sheaves of `R`-modules is K-flat. -/
theorem isKFlat_coproduct_nat
    (K : ℕ → CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (hK : ∀ n : ℕ, (K n).IsKFlatTensor) : (∐ K).IsKFlatTensor := by
  let := SheafOfModules.monoidalCategory R
  let := (SheafOfModules.tensorClosed R).2.1.some
  let := (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions J R).1
  intro A hA
  let T := ((MonoidalCategory.curriedTensor (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ)).obj A
  have hT : ∀ n, (T.obj (K n)).Acyclic := fun n ↦ hK n A hA
  have hsum := acyclic_coproduct_nat (fun n ↦ T.obj (K n)) hT
  have e := PreservesCoproduct.iso T K
  intro i
  exact (hsum i).of_iso e.symm


/-- The mapping cone of a morphism of K-flat complexes of sheaves of `R`-modules is K-flat. -/
theorem isKFlat_mappingCone
    {K₁ K₂ : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (f : K₁ ⟶ K₂) (h₁ : K₁.IsKFlatTensor) (h₂ : K₂.IsKFlatTensor) :
    (mappingCone f).IsKFlatTensor := by
  let := SheafOfModules.monoidalCategory R
  intro A hA
  exact (SheafOfModules.tensor_mappingCone_two_out_of_three R A K₁ K₂ f hA
    |>.2.1) ⟨h₁ A hA, h₂ A hA⟩

end CochainComplex
