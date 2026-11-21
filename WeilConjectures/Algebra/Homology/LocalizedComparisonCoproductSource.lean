/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelMap
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyCofan
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyMapNaturality
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # The source coproduct for localized derived tensor comparison

## References

* Stacks Project, Tags 06Y6 and 0DJA(1)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped TensorProduct
set_option autoImplicit false
namespace ModuleCat

/-- The localized comparison of universal models is compatible with a complex coproduct. -/
theorem exists_localizedComparison_coproduct_source
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]
    {I : Type u} (M : I → CochainComplex (ModuleCat.{u} A) ℤ)
    (S : CochainComplex (ModuleCat.{u} A) ℤ) (s : ∀ j, M j ⟶ S)
    (hs : IsColimit (Cofan.mk S s))
    (m : ∀ j, BaseDerivedTensorCohomologyModel R A B (M j) C)
    (mS : BaseDerivedTensorCohomologyModel R A B S C) (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    ∃ e : (∐ fun j ↦ (extendScalars (algebraMap (A ⊗[R] B) C)).obj
        ((m j).cohomology i)) ≅
      (extendScalars (algebraMap (A ⊗[R] B) C)).obj (mS.cohomology i),
      ∀ j, Sigma.ι _ j ≫ e.hom ≫ mS.localizedComparison i =
        (m j).localizedComparison i ≫ HomologicalComplex.homologyMap (F.map (s j)) i := by
  classical
  dsimp only
  have hm (j : I) := RingTensorCohomology.exists_baseDerivedTensorCohomologyModelMap
    R A B C (M j) S (s j) (m j) mS i
  choose δ g hδ hg using hm
  obtain ⟨hc⟩ := baseDerivedTensorCohomology_canonical_cofan R A B C M S s hs m mS i
    δ g hδ hg
  let J := extendScalars.{u, u, u} (algebraMap (A ⊗[R] B) C)
  let hc' := isColimitCofanMkObjOfIsColimit J (fun j ↦ (m j).cohomology i) g hc
  let e := (coproductIsCoproduct (fun j ↦ J.obj ((m j).cohomology i))).coconePointUniqueUpToIso
    hc'
  refine ⟨e, ?_⟩
  intro j
  have he : Sigma.ι _ j ≫ e.hom = J.map (g j) :=
    (coproductIsCoproduct _).comp_coconePointUniqueUpToIso_hom hc' (Discrete.mk j)
  rw [← Category.assoc, he]
  exact baseDerivedTensorCohomologyMap_localized_naturality R A B C (M j) S (s j)
    (m j) mS i (δ j) (g j) (hδ j) (hg j)

end ModuleCat
