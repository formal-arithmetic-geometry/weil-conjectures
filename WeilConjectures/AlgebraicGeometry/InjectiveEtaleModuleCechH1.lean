/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import WeilConjectures.AlgebraicGeometry.InjectiveEtaleConstantRingModule
import WeilConjectures.CategoryTheory.SiteCechMathlibComparison
import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Degree-one Čech acyclicity of injective étale module sheaves

## References

* Stacks Project, Cohomology on Sites, Lemmas 03FC and 03FD.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- The underlying abelian presheaf of an injective module sheaf has vanishing Čech H¹
on every étale covering, including coverings with an infinite index set.
(Stacks, Tags 03FC, 03FD.) -/
theorem isZero_cech_H_one_of_injective_module_sheaf
    (Y : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J]
    (U : Y.Etale) {I : Type (u + 1)} (V : I → Y.Etale) (f : ∀ i : I, V i ⟶ U)
    (hcover : Sieve.ofArrows V f ∈ Y.smallEtaleTopology U) :
    IsZero (((cechComplexFunctor fun i : I ↦ Over.mk (f i)).obj
      ((Over.forget U).op ⋙ ((sheafCompose Y.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj J).obj)).homology 1) := by
  classical
  let K := Y.smallEtaleTopology.toPrecoverage
  have htop : K.toGrothendieck = Y.smallEtaleTopology := by
    apply le_antisymm
    · exact Y.smallEtaleTopology.toGrothendieck_toPrecoverage_le
    · intro W R hR
      have h : R.arrows ∈ K W :=
        (Y.smallEtaleTopology.arrows_mem_toPrecoverage_iff R).2 hR
      simpa using K.generate_mem_toGrothendieck h
  have hc : Presieve.ofArrows V f ∈ K U := hcover
  obtain ⟨S⟩ := SiteCechComplex.exists_of_covering K hc
  obtain ⟨R, M, hM, ⟨e⟩⟩ := exists_injective_etale_ring_module Y Λ J
  have : HasSheafify K.toGrothendieck AddCommGrpCat.{u + 1} := by
    rw [htop]
    infer_instance
  have : K.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{u + 1} := by
    rw [htop]
    infer_instance
  have vanish : ∀ (R : Sheaf Y.smallEtaleTopology RingCat.{u + 1})
      (M : SheafOfModules.{u + 1} R), Injective M →
        IsZero ((S.cohomologyFunctor 1).obj M.val.presheaf) := by
    rw [← htop]
    intro R M hM
    have : Injective M := hM
    have : Injective M.val := injective_module_sheaf_injective_presheaf R M
    let q : ℕ := 0
    change IsZero ((S.complex M.val.presheaf).homology (q + 1))
    apply HomologicalComplex.ExactAt.isZero_homology
    apply (HomologicalComplex.exactAt_iff' (S.complex M.val.presheaf)
      q (q + 1) (q + 2) (by simp) (by simp)).2
    rw [ShortComplex.ab_exact_iff]
    intro c hc
    change (CochainComplex.of.d (S.cochains M.val.presheaf)
      (S.differential M.val.presheaf) (q + 1) ((q + 1) + 1)) c = 0 at hc
    rw [CochainComplex.of_d] at hc
    obtain ⟨b, hb⟩ := injective_presheaf_module_cech_cocycle_lift_max.{u + 1, u, u + 1}
      R.obj M.val V f S q c hc
    refine ⟨b, ?_⟩
    change (CochainComplex.of.d (S.cochains M.val.presheaf)
      (S.differential M.val.presheaf) q (q + 1)) b = c
    rw [CochainComplex.of_d]
    exact hb
  have hz := vanish R M hM
  have hz' : IsZero ((S.cohomologyFunctor 1).obj
      (J.obj ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) :=
    hz.of_iso ((S.cohomologyFunctor 1).mapIso e.symm)
  obtain ⟨c⟩ := S.mathlib_complex_iso_exists V f
    (J.obj ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  exact hz'.of_iso ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) 1).mapIso c.symm)


end AlgebraicGeometry.Scheme
