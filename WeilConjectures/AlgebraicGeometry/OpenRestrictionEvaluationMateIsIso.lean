/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.OpenExtensionProjectionFormula

/-! # Invertibility of the mixed-universe open-restriction evaluation mate

## References

* Stacks Project, Tags 08DJ, 08DL, 08BS and 01AK.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Use the standard localization on the open scheme. (Stacks, Tag 05RU) -/
local instance openRestrictionMateStandardDerived (X : Scheme.{u}) (U : X.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
  HasDerivedCategory.standard _

private theorem mate_isIso_of_projection
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (H : Cᵒᵖ × C ⥤ C) (HU : Dᵒᵖ × D ⥤ D) (R : C ⥤ D) [R.Monoidal]
    (J : D ⥤ C) (adj : J ⊣ R)
    (e : ∀ A K N : C, (A ⟶ H.obj (op K, N)) ≃ (A ⊗ K ⟶ N))
    (eU : ∀ A K N : D, (A ⟶ HU.obj (op K, N)) ≃ (A ⊗ K ⟶ N))
    (hx : ∀ A A' K N (a : A' ⟶ A) (f : A ⟶ H.obj (op K, N)),
      e A' K N (a ≫ f) = (a ⊗ₘ 𝟙 K) ≫ e A K N f)
    (hu : ∀ A A' K N (a : A' ⟶ A) (f : A ⟶ HU.obj (op K, N)),
      eU A' K N (a ≫ f) = (a ⊗ₘ 𝟙 K) ≫ eU A K N f)
    (K N : C)
    (p : ∀ A : D, J.obj (A ⊗ R.obj K) ≅ J.obj A ⊗ K)
    (hp : ∀ A : D, adj.unit.app (A ⊗ R.obj K) ≫ R.map (p A).hom =
      (adj.unit.app A ⊗ₘ 𝟙 (R.obj K)) ≫ (Functor.Monoidal.μIso R (J.obj A) K).hom) :
    IsIso ((eU (R.obj (H.obj (op K, N))) (R.obj K) (R.obj N)).symm
      ((Functor.Monoidal.μIso R (H.obj (op K, N)) K).hom ≫
        R.map (e (H.obj (op K, N)) K N (𝟙 _)))) := by
  let c := (eU (R.obj (H.obj (op K, N))) (R.obj K) (R.obj N)).symm
    ((Functor.Monoidal.μIso R (H.obj (op K, N)) K).hom ≫
      R.map (e (H.obj (op K, N)) K N (𝟙 _)))
  apply isIso_of_yoneda_map_bijective c
  intro A
  let pe : (J.obj A ⊗ K ⟶ N) ≃ (J.obj (A ⊗ R.obj K) ⟶ N) :=
    { toFun := fun f ↦ (p A).hom ≫ f
      invFun := fun f ↦ (p A).inv ≫ f
      left_inv := by intro f; simp
      right_inv := by intro f; simp }
  let b := (adj.homEquiv A (H.obj (op K, N))).symm |>.trans (e (J.obj A) K N)
    |>.trans pe |>.trans (adj.homEquiv (A ⊗ R.obj K) N)
    |>.trans (eU A (R.obj K) (R.obj N)).symm
  have hb (f : A ⟶ R.obj (H.obj (op K, N))) : b f = f ≫ c := by
    apply (eU A (R.obj K) (R.obj N)).injective
    dsimp only [b, Equiv.trans_apply]
    rw [Equiv.apply_symm_apply]
    change (adj.homEquiv (A ⊗ R.obj K) N)
      ((p A).hom ≫ e (J.obj A) K N ((adj.homEquiv A _).symm f)) =
      eU A (R.obj K) (R.obj N) (f ≫ c)
    rw [adj.homEquiv_unit, R.map_comp, ← Category.assoc, hp]
    have hx' := hx (H.obj (op K, N)) (J.obj A) K N
      ((adj.homEquiv A _).symm f) (𝟙 _)
    simp only [Category.comp_id] at hx'
    rw [hx', R.map_comp, Category.assoc]
    have hn := Functor.LaxMonoidal.μ_natural R ((adj.homEquiv A _).symm f) (𝟙 K)
    rw [R.map_id] at hn
    change (R.map ((adj.homEquiv A _).symm f) ⊗ₘ 𝟙 (R.obj K)) ≫
      (Functor.Monoidal.μIso R (H.obj (op K, N)) K).hom =
      (Functor.Monoidal.μIso R (J.obj A) K).hom ≫
        R.map ((adj.homEquiv A _).symm f ⊗ₘ 𝟙 K) at hn
    rw [← reassoc_of% hn, ← Category.assoc, tensorHom_comp_tensorHom]
    have hf : adj.unit.app A ≫ R.map ((adj.homEquiv A _).symm f) = f := by
      have h := (adj.homEquiv A (H.obj (op K, N))).apply_symm_apply f
      rw [adj.homEquiv_unit] at h
      exact h
    rw [hf, Category.id_comp, hu]
    simp only [c, Equiv.apply_symm_apply]
  have heq : (fun f : A ⟶ R.obj (H.obj (op K, N)) ↦ f ≫ c) = b := by
    funext f
    exact (hb f).symm
  change Function.Bijective (fun f : A ⟶ R.obj (H.obj (op K, N)) ↦ f ≫ c)
  rw [heq]
  exact b.bijective

set_option maxHeartbeats 1000000 in
-- The canonical-family predicate unfolds the recorded sheaf tensor instances.
set_option linter.style.haveILetI false in
/-- The mate of restricted evaluation is invertible for any strong monoidal
structure on the exact restriction functor, with independently specified localizations. -/
theorem openRestriction_evaluationMate_isIso (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory ⋙ E
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace) X.sheaf
    ∀ m : R.Monoidal,
      letI := m
      ∀ K N : schemeDerivedCategory X,
        IsIso ((schemeDerivedTensorHomEquiv U.toScheme
          (R.obj (H.obj (op K, N))) (R.obj K) (R.obj N)).symm
            ((Functor.Monoidal.μIso R (H.obj (op K, N)) K).hom ≫
              R.map (schemeDerivedTensorHomEquiv X (H.obj (op K, N)) K N (𝟙 _)))) := by
  classical
  dsimp only
  let E := (Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv U)).mapDerivedCategory
  let R := (SheafOfModules.overFunctor.{u}
    (moduleRings X.toRingedSpace) U).mapDerivedCategory ⋙ E
  let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace) X.sheaf
  let HU := derivedInternalHom
    (Opens.grothendieckTopology U.toScheme.toRingedSpace) U.toScheme.sheaf
  let e := schemeDerivedTensorHomEquiv X
  let eU := schemeDerivedTensorHomEquiv U.toScheme
  have he : IsCanonicalDerivedTensorHom X e :=
    Classical.choose_spec (exists_canonicalDerivedTensorHom X)
  have heU : IsCanonicalDerivedTensorHom U.toScheme eU :=
    Classical.choose_spec (exists_canonicalDerivedTensorHom U.toScheme)
  intro m K N
  letI : R.Monoidal := m
  obtain ⟨J, adj, hp⟩ := exists_openExtension_projectionFormula X U m
  have hi (A : schemeDerivedCategory U.toScheme) :
      IsIso ((adj.homEquiv (A ⊗ R.obj K) (J.obj A ⊗ K)).symm
        ((adj.unit.app A ⊗ₘ 𝟙 (R.obj K)) ≫
          (Functor.Monoidal.μIso R (J.obj A) K).hom)) := hp A K
  let p := fun A ↦ asIso ((adj.homEquiv (A ⊗ R.obj K) (J.obj A ⊗ K)).symm
    ((adj.unit.app A ⊗ₘ 𝟙 (R.obj K)) ≫
      (Functor.Monoidal.μIso R (J.obj A) K).hom))
  apply mate_isIso_of_projection H HU R J adj e eU ?_ ?_ K N p ?_
  · intro B B' L M a f
    have hn := he.1 B B' L L M M a (𝟙 L) (𝟙 M) f
    change e B' L M (a ≫ f ≫ H.map (𝟙 (op L, M))) = _ at hn
    simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using hn
  · intro B B' L M a f
    have hn := heU.1 B B' L L M M a (𝟙 L) (𝟙 M) f
    change eU B' L M (a ≫ f ≫ HU.map (𝟙 (op L, M))) = _ at hn
    simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using hn
  · intro A
    have h := (adj.homEquiv (A ⊗ R.obj K) (J.obj A ⊗ K)).apply_symm_apply
      ((adj.unit.app A ⊗ₘ 𝟙 (R.obj K)) ≫
        (Functor.Monoidal.μIso R (J.obj A) K).hom)
    rw [adj.homEquiv_unit] at h
    exact h

end AlgebraicGeometry
