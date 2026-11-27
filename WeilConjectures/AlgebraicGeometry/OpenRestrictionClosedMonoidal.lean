/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom

import WeilConjectures.AlgebraicGeometry.OpenRestrictionDerivedMonoidal
import WeilConjectures.AlgebraicGeometry.OpenRestrictionEvaluationMateIsIso

/-! # Closed monoidal comparisons for open restriction

## References

* Stacks Project, Tags 08DJ and 08DL.
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

/-- The standard localization is available on the open scheme independently of the
specified localization universe of the over-site. (Stacks, Tag 05RU) -/
local instance closedRestrictionStandardDerived (X : Scheme.{u}) (U : X.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
  HasDerivedCategory.standard _

private theorem monoidal_restriction_mate_equation
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (H : Cᵒᵖ × C ⥤ C) (J : Dᵒᵖ × D ⥤ D) (R : C ⥤ D) [R.Monoidal]
    (e : ∀ A K N : C, (A ⟶ H.obj (op K, N)) ≃ (A ⊗ K ⟶ N))
    (eU : ∀ A K N : D, (A ⟶ J.obj (op K, N)) ≃ (A ⊗ K ⟶ N))
    (hx : ∀ A A' K N (a : A' ⟶ A) (f : A ⟶ H.obj (op K, N)),
      e A' K N (a ≫ f) = (a ⊗ₘ 𝟙 K) ≫ e A K N f)
    (hu : ∀ A A' K N (a : A' ⟶ A) (f : A ⟶ J.obj (op K, N)),
      eU A' K N (a ≫ f) = (a ⊗ₘ 𝟙 K) ≫ eU A K N f)
    (A K N : C) (ξ : A ⟶ H.obj (op K, N)) :
    eU (R.obj A) (R.obj K) (R.obj N)
      (R.map ξ ≫ (eU (R.obj (H.obj (op K, N))) (R.obj K) (R.obj N)).symm
        ((Functor.Monoidal.μIso R (H.obj (op K, N)) K).hom ≫
          R.map (e (H.obj (op K, N)) K N (𝟙 _)))) =
      (Functor.Monoidal.μIso R A K).hom ≫ R.map (e A K N ξ) := by
  rw [hu, Equiv.apply_symm_apply]
  have hn := Functor.LaxMonoidal.μ_natural R ξ (𝟙 K)
  rw [R.map_id] at hn
  change (R.map ξ ⊗ₘ 𝟙 (R.obj K)) ≫
    (Functor.Monoidal.μIso R (H.obj (op K, N)) K).hom =
    (Functor.Monoidal.μIso R A K).hom ≫ R.map (ξ ⊗ₘ 𝟙 K) at hn
  rw [← Category.assoc, hn, Category.assoc, ← R.map_comp]
  have h := hx (H.obj (op K, N)) A K N ξ (𝟙 _)
  simpa only [Category.comp_id] using congrArg
    (fun f ↦ (Functor.Monoidal.μIso R A K).hom ≫ R.map f) h.symm

private theorem closedRestriction_tensorHomEquiv_comp (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (A A' K N : schemeDerivedCategory X) (a : A' ⟶ A)
    (f : A ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.sheaf).obj (op K, N)) :
    schemeDerivedTensorHomEquiv X A' K N (a ≫ f) =
      (a ⊗ₘ 𝟙 K) ≫ schemeDerivedTensorHomEquiv X A K N f := by
  have hn := (Classical.choose_spec (exists_canonicalDerivedTensorHom X)).1
    A A' K K N N a (𝟙 K) (𝟙 N) f
  change schemeDerivedTensorHomEquiv X A' K N
    (a ≫ f ≫ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.sheaf).map (𝟙 (op K, N))) =
    (a ⊗ₘ 𝟙 K) ≫ schemeDerivedTensorHomEquiv X A K N f ≫ 𝟙 N at hn
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using hn

/-- Exact restriction carries compatible strong tensor and internal-Hom comparisons.
(Stacks, Tags 06YH, 08DJ and 08DL) No evaluation map is asserted to be invertible. -/
theorem exists_openRestriction_closedMonoidal (X : Scheme.{u})
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
    let HU := derivedInternalHom
      (Opens.grothendieckTopology U.toScheme.toRingedSpace) U.toScheme.sheaf
    ∃ m : R.Monoidal,
      letI := m
      ∃ h : ∀ K N : schemeDerivedCategory X,
        R.obj (H.obj (op K, N)) ≅ HU.obj (op (R.obj K), R.obj N),
        ∀ A K N (ξ : A ⟶ H.obj (op K, N)),
          schemeDerivedTensorHomEquiv U.toScheme (R.obj A) (R.obj K) (R.obj N)
            (R.map ξ ≫ (h K N).hom) =
          (Functor.Monoidal.μIso R A K).hom ≫
            R.map (schemeDerivedTensorHomEquiv X A K N ξ) := by
  classical
  -- Reuse the functors in the statement instead of elaborating their instances again.
  intro E R H HU
  let e := schemeDerivedTensorHomEquiv X
  let eU := schemeDerivedTensorHomEquiv U.toScheme
  -- Choose the local instance directly, avoiding a dependent elimination over this context.
  let m : R.Monoidal := Classical.choice (exists_openRestriction_derivedMonoidal X U)
  let c := fun K N ↦ (eU (R.obj (H.obj (op K, N))) (R.obj K) (R.obj N)).symm
    ((Functor.Monoidal.μIso R (H.obj (op K, N)) K).hom ≫
      R.map (e (H.obj (op K, N)) K N (𝟙 _)))
  have hc (K N : schemeDerivedCategory X) : IsIso (c K N) :=
    openRestriction_evaluationMate_isIso X U m K N
  let h := fun K N ↦ asIso (c K N)
  refine ⟨m, h, ?_⟩
  intro A K N ξ
  change eU (R.obj A) (R.obj K) (R.obj N) (R.map ξ ≫ c K N) =
    (Functor.Monoidal.μIso R A K).hom ≫ R.map (e A K N ξ)
  exact monoidal_restriction_mate_equation H HU R e eU
    (closedRestriction_tensorHomEquiv_comp X)
    (closedRestriction_tensorHomEquiv_comp U.toScheme) A K N ξ

end AlgebraicGeometry
