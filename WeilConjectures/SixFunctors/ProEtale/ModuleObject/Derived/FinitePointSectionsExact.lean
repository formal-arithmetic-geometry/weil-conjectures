/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective
import Mathlib.CategoryTheory.Abelian.Projective.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Exactness of the actual scalar sections at the geometric point
Source: latest blueprint sk-lem-finite, geometric-point identification
(blueprint: lem-sf-finite-point-sections-exact).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsSepClosed k]

/-- Exactness holds for the actual ΓΛ-valued coyoneda sections and every condensed
coefficient ring, without a constructibility assumption.

Source: latest blueprint sk-lem-finite, first paragraph; weakly contractible geometric
point (blueprint: lem-sf-finite-point-sections-exact).

Proof: the abelian tensor unit on Spec k is projective because its terminal pro-etale
object is weakly contractible. The regular coefficient module is therefore projective.
After forgetting scalars, the functor is additive coyoneda, so finite limits are
preserved by reflection through the module forgetful functor. A map out of the regular
module lifts through any epimorphism by projectivity, so scalar sections preserve
epimorphisms. An additive functor preserving kernels and epimorphisms is exact and
preserves finite colimits.
-/
theorem finite_point_sections_exact :
    PreservesFiniteLimits (condensedRingCoefficientSections Λ (Spec (.of k))) ∧
      PreservesFiniteColimits (condensedRingCoefficientSections Λ (Spec (.of k))) := by
  let F := condensedRingCoefficientSections Λ (Spec (.of k))
  have hlim : PreservesFiniteLimits F := by
    refine ⟨fun J _ _ ↦ ?_⟩
    have : PreservesLimitsOfShape J (F ⋙
        forget₂ (ModuleCat.{u + 1} (MonObj.Γ Λ)) Ab.{u + 1}) :=
      inferInstanceAs (PreservesLimitsOfShape J
        (preadditiveCoyonedaObj
          (Mod.regular (condensedRingObj Λ (Spec (.of k)))) ⋙ forget₂ _ Ab.{u + 1}))
    exact preservesLimitsOfShape_of_reflects_of_preserves F
      (forget₂ (ModuleCat.{u + 1} (MonObj.Γ Λ)) Ab.{u + 1})
  have : F.PreservesEpimorphisms := ⟨fun {M N} f hf ↦ by
    apply (ModuleCat.epi_iff_surjective (F.map f)).2
    intro x
    obtain ⟨y, hy⟩ := Projective.factors
      (show Mod.regular (condensedRingObj Λ (Spec (.of k))) ⟶ N from x) f
    exact ⟨y, hy⟩⟩
  have : F.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels F
  exact ⟨hlim, Functor.preservesFiniteColimits_of_preservesHomology F⟩

end AlgebraicGeometry.ProEtale.CondensedRing
