/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import WeilConjectures.AlgebraicGeometry.CondensedQcqsPushforwardContinuity
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeInternalHomColimits
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeHomEvaluation

/-! # Exact internal Hom and its derived sections formula -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Shifted additive Hom on strict complexes with condensed coefficients
(Hemo--Richarz--Scholbach, Lemma 5.3(2)). -/
noncomputable abbrev condensedShiftedHom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (n : ℤ) :
    CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ ⥤
        Ab.{u + 1} :=
  DerivedCategory.Q ⋙ shiftFunctor _ n ⋙ preadditiveCoyoneda.obj (op K)

/-- Derived Hom from a locally finite free module is derived sections of its exact dual tensor
(Stacks, Tag 08JJ; Hemo--Richarz--Scholbach, Lemma 5.3(2)). -/
theorem condensed_finite_free_derived_hom
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hP : IsLocallyFree (condensedRingObj Λ X) P)
    : ∃ H :
        Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
          Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
      Exists fun [_hadd : H.Additive] ↦
        PreservesFiniteLimits H ∧ PreservesFiniteColimits H ∧
        PreservesColimitsOfSize.{u + 1, u + 1} H ∧
        ∀ n : ℤ, Nonempty
          (condensedShiftedHom Λ X ((DerivedCategory.singleFunctor _ 0).obj P) n ≅
            H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙
              (condensedModuleSections Λ X).rightDerivedFunctor ⋙
                DerivedCategory.homologyFunctor _ n) := by
  let H := Mod.ihom P
  have : PreservesColimitsOfSize.{u + 1, u + 1} H :=
    condensed_locally_free_ihom_preservesColimits (condensedRingObj Λ X) P hP
  have := (Mod.ihomAdjunction P).rightAdjoint_preservesLimits
  refine ⟨H, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro n
  exact condensed_finite_free_hom_evaluation X Λ P hP n

end AlgebraicGeometry.ProEtale
