/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.AlgebraicGeometry.CondensedStratumModelInductionStepEmpty
import WeilConjectures.AlgebraicGeometry.CondensedStratumModelInductionStepNonempty

/-!
# One support-induction step for finite coefficient models

Source: upstream `ModuleObject/Colimit/TwoColimit.lean`, `(Obj)` descent paragraph,
with the open-closed and extension-class argument recorded in
`lem-weil-pbc-condensed-stratum-model-assembly`. The induction hypothesis is an explicit
input here; the caller carries out the well-founded induction.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- One geometric step assembling a model from the strictly smaller closed supports.

Source: upstream `ModuleObject/Colimit/TwoColimit.lean`, `(Obj)` descent paragraph;
Stacks Project, Tags 09AH and 09AA for open-closed localization, including the
empty-complement case. This is the induction step of the assembly node, not an
unconditional assertion of the assembly theorem on every closed subscheme. -/
theorem exists_finiteCoefficient_model_on_closed_support_step
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (padicAlgClRingObj T ℓ))
    (S : Scheme.Stratification T)
    (hS : ∀ a : Fin S.n,
      ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
        (M_E : Mod (Sheaf (Scheme.ProEt.topology (S.domain a)) Ab.{u + 1})
          ((upperStar Ab.{u + 1} (S.immersion a)).obj (padicSubfieldRingObj T ℓ E))),
        IsLocallyFinitelyPresented
          ((upperStar Ab.{u + 1} (S.immersion a)).obj (padicSubfieldRingObj T ℓ E)) M_E ∧
        Nonempty ((Mod.extendScalars ((upperStar Ab.{u + 1} (S.immersion a)).map
          (padicSubfieldRingObjToPadicAlgCl T ℓ E))).obj M_E ≅
            (((upperStar Ab.{u + 1} (S.immersion a)).mapMod
              (padicAlgClRingObj T ℓ)).obj M))) :
    ∀ (D : TopologicalSpace.Closeds T),
      (∀ (D' : TopologicalSpace.Closeds T), D' < D →
        ∀ (Y : Scheme.{u}) (i : Y ⟶ T) [IsClosedImmersion i], Set.range i ⊆ D' →
          ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
            (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
              (padicSubfieldRingObj Y ℓ E)),
            IsConstructibleModuleObject (padicSubfieldRingObj Y ℓ E) P ∧
            Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Y ℓ E)).obj P ≅
              (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) i).obj M)) →
      ∀ (Y : Scheme.{u}) (i : Y ⟶ T) [IsClosedImmersion i], Set.range i ⊆ D →
      ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
        (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (padicSubfieldRingObj Y ℓ E)),
        IsConstructibleModuleObject (padicSubfieldRingObj Y ℓ E) P ∧
        Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Y ℓ E)).obj P ≅
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) i).obj M)  := by
  intro D hD Y i hI hYi
  by_cases hY : Nonempty Y
  · exact @exists_finiteCoefficient_model_on_closed_support_step_nonempty
      T _ ℓ _ M S hS D hD Y i hI hY hYi
  · let hE : IsEmpty Y := ⟨fun y ↦ hY ⟨y⟩⟩
    exact @exists_finiteCoefficient_model_on_closed_support_step_empty
      T _ ℓ _ M S hS D hD Y i hI hE hYi

end AlgebraicGeometry.ProEtale
