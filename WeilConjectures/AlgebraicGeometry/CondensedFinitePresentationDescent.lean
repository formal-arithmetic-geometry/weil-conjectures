/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.AlgebraicGeometry.CondensedLfpCoefficientModel
import WeilConjectures.AlgebraicGeometry.CondensedStratumModelAssembly
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage

/-!
# Descent of a constructible condensed module to finite coefficients
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A constructible module over the finite-subextension-valued condensed algebraic closure
has a constructible model over one finite coefficient field. -/
theorem exists_constructible_finiteCoefficient_model
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (padicAlgClRingObj T ℓ))
    (hM : IsConstructibleModuleObject (padicAlgClRingObj T ℓ) M) :
    ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (M_E : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ E)),
      IsConstructibleModuleObject (padicSubfieldRingObj T ℓ E) M_E ∧
        Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).obj M_E ≅ M) := by
  obtain ⟨S, hS⟩ := hM
  apply exists_finiteCoefficient_model_of_stratum_models T ℓ M S
  intro a
  exact exists_lfp_finiteCoefficient_model_on_immersion T (S.domain a) (S.immersion a) ℓ
    (((upperStar Ab.{u + 1} (S.immersion a)).mapMod (padicAlgClRingObj T ℓ)).obj M) (hS a)

end AlgebraicGeometry.ProEtale
