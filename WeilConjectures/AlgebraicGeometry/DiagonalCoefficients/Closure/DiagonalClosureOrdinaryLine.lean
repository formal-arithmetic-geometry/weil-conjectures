/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientMaps
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Closure.DiagonalClosureOrdinaryLineFactorIso

/-! # Ordinary scalar extension of the rational root line to the closure -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The ordinary closure line is the scalar extension of the rational line, with
its actual colimit leg as the composite of the extension unit and the comparison. -/
theorem diagonalClosure_ordinaryLine
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (X : Scheme.{u}) (hX : IsUnit (l : Γ(X, ⊤))) :
    ∃ q : (Mod.extendScalars
        (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) X)).obj
          (spRationalTwist X l E) ≅ spQbarTwist X l,
      Mod.extendUnitHom (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) X)
          (spRationalTwist X l E) ≫ q.hom.hom = closureLineMap l E X := by
  obtain ⟨f, hf⟩ := diagonalClosure_ordinaryLine_factor l E X hX
  haveI : IsIso f := diagonalClosure_ordinaryLine_factor_isIso l E X hX f hf
  exact ⟨asIso f, hf⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
