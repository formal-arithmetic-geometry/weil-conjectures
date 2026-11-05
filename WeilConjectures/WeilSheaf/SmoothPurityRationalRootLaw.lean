/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityRootFrobeniusUnitLaw
public import WeilConjectures.WeilSheaf.SmoothPurityChangeCoefficientWeilLaw
import WeilConjectures.Tactic.ExactModProofs

/-! # The scalar law immediately after rational coefficient change -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
  {ζ : ℕ → AlgebraicClosure k} (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))
  (hζ' : ∀ n, ζ (n + 1) ^ ℓ = ζ n)

/-- Coefficient change carries the root trivialization and its scalar Frobenius law. -/
theorem purity_rationalRootTrivialization_weil :
    (Nat.card k : ℤ) •
        ((geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a).hom.app
          ((Mod.extendScalars (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl ℓ) X)).obj
            (tateModule X ℓ)) ≫
          (purityChangeCoefficientTrivialization (Profinite.continuousMapRingObj ℤ_[ℓ])
            (Profinite.padicIntRingObjToPadicAlgCl ℓ) a.geometricFiberProj (tateModule X ℓ)
            (upperStarMapModTateModuleIsoUnit a.geometricFiberProj
              a.geometricFiberToAlgebraicClosure ℓ hζ hζ' ≪≫
              (a.geometricFiberProj)^*[Ab.{u + 1}].mapModUnitIso)).hom) =
      (a.geometricGaloisFrobenius.hom)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
          (purityChangeCoefficientTrivialization (Profinite.continuousMapRingObj ℤ_[ℓ])
            (Profinite.padicIntRingObjToPadicAlgCl ℓ) a.geometricFiberProj (tateModule X ℓ)
            (upperStarMapModTateModuleIsoUnit a.geometricFiberProj
              a.geometricFiberToAlgebraicClosure ℓ hζ hζ' ≪≫
              (a.geometricFiberProj)^*[Ab.{u + 1}].mapModUnitIso)).hom ≫
        (geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a).hom.app
          (𝟙_ _) := by
  have h := purityChangeCoefficientTrivialization_weil
    (a := Profinite.padicIntRingObjToPadicAlgCl ℓ) (f := a) (M := tateModule X ℓ)
    (c := (Nat.card k : ℤ))
    (e₁ := upperStarMapModTateModuleIsoUnit a.geometricFiberProj
      a.geometricFiberToAlgebraicClosure ℓ hζ hζ' ≪≫
        (a.geometricFiberProj)^*[Ab.{u + 1}].mapModUnitIso)
    (by
      have hr := purity_tateModule_rootTrivialization_frobenius a hζ hζ'
      dsimp only [Functor.comp_obj, Functor.comp_map] at hr ⊢
      run_tac
        let ht ← Lean.Elab.Term.elabTerm (Lean.mkIdent `hr) none
        let mut pending := #[(← Lean.Meta.inferType ht, ← Lean.Elab.Tactic.getMainTarget)]
        let mut count := 0
        while !pending.isEmpty && count < 20 do
          let (a, b) := pending.back!
          pending := pending.pop
          if a == b then continue
          if (← Lean.Meta.isProof a) then continue
          let aa := a.getAppArgs
          let bb := b.getAppArgs
          if a.getAppFn == b.getAppFn && aa.size == bb.size && aa.size > 0 then
            for i in [:aa.size] do
              pending := pending.push (aa[i]!, bb[i]!)
          else
            count := count + 1
            Lean.logInfo m!"Root input data difference: {a.getAppFn} versus {b.getAppFn}"
        Lean.logInfo m!"Root input data differences: {count}"
      cast_proofs hr)
  dsimp only [Functor.comp_obj, Functor.comp_map] at h ⊢
  run_tac
    let ht ← Lean.Elab.Term.elabTerm (Lean.mkIdent `h) none
    let mut pending := #[(← Lean.Meta.inferType ht, ← Lean.Elab.Tactic.getMainTarget)]
    let mut count := 0
    while !pending.isEmpty && count < 20 do
      let (a, b) := pending.back!
      pending := pending.pop
      if a == b then continue
      if (← Lean.Meta.isProof a) then continue
      let aa := a.getAppArgs
      let bb := b.getAppArgs
      if a.getAppFn == b.getAppFn && aa.size == bb.size && aa.size > 0 then
        for i in [:aa.size] do
          pending := pending.push (aa[i]!, bb[i]!)
      else
        count := count + 1
        Lean.logInfo m!"Rational root data difference: {a.getAppFn} versus {b.getAppFn}"
    Lean.logInfo m!"Rational root data differences: {count}"
  cast_proofs h

end AlgebraicGeometry.ProEtale.CondensedRing
