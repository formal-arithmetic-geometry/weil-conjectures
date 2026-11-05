/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityScalarPullbackInterface
public import WeilConjectures.WeilSheaf.SmoothPurityK4NativeScalarRoot
import WeilConjectures.Tactic.ExactModProofs

/-! # The scalar law immediately after rational coefficient change -/

set_option profiler true
set_option profiler.threshold 1

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.K4Native

open CondensedRing

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
  {ζ : ℕ → AlgebraicClosure k} (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))
  (hζ' : ∀ n, ζ (n + 1) ^ ℓ = ζ n)

/-- Identify the whole descent isomorphism with its normalized native component. -/
lemma scalarSourceIso_eq :
    purityScalarSourceIso ℓ a =
      scalarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a
        ((Mod.extendScalars (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl ℓ) X)).obj
          (tateModule X ℓ)) := by
  rw [purityScalarSourceIso_eq]
  rfl

/-- Identify the whole unit descent isomorphism. -/
lemma scalarSourceUnitIso_eq :
    purityScalarSourceUnitIso ℓ a =
      scalarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a (𝟙_ _) := by
  rw [purityScalarSourceUnitIso_eq]
  rfl

/-- The native scalar law in the consumer's named data. -/
lemma scalarRootTrivialization_weil :
    (Nat.card k : ℤ) •
        (purityScalarSourceDatum ℓ a ≫ (purityScalarRootTrivialization ℓ a hζ hζ').hom) =
      (purityScalarFrobeniusPull ℓ a).map
          (purityScalarRootTrivialization ℓ a hζ hζ').hom ≫
        purityScalarSourceUnitDatum ℓ a := by
  have h := purity_rationalRootTrivialization_weil a hζ hζ'
  rw [← purityScalarRootTrivialization_eq] at h
  rw [← scalarSourceIso_eq a, ← scalarSourceUnitIso_eq a] at h
  rw [purityScalarSourceDatum_eq_iso, purityScalarSourceUnitDatum_eq_iso]
  dsimp +instances only [purityScalarFrobeniusPull, Functor.comp_obj, Functor.comp_map] at h ⊢
  exact_mod_proofs h

end AlgebraicGeometry.ProEtale.K4Native
