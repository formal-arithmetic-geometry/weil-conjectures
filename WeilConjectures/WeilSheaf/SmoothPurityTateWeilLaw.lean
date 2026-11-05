/-
Copyright (c) 2026 Claude and The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityRootFrobeniusUnitLaw
public import WeilConjectures.WeilSheaf.SmoothPurityChangeCoefficientWeilLaw
import WeilConjectures.Tactic.ExactModProofs

/-! # The rational Tate trivialization and its Frobenius law -/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k ≠ l)] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
  {ζ : ℕ → AlgebraicClosure k} (hζ : ∀ n, IsPrimitiveRoot (ζ n) (l ^ n))
  (hζ' : ∀ n, ζ (n + 1) ^ l = ζ n)

/-- Trivialize the Tate twist after changing coefficients to the rational ring. -/
noncomputable def purityTateTwistOneTrivialization :
    (a.geometricFiberProj)^*⟦Profinite.padicAlgClRingObj l⟧.obj (tateTwistOne X l) ≅
      (a.geometricFiberProj)^*⟦Profinite.padicAlgClRingObj l⟧.obj (𝟙_ _) :=
  purityRationalTateTrivialization a.geometricFiberProj a.geometricFiberToAlgebraicClosure l hζ hζ'

set_option diagnostics true in
/-- The rational trivialization transports the geometric Frobenius with scalar q. -/
theorem purityTateTwistOneTrivialization_weil :
    (Nat.card k : ℤ) •
        ((geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj l) a).hom.app
            (tateTwistOne X l) ≫ (purityTateTwistOneTrivialization a hζ hζ').hom) =
      (a.geometricGaloisFrobenius.hom)^*⟦Profinite.padicAlgClRingObj l⟧.map
          (purityTateTwistOneTrivialization a hζ hζ').hom ≫
        (geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj l) a).hom.app
          (𝟙_ _) := by
  have h := purityChangeCoefficientTrivialization_weil
    (a := Profinite.padicIntRingObjToPadicAlgCl l) (f := a) (M := tateModule X l)
    (c := (Nat.card k : ℤ))
    (e₁ := upperStarMapModTateModuleIsoUnit a.geometricFiberProj
      a.geometricFiberToAlgebraicClosure l hζ hζ' ≪≫
        (a.geometricFiberProj)^*[Ab.{u + 1}].mapModUnitIso)
    (purity_tateModule_rootTrivialization_frobenius a hζ hζ')
  dsimp only [purityTateTwistOneTrivialization, purityRationalTateTrivialization,
    tateTwistOne, Functor.comp_obj, Functor.comp_map] at h ⊢
  cast_proofs h

end AlgebraicGeometry.ProEtale.CondensedRing
