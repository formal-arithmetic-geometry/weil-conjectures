/-
Copyright (c) 2026 Claude and The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityRationalRootLaw
public import WeilConjectures.WeilSheaf.SmoothPurityScalarIsoAlias

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

/-- Identify the two trivializations at the isomorphism level. -/
lemma purityTateTwistOneTrivialization_eq :
    purityTateTwistOneTrivialization a hζ hζ' =
      purityChangeCoefficientTrivialization (Profinite.continuousMapRingObj ℤ_[l])
        (Profinite.padicIntRingObjToPadicAlgCl l) a.geometricFiberProj (tateModule X l)
        (upperStarMapModTateModuleIsoUnit a.geometricFiberProj
          a.geometricFiberToAlgebraicClosure l hζ hζ' ≪≫
          (a.geometricFiberProj)^*[Ab.{u + 1}].mapModUnitIso) := rfl

/-- The rational trivialization transports the geometric Frobenius with scalar q. -/
theorem purityTateTwistOneTrivialization_weil :
    (Nat.card k : ℤ) •
        ((geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj l) a).hom.app
            (tateTwistOne X l) ≫ (purityTateTwistOneTrivialization a hζ hζ').hom) =
      (a.geometricGaloisFrobenius.hom)^*⟦Profinite.padicAlgClRingObj l⟧.map
          (purityTateTwistOneTrivialization a hζ hζ').hom ≫
        (geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj l) a).hom.app
          (𝟙_ _) := by
  -- The motive is spelled like the goal; the object and the isomorphism of `he` come from the
  -- rational root law by unification, so that the kernel only compares `tateTwistOne X l` with
  -- its unfolding outside of `NatTrans.app`.
  have key := purity_motive_of_heq
    (β := fun M => (a.geometricFiberProj)^*⟦Profinite.padicAlgClRingObj l⟧.obj M ≅
      (a.geometricFiberProj)^*⟦Profinite.padicAlgClRingObj l⟧.obj (𝟙_ _))
    (fun M w => (Nat.card k : ℤ) •
        ((geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj l) a).hom.app
            M ≫ w.hom) =
      (a.geometricGaloisFrobenius.hom)^*⟦Profinite.padicAlgClRingObj l⟧.map w.hom ≫
        (geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj l) a).hom.app
          (𝟙_ _))
    (purity_rationalRootTrivialization_weil a hζ hζ')
    (x' := tateTwistOne X l) (v := purityTateTwistOneTrivialization a hζ hζ')
  exact key rfl (heq_of_eq (purityTateTwistOneTrivialization_eq a hζ hζ'))

end AlgebraicGeometry.ProEtale.CondensedRing
