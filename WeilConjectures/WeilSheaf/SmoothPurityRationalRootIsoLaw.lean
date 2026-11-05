/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityRationalRootLaw
public import WeilConjectures.WeilSheaf.SmoothPurityScalarIsoTransport
import WeilConjectures.Tactic.ExactModProofs

/-! # Whole-isomorphism transport in the original rational coefficient vocabulary -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
  {ζ : ℕ → AlgebraicClosure k} (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))
  (hζ' : ∀ n, ζ (n + 1) ^ ℓ = ζ n)

/-- Accept named whole isomorphisms without comparing their morphism projections. -/
theorem purity_rationalRootTrivialization_weil_of_iso_eq
    (s : (a.geometricGaloisFrobenius.hom)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj
        ((a.geometricFiberProj)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj
          ((Mod.extendScalars (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl ℓ) X)).obj
            (tateModule X ℓ))) ≅
      (a.geometricFiberProj)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj
        ((Mod.extendScalars (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl ℓ) X)).obj
          (tateModule X ℓ)))
    (t : (a.geometricGaloisFrobenius.hom)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj
        ((a.geometricFiberProj)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj (𝟙_ _)) ≅
      (a.geometricFiberProj)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj (𝟙_ _))
    (e : (a.geometricFiberProj)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj
        ((Mod.extendScalars (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl ℓ) X)).obj
          (tateModule X ℓ)) ≅
      (a.geometricFiberProj)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj (𝟙_ _))
    (hs : s =
      (geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a).app
        ((Mod.extendScalars (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl ℓ) X)).obj
          (tateModule X ℓ)))
    (ht : t =
      (geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a).app (𝟙_ _))
    (he : e =
      purityChangeCoefficientTrivialization (Profinite.continuousMapRingObj ℤ_[ℓ])
        (Profinite.padicIntRingObjToPadicAlgCl ℓ) a.geometricFiberProj (tateModule X ℓ)
        (upperStarMapModTateModuleIsoUnit a.geometricFiberProj
          a.geometricFiberToAlgebraicClosure ℓ hζ hζ' ≪≫
          (a.geometricFiberProj)^*[Ab.{u + 1}].mapModUnitIso)) :
    (Nat.card k : ℤ) • (s.hom ≫ e.hom) =
      (a.geometricGaloisFrobenius.hom)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map e.hom ≫ t.hom := by
  apply purity_scalarDatum_transport_isos
    (a.geometricGaloisFrobenius.hom)^*⟦Profinite.padicAlgClRingObj ℓ⟧
    _ s _ t _ e hs ht he (Nat.card k : ℤ)
  have h := purity_rationalRootTrivialization_weil a hζ hζ'
  dsimp +instances only [Iso.app_hom, Functor.comp_obj, Functor.comp_map] at h ⊢
  exact_mod_proofs h

end AlgebraicGeometry.ProEtale.CondensedRing
