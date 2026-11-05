/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTatePullbackFactor
public import WeilConjectures.WeilSheaf.SmoothPurityRationalRootLaw
public import WeilConjectures.WeilSheaf.SmoothPurityScalarDatumNamed
public import WeilConjectures.WeilSheaf.SmoothPurityFrobeniusFactorAlias
public import WeilConjectures.WeilSheaf.SmoothPurityCyclotomicField
import WeilConjectures.Tactic.ExactModProofsFallback

/-! # The scalar Frobenius law for the canonical geometric Tate line -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable {k : Type u} [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
  {ζ : ℕ → AlgebraicClosure k} (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))
  (hζ' : ∀ n, ζ (n + 1) ^ ℓ = ζ n)

local instance : NeZero (ℓ : k) := ⟨by
  rw [Ne, ringChar.spec, Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime k _) Fact.out]
  exact Fact.out⟩
local instance : NeZero (ℓ : AlgebraicClosure k) := WeilSheaf.purity_neZero_natCast_algebraicClosure k ℓ

/-- A root trivialization of the geometric Tate line, using its canonical pullback
from the finite-base model. -/
noncomputable def purityCanonicalTateOneTrivialization :
    tateTwistOne a.geometricFiber ℓ ≅
      𝟙_ (Mod (Sheaf (ProEt.topology a.geometricFiber) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) a.geometricFiber)) :=
  (upperStarTateTwistOneIso ℓ a.geometricFiberProj a).symm ≪≫
    purityChangeCoefficientTrivialization (Profinite.continuousMapRingObj ℤ_[ℓ])
      (Profinite.padicIntRingObjToPadicAlgCl ℓ) a.geometricFiberProj (tateModule X ℓ)
      (upperStarMapModTateModuleIsoUnit a.geometricFiberProj
        a.geometricFiberToAlgebraicClosure ℓ hζ hζ' ≪≫
        (a.geometricFiberProj)^*[Ab.{u + 1}].mapModUnitIso) ≪≫
    (Functor.Monoidal.εIso (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) a.geometricFiberProj)).symm

/-- The canonical geometric Tate datum has the expected q-scalar law under the
root trivialization. -/
lemma purityCanonicalTateOneTrivialization_weil :
    (Nat.card k : ℤ) •
        ((upperStarTateTwistOneIso ℓ a.geometricGaloisFrobenius.hom
          a.geometricFiberToAlgebraicClosure).hom ≫
          (purityCanonicalTateOneTrivialization ℓ a hζ hζ').hom) =
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) a.geometricGaloisFrobenius.hom).map
          (purityCanonicalTateOneTrivialization ℓ a hζ hζ').hom ≫
        (Functor.Monoidal.εIso
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) a.geometricGaloisFrobenius.hom)).inv := by
  have ha := purity_upperStarTateTwistOneIso_factor ℓ a.geometricFiberProj
    a.geometricGaloisFrobenius.hom
    a.geometricGaloisFrobenius_hom_comp_geometricFiberProj a
  rw [purity_upperStarTateTwistOneIso_independent_base ℓ a.geometricGaloisFrobenius.hom
    (a.geometricFiberProj ≫ a) a.geometricFiberToAlgebraicClosure] at ha
  have hb := purity_upperStar_unit_factor (Profinite.padicAlgClRingObj ℓ)
    a.geometricFiberProj a.geometricGaloisFrobenius.hom
    a.geometricGaloisFrobenius_hom_comp_geometricFiberProj
  have he := purity_rationalRootTrivialization_weil a hζ hζ'
  rw [← purity_geometricFiberProjUpperStarFrobeniusIso_eq
    (Profinite.padicAlgClRingObj ℓ) a] at ha hb
  have h := purity_scalarDatum_conjugate_named
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) a.geometricGaloisFrobenius.hom)
    (upperStarTateTwistOneIso ℓ a.geometricFiberProj a)
    (Functor.Monoidal.εIso (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) a.geometricFiberProj)).symm
    ((geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a).hom.app (tateTwistOne X ℓ))
    ((geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a).hom.app (𝟙_ _))
    (upperStarTateTwistOneIso ℓ a.geometricGaloisFrobenius.hom
      a.geometricFiberToAlgebraicClosure).hom
    (Functor.Monoidal.εIso
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) a.geometricGaloisFrobenius.hom)).inv
    ha hb (purityChangeCoefficientTrivialization (Profinite.continuousMapRingObj ℤ_[ℓ])
      (Profinite.padicIntRingObjToPadicAlgCl ℓ) a.geometricFiberProj (tateModule X ℓ)
      (upperStarMapModTateModuleIsoUnit a.geometricFiberProj
        a.geometricFiberToAlgebraicClosure ℓ hζ hζ' ≪≫
        (a.geometricFiberProj)^*[Ab.{u + 1}].mapModUnitIso))
    (purityCanonicalTateOneTrivialization ℓ a hζ hζ') rfl (Nat.card k : ℤ)
    (by
      dsimp only [tateTwistOne, Functor.comp_obj, Functor.comp_map] at he ⊢
      exact_mod_proofs_fallback he)
  try dsimp only [Functor.comp_obj, Functor.comp_map] at h ⊢
  exact_mod_proofs h

end AlgebraicGeometry.ProEtale
