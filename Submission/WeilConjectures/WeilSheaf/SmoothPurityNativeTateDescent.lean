/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Submission.WeilConjectures.WeilSheaf.SmoothPurityTateDescentPair
public import Submission.WeilConjectures.WeilSheaf.SmoothPurityTateCondensedEncoding
public import Submission.WeilConjectures.WeilSheaf.TateTwistCohomology

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The native Tate sheaf as finite-base descent -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime]
  [Fact (ringChar k₀ ≠ ℓ)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The native cyclotomic Tate sheaf is descent of the finite-base root-defined Tate sheaf. -/
theorem purity_nonempty_toCondensedTateDescentIso (d : ℕ) :
    Nonempty ((ProEtaleWeilSheaf.toCondensed k₀ ℓ X).obj
        (tateTwistSheaf k₀ ℓ X d).obj ≅
      (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj ℓ)
        (X ↘ Spec (.of k₀))).obj (ProEtale.tateTwist X ℓ d)) := by
  obtain ⟨e⟩ := purity_nonempty_tateRootPair_iso_toCondensed_constantTwist k₀ ℓ X d
  exact ⟨(ProEtaleWeilSheaf.toCondensed k₀ ℓ X).mapIso (tateTwistSheafNatObjIso k₀ ℓ X d) ≪≫
    e.symm ≪≫ (purity_geometricFiberWeilLowerStarTateRootIso k₀ ℓ X d).symm⟩

end AlgebraicGeometry.WeilSheaf
