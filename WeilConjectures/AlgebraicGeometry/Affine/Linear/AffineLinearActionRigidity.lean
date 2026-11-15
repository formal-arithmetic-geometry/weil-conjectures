/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearUniversalAction
import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift

/-! # Identity detection on the universal linear parameter scheme
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- An endomorphism of the universal affine trace object is the identity if its
pullback to the identity-matrix section is the identity. -/
theorem linearAction_eq_id_of_identitySection
    (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (r : linearActionObject A N hA (generalLinearOpen d S).toScheme d ⟶
      linearActionObject A N hA (generalLinearOpen d S).toScheme d)
    (hr : (ordinaryFinitePullback A (glOne (c := d) (S := S))).map r = 𝟙 _) :
    r = 𝟙 _ := by
  obtain ⟨t₀, D₀, _, htrace⟩ := exists_affineSpaceTopTrace N hN A hA
  have := (htrace (generalLinearOpen d S).toScheme
    (linearUniversalInvertible N S hS d) d).2.2.1
  let e := asIso (affineTraceCounit A N hA t₀ D₀ (generalLinearOpen d S).toScheme
    (linearUniversalInvertible N S hS d) d)
  have hunit : DerivedCategory.isInvertible A (generalLinearOpen d S).toScheme
      (ordinaryFiniteUnit A (generalLinearOpen d S).toScheme) :=
    ⟨_, ⟨derivedTensorLeftUnitor _ _ _⟩, ⟨derivedTensorLeftUnitor _ _ _⟩⟩
  exact eq_id_of_leftDerivedUpperStar_map_eq_id_of_isInvertible glOne
    exists_isPreconnected_glOne (DerivedCategory.isInvertible.of_iso e.symm hunit) r hr

end AlgebraicGeometry.Etale
