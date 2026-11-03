/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteRingCompactSupport.FiniteRingCanonicalCompactSupport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor

/-! # Pasting of finite-ring compact-support exchange for powers

Source: finite torsion compact-support base change, horizontal pasting, and its
specified site-comparison transport
(blueprint: lem-trf-finite-ring-compact-exchange-power).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.FiniteRingCompactSupport

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Horizontal pasting for the specified finite-ring exchanges, including the source
and target normalized derived compositors.
Source: `thm-cbc-finite-torsion`, horizontal pasting, and
`thm-cbc-finite-level-proetale`, transport of the specified exchange
(blueprint: lem-trf-finite-ring-compact-exchange-power).

Proof: represent K by its bounded-below etale model. On this model compute the exchange
as proper base change followed by inverse open base change. The horizontal pasting identity
of the etale compact-support formalism compares the direct rectangle with the two successive
squares. Change the resulting compactifications by the canonical common-refinement
comparisons; their cocycle and exchange naturality cancel the intermediate comparison. The
pullback-site comparisons respect composition, so transporting this equality gives the displayed
formula with the inverse canonical pullback compositors. Naturality in the comparison from the
model to K removes the chosen presentation. All comparisons are the specified ones. -/
theorem finiteRingCompactExchange_power
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (w : Aut X) (v : Aut Y)
    (sq : ∀ r : ℕ, IsPullback (w ^ r).hom f f (v ^ r).hom)
    (c : Compactification f) (m : ℕ)
    (K : Category A X)
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K) :
    (((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v.hom (v ^ m).hom).symm ≪≫
        leftDerivedUpperStarCongr (ModuleCat.{u + 1} A)
          (congrArg Iso.hom (pow_succ v m)).symm).hom.app ((support A c).obj K)) ≫
      exchange A (sq (m + 1)) c c K
        (constructibleFiniteTor_leftDerivedFunctor_upperStar_obj _ hK).plusEtaleOrigin =
    (upperStar (ModuleCat.{u + 1} A) v.hom).leftDerivedFunctor.map
        (exchange A (sq m) c c K
          (constructibleFiniteTor_leftDerivedFunctor_upperStar_obj _ hK).plusEtaleOrigin) ≫
      exchange A (sq 1) c c
        ((upperStar (ModuleCat.{u + 1} A) (w ^ m).hom).leftDerivedFunctor.obj K)
        (constructibleFiniteTor_leftDerivedFunctor_upperStar_obj _
          (constructibleFiniteTor_leftDerivedFunctor_upperStar_obj _ hK)).plusEtaleOrigin ≫
      (support A c).map
        (((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w.hom (w ^ m).hom).symm ≪≫
          leftDerivedUpperStarCongr (ModuleCat.{u + 1} A)
            (congrArg Iso.hom (pow_succ w m)).symm).hom.app K) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteRingCompactSupport
