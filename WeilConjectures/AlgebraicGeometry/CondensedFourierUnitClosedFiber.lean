/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.AlgebraicGeometry.InternalSignedTateTwist
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import WeilConjectures.AlgebraicGeometry.CondensedFourierUnitClosedFiberE
import WeilConjectures.AlgebraicGeometry.CondensedFourierUnitClosedFiberQbar

/-! # The closed zero-fibre calculation for the unit Fourier transform

Source: current blueprint, lem-fd-first-formula.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Pushing the ordinary zero-fibre restriction of the unit transform back to the line
identifies it with the signed-Tate-twisted skyscraper shifted by minus one, for both
coefficient models. This computes the zero fibre and asserts nothing about support away
from zero.

Source: latest blueprint, lem-fd-first-formula.proof.md, constant-sheaf paragraph,
zero-fibre calculation (blueprint: lem-fd-unit-closed-fiber).

Proof in words. First use E coefficients over k₀. Compact-support base change along the
zero section identifies the ordinary derived restriction of FT(E) with the compact-support
direct image of the restricted kernel, shifted by one. The pairing restricted to this
fibre is zero. Pullback composition and root-zero evaluation on the degree-q
Artin--Schreier projector identify that kernel with the coefficient unit. The rational
affine-line trace over k₀ identifies its compact-support image with the negative Tate
line shifted by minus two; composing shifts gives minus one. Apply closed direct image.
It commutes with shifts, and the closed support projection formula, together with the
cartesian Tate-line comparison, identifies the pushed negative line with the negative
Tate twist of the origin skyscraper. Pull this whole comparison to k along the field
map. Compact-support exchange uses Noetherian source schemes over k₀ and allows this
arbitrary base map; the closed-immersion exchange and the coefficient and Tate pullback
comparisons identify both endpoints. For algebraic-closure coefficients extend scalars:
the scalar-six comparisons commute with the operations, preserve the E-defined
Artin--Schreier character projector, and identify the scalar-extended Tate line with the
actual Qbar line. These are only zero-fibre comparisons; no punctured-line vanishing or
invertibility of the localization unit is assumed. -/
theorem first_formula_unit_closed_fiber
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [CharP k₀ p]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (hμ : ∀ ζ : rootsOfUnity p (PadicAlgCl ℓ), ((ζ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) ∈ E.1)
    (ψ : AddChar k₀ E) (hψ : ψ ≠ 1)
    (k : Type u) [Field k] [Algebra k₀ k] (hk : Finite k ∨ IsAlgClosed k)
    (c : Compactification (pullback.snd
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k))
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k)))) :
  Nonempty ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
    ((CondensedRing.upperStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).leftDerivedFunctor.obj
      ((condensedFieldFourierTransform (Profinite.continuousMapRingObj E.1) k₀ k
        ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) c).obj
      ((DerivedCategory.singleFunctor _ 0).obj
      (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) (AffineSpace PUnit
        (Spec (.of k)))))))) ≅
    (shiftFunctor _ (-1 : ℤ)).obj
      (spInternalComplexTwist (AffineSpace PUnit (Spec (.of k))) _ (spRationalTwist (AffineSpace
        PUnit (Spec (.of k))) ℓ E)
        ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) (Spec (.of k))))))
        (-1))) ∧
  Nonempty ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).leftDerivedFunctor.obj
      ((condensedFieldFourierTransform (Profinite.padicAlgClRingObj ℓ) k₀ k
        ((Profinite.PadicAlgCl.constRingHom ℓ).toMonoidHom.compAddChar
        (E.1.subtype.toMonoidHom.compAddChar ψ)) c).obj
      ((DerivedCategory.singleFunctor _ 0).obj
      (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (AffineSpace PUnit (Spec
        (.of k)))))))) ≅
    (shiftFunctor _ (-1 : ℤ)).obj
      (spInternalComplexTwist (AffineSpace PUnit (Spec (.of k))) _ (spQbarTwist (AffineSpace
        PUnit (Spec (.of k))) ℓ)
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k))))))
        (-1))) := by
  constructor
  · exact first_formula_unit_closed_fiber_E p ℓ hpℓ k₀ E hμ ψ hψ k hk c
  · exact first_formula_unit_closed_fiber_Qbar p ℓ hpℓ k₀ E hμ ψ hψ k hk c

end AlgebraicGeometry.ProEtale
