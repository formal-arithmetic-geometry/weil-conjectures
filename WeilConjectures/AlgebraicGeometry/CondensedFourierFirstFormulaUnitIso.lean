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

import WeilConjectures.AlgebraicGeometry.CondensedFourierUnitPuncturedVanishing
import WeilConjectures.AlgebraicGeometry.CondensedFourierUnitClosedFiber
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleClosedPushforward

/-! # One calculation in the first Fourier formulas

Source: current blueprint, lem-fd-first-formula.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The constant-unit Fourier comparisons for both coefficient models.

Source: current blueprint, first-formula proof, constant-sheaf paragraph
(blueprint: lem-fd-first-formula-unit-iso).

Proof in words. First work over k₀ with finite-intermediate-field coefficients. Expanding
the transform of the unit gives the compact-support direct image of the kernel shifted by
one. At every nonzero geometric point the stalk formula and nontrivial character integral
make this object zero. Its restriction to the punctured line is bounded constructible, so
geometric-fibre conservativity makes that restriction zero. The ordinary open-closed
localization triangle then identifies the transform with the closed direct image of its
ordinary restriction to zero. Shriek base change at zero and the zero-function
Artin-Schreier unit trivialization identify that restriction with the compact-support
cohomology of the affine line shifted by one. The rational affine-line trace over k₀ is the
negative Tate line shifted by minus two; after the Fourier shift it is shifted by minus one.
The closed support projection formula moves the Tate line through the zero-section direct
image, yielding the signed twist of the skyscraper. Pull this comparison to k by arbitrary
base-map compact-support exchange; coefficient and monoidal pullback comparisons identify
the displayed objects. Finally extend coefficients to the finite-subextension algebraic
closure. Scalar comparisons commute with all the operations and with the character
projector on the finite etale torsor pushforward, hence preserve the actual kernel and Tate
line. This gives the second displayed comparison without any choice of a trivial Tate line.
-/
theorem first_formula_unit_iso
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [CharP k₀ p]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (hμ : ∀ ζ : rootsOfUnity p (PadicAlgCl ℓ), ((ζ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) ∈ E.1)
    (ψ : AddChar k₀ E) (hψ : ψ ≠ 1)
    (k : Type u) [Field k] [Algebra k₀ k] (hk : Finite k ∨ IsAlgClosed k)
    (c : Compactification (pullback.snd
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k))
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k)))) :
  Nonempty ((condensedFieldFourierTransform (Profinite.continuousMapRingObj E.1) k₀ k
        ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) c).obj
      ((DerivedCategory.singleFunctor _ 0).obj
      (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) (AffineSpace PUnit
        (Spec (.of k)))))) ≅
    (shiftFunctor _ (-1 : ℤ)).obj
      (spInternalComplexTwist (AffineSpace PUnit (Spec (.of k))) _ (spRationalTwist (AffineSpace
        PUnit (Spec (.of k))) ℓ E)
        ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) (Spec (.of k))))))
        (-1))) ∧
  Nonempty ((condensedFieldFourierTransform (Profinite.padicAlgClRingObj ℓ) k₀ k
        ((Profinite.PadicAlgCl.constRingHom ℓ).toMonoidHom.compAddChar
        (E.1.subtype.toMonoidHom.compAddChar ψ)) c).obj
      ((DerivedCategory.singleFunctor _ 0).obj
      (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (AffineSpace PUnit (Spec
        (.of k)))))) ≅
    (shiftFunctor _ (-1 : ℤ)).obj
      (spInternalComplexTwist (AffineSpace PUnit (Spec (.of k))) _ (spQbarTwist (AffineSpace
        PUnit (Spec (.of k))) ℓ)
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k))))))
        (-1))) := by
  obtain ⟨hE, hQ⟩ := first_formula_unit_punctured_vanishing p ℓ hpℓ k₀ E hμ ψ hψ k hk c
  obtain ⟨⟨eE⟩, ⟨eQ⟩⟩ := first_formula_unit_closed_fiber p ℓ hpℓ k₀ E hμ ψ hψ k hk c
  let i := AffineSpace.zeroSection PUnit (Spec (.of k))
  let U := i.openComplement
  have : IsLocallyNoetherian (AffineSpace PUnit (Spec (.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k))
  have hij : IsCompl (Set.range i.base) (Set.range U.ι.base) := by
    dsimp only [U]
    rw [i.range_eq_compl_range_openComplement_ι]
    exact isCompl_compl.symm
  constructor
  · have h := CondensedRing.isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero
      (Profinite.continuousMapRingObj E.1) U.ι i hij hE
    exact ⟨@asIso _ _ _ _ _ h ≪≫ eE⟩
  · have h := CondensedRing.isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero
      (Profinite.padicAlgClRingObj ℓ) U.ι i hij hQ
    exact ⟨@asIso _ _ _ _ _ h ≪≫ eQ⟩

end AlgebraicGeometry.ProEtale
