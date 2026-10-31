/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Punctured-line vanishing for the unit Fourier transform

Source: current blueprint, lem-fd-first-formula.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The Fourier transform of the coefficient unit vanishes on the punctured dual line,
for finite-intermediate-field and finite-subextension algebraic-closure coefficients.

Source: latest blueprint, lem-fd-first-formula.proof.md, constant-sheaf paragraph,
nonzero geometric fibres (blueprint: lem-fd-unit-punctured-vanishing).

Proof in words. Work first over k₀ with E coefficients. Pulling the unit back in the
transform gives the unit, so the integrand is the degree-q Artin--Schreier kernel.
At a geometric point ξ outside the origin, compact-support base change identifies its
pullback with the compact-support integral on the affine line of x ↦ xξ, shifted by one.
The coordinate ξ is nonzero because the point factors through the open complement.
The character integral for a nonzero linear form has zero derived coefficient sections.
Its bounded constructible homology over the algebraically closed point consists of
finite-dimensional coefficient modules: the point coefficient equivalence and local
finite-freeness identify each with a finite free coefficient object. Point sections are
exact and faithful on these objects, so this compact-support object itself is zero.
The transform is bounded constructible, as is its open restriction.
Geometric-pullback conservativity over the
finite field therefore makes that open restriction zero. For an arbitrary k/k₀ in the
statement, pull this vanishing back along the base map on punctured lines: compact-support
exchange, monoidal pullback and the kernel's pullback comparison identify the result with
the stated transform. The source schemes over k₀ are Noetherian, so this exchange permits
an arbitrary extension k/k₀. Finally extend scalars from E to the condensed algebraic
closure. Scalar exchange for pullback, tensor and compact support identifies the
transform; on the kernel it identifies the image of the same E-defined character
projector on the finite étale Artin--Schreier torsor pushforward. Thus its open
restriction is also zero. No localization or calculation of the zero fibre is used. -/
theorem first_formula_unit_punctured_vanishing
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [CharP k₀ p]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (hμ : ∀ ζ : rootsOfUnity p (PadicAlgCl ℓ), ((ζ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) ∈ E.1)
    (ψ : AddChar k₀ E) (hψ : ψ ≠ 1)
    (k : Type u) [Field k] [Algebra k₀ k] (hk : Finite k ∨ IsAlgClosed k)
    (c : Compactification (pullback.snd
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k))
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k)))) :
  IsZero ((CondensedRing.upperStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k))).openComplement.ι).leftDerivedFunctor.obj
    ((condensedFieldFourierTransform (Profinite.continuousMapRingObj E.1) k₀ k
        ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) c).obj
      ((DerivedCategory.singleFunctor _ 0).obj
      (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) (AffineSpace PUnit
        (Spec (.of k)))))))) ∧
  IsZero ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
      (AffineSpace.zeroSection PUnit (Spec (.of k))).openComplement.ι).leftDerivedFunctor.obj
    ((condensedFieldFourierTransform (Profinite.padicAlgClRingObj ℓ) k₀ k
        ((Profinite.PadicAlgCl.constRingHom ℓ).toMonoidHom.compAddChar
        (E.1.subtype.toMonoidHom.compAddChar ψ)) c).obj
      ((DerivedCategory.singleFunctor _ 0).obj
      (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (AffineSpace PUnit (Spec
        (.of k)))))))) := by
  sorry

end AlgebraicGeometry.ProEtale
