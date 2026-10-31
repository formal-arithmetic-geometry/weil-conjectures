/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.ProEtaleCoefficients.BoundedConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComparisons

/-!
# Shift compatibility of condensed coefficient transitions

Source: `literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-thm-sfb-qlbar-two-colimit/def-sfb-derived-extend-comp-iso.proof.md`,
with the restriction in `def-sfb-constructible-extend-comp-iso.proof.md`.
(blueprint: lem-pur-general-transition-shift-compatibility)

The proof first identifies the three condensed scalar extension functors with exact
termwise derived functors.  The coefficient maps compose, so the unit-normalized
ordinary scalar comparison is the canonical composite comparison.  The factorization
of exact derived functors through cochain complexes uses identity-on-components shift
maps; the degreewise components of the scalar comparison are therefore unchanged by
an integer shift, including the sign in the shifted differential.  Localization
uniqueness then gives the shift square in the ambient derived categories.  Restricting
to the full bounded constructible subcategories preserves this equality and gives the
stated `NatTrans.CommShift` instance.  The same argument covers equal fields, zero and
negative shifts, and zero complexes.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
variable [TopologicalSpace.NoetherianSpace X]

/-- Triangulated structure on finite-field bounded constructible complexes.
Source: `prop-sfb-bounded-constructible-triangulated`
(blueprint: lem-pur-general-transition-shift-compatibility).
-/
noncomputable instance generalTransitionFiniteBoundedTriangulated
    (E : FiniteIntermediateField ℓ) :
    (boundedConstructible (padicSubfieldRingObj X ℓ E)).IsTriangulated :=
  (isTriangulated_boundedConstructible X).1 ℓ E

/-- Triangulated structure on condensed algebraic-closure bounded constructible complexes.
Source: `prop-sfb-bounded-constructible-triangulated`
(blueprint: lem-pur-general-transition-shift-compatibility).
-/
noncomputable instance generalTransitionAlgClBoundedTriangulated :
    (boundedConstructible (padicAlgClRingObj X ℓ)).IsTriangulated :=
  (isTriangulated_boundedConstructible X).2.2.1 ℓ

/-- Shift structure on the restricted finite-field scalar extension.
Source: `def-sfb-constructible-extend-subfield`
(blueprint: lem-pur-general-transition-shift-compatibility).
-/
noncomputable instance generalTransitionConstructibleExtendCommShift
    {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    (constructibleExtendScalars X ℓ h).CommShift ℤ := by
  let hF := fun K ↦ boundedConstructible_derivedExtendScalarsSubfield_obj X ℓ h K
  exact Functor.CommShift.ofComp
    ((boundedConstructible (padicSubfieldRingObj X ℓ F)).liftCompιIso
      ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
        @derivedExtendScalarsSubfield X ℓ _ E F h) hF) ℤ

/-- Shift structure on the restricted extension to condensed `Qbar` coefficients.
Source: `def-sfb-constructible-extend-to-qlbar`
(blueprint: lem-pur-general-transition-shift-compatibility).
-/
noncomputable instance generalTransitionConstructibleToAlgClCommShift
    (E : FiniteIntermediateField ℓ) :
    (constructibleToPadicAlgCl X ℓ E).CommShift ℤ := by
  let hF := fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj X ℓ E K
  exact Functor.CommShift.ofComp
    ((boundedConstructible (padicAlgClRingObj X ℓ)).liftCompιIso
      ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
        derivedExtendScalarsToPadicAlgCl X ℓ E) hF) ℤ

/-- The canonical condensed scalar-extension comparison commutes with all integer shifts.

Source: `literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-thm-sfb-qlbar-two-colimit/def-sfb-derived-extend-comp-iso.proof.md`,
termwise shift comparison and localization descent; restricted by
`def-sfb-constructible-extend-comp-iso.proof.md`.
(blueprint: lem-pur-general-transition-shift-compatibility)

Proof: Apply exactness of extension of scalars along the two finite coefficient
inclusions and along their composite.  The coefficient-map composition identifies the
composite restriction functor with direct restriction, and the unit-compatible
uniqueness of left adjoints fixes the ordinary comparison.  Exact-derived
factorizations identify this comparison with a termwise natural isomorphism.  At
cochain degree `r`, its component after shifting by `n` is the same map on the term
in degree `r + n`; multiplying the naturality equation by the shifted sign
`(-1)^n` proves the chain-map square.  The localization universal property descends
that square to the derived categories.  The full bounded constructible subcategories
are stable under shifts and their inclusions are faithful, so the restricted
comparison has `NatTrans.CommShift`.
-/
theorem generalTransitionShiftCompatibility {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    NatTrans.CommShift (constructibleToPadicAlgClCompIso X ℓ h).hom ℤ := by
  sorry

end AlgebraicGeometry.ProEtale
