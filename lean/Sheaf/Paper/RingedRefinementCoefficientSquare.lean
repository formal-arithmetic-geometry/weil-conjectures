/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.RingedRefinementData
import Sheaf.Paper.CanonicalRingedRefinementShape
import Sheaf.Paper.RingedRefinementCore
import Sheaf.Paper.RingedRefinementClopen
import Sheaf.Paper.RingedRefinementFinite

/-!
# Coefficient change and clopen refinement mates

(blueprint: lem-pur-ringed-refinement-coefficient-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules
open RingedRefinement

/-- Coefficient change preserves the canonical clopen refinement mate, with all
coherences on ordinary unbounded derived categories, also for strict inverse systems.
Source: Bhatt--Scholze, 6.7.6--6.7.7, ordinary-derived coefficient supplement
(blueprint: lem-pur-ringed-refinement-coefficient-square).

Proof:
1. Use the geometric clopen-section clause of
   lem-cbc-strict-tower-proper-open-calculus to construct each Shape. Its projections
   and distinguished section give the two open components without a cartesian
   hypothesis on the original refinement triangle.
2. Construct the inverse-image ring identifications and actual module operations.
   The exact inverse-image/right-derived direct-image adjunction is the one of
   lem-weil-pbc-ringed-projection-mate-exact. Use lem-pur-derived-change-of-rings for
   K-flat scalar extension and lem-pur-site-restriction-module-adjunction-exact for
   exact open extension. Sectionwise direct-image compositors fix all conjugate
   pullback and proper-image comparisons.
3. Use lem-sfb-ringed-derived-monoidal-comparisons for the normalized scalar/pullback
   comparison. Its ordinary transpose is identity on underlying sections; compute
   the derived comparison on common flat-term K-flat representatives.
4. Apply lem-sf-open-tensor-normalization to beta and delta. Their inverse transposes
   are the displayed open units. The two-component module decomposition defines pi
   as (identity, zero), so scalar extension preserves it. Pasting the three factors
   gives delta1 S1(hA) c_u = hB L_B(delta2), naturally in M.
5. Take B-geometric adjunction transposes. The definition of chi, from
   lem-pur-ringed-coefficient-projection-cocycle, replaces its transpose by scalar
   extension of the A-counit after the canonical inverse-image/scalar comparison.
   Counit naturality and the adjunct equation of r reduce both sides to Step 4.
   Injectivity of the Hom bijection proves square; chi is never inverted.
6. Balanced tensor associators and their unit normalizations are those of
   lem-sfb-successive-derived-quotient-normalization. On pure tensors the double
   scalar comparison multiplies the two scalars. The coefficient cocycle and its
   commuting-square clause give coefficient composition and naturality.
7. Successive clopen projections select nested components, so their composite is
   the same projection (identity, zero, zero). The normalized open comparators
   respect this decomposition. Mate pasting gives the stated refinement composition
   and identity equations. Pasting the scalar/pullback comparisons and transposing
   gives spatial_coefficient; hence the coefficient squares paste compatibly.
8. All exact open maps act termwise, scalar shifts are normalized by their universal
   cochain counits, and lem-weil-pbc-derived-adjunction-shift fixes the geometric
   unit and counit shifts. The same calculation proves every Shifts field.
9. Carry out Steps 1--8 on the actual vertical ringed diagram sites using
   lem-weil-pbc-diagram-site-realization and lem-coef-semilinear-derived-sections.
   Arbitrary ring sheaves there retain all semilinear transitions. No evaluation,
   total limit, normalized-input restriction or detection of morphism equality is
   involved in any equation.
10. For constant finite coefficients the section-preserving diagram realization
    and constant-section ring maps fix FiniteRealization. Its ordinary direct-image
    comparison retains sections; its adjoint and exact localization fix pull,
    while the derived adjunction fixes push. The open unit fixes shriekIso.
    Under these identifications the three h factors are exactly the alpha of
    lem-cbc-strict-tower-proper-open-calculus. Their adjunct is its gamma, after
    the canonical identity-proper comparison. This proves FiniteNormalization.
No flatness of coefficient maps, invertibility of chi, noetherian hypothesis,
or boundedness of inputs is used. -/
theorem ringedRefinementCoefficientSquare :
    (∀ T : Scheme.{u}, Nonempty (RingedRefinement.Package .ordinary T)) ∧
    (∀ T : Scheme.{u}, ∃ P : RingedRefinement.Package .systems T,
      ∀ (B : Type (u + 1)) [CommRing B] [Finite B],
        ∃ (e : ∀ W : Over T, RingedRefinement.FiniteRealization P B W)
          (k : RingedRefinement.FiniteComparison P B e),
          RingedRefinement.FiniteNormalization P B e k) := by
  have build (m : Mode) (T : Scheme.{u}) : Nonempty (Package m T) := by
    obtain ⟨o, p, sc, ⟨ac⟩⟩ := ringedRefinementCore m T
    obtain ⟨e, hc, hr, ⟨hs⟩⟩ := ringedRefinementClopen o p sc ac
    exact ⟨{
      coefficients := canonicalCoefficients m T
      operations := o
      spatial := p
      scalars := sc
      associators := ac
      opens := e
      refinements := canonicalRefinements e
      laws := laws_of_clopen sc ac (canonicalRefinements e) hc hr
      shifts := shifts_of_generators sc (canonicalRefinements e) hs
      shapes := fun u j₁ j₂ _ _ _ _ _ h ↦ canonicalShape u j₁ j₂ h }⟩
  constructor
  · exact build .ordinary
  · intro T
    obtain ⟨P⟩ := build .systems T
    exact ⟨P, fun B _ _ ↦ ringedRefinementFinite P B⟩

end SheafOfModules
