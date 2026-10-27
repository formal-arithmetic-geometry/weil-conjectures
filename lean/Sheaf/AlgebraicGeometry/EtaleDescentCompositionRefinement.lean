/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q124
-/
module

public import Sheaf.AlgebraicGeometry.FpEtaleSpaceDescent
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests

/-! # Composition, refinement, and base localization of étale descent

Source: Rydh, Submersions and effective descent of étale morphisms,
Propositions (5.6)--(5.7), printed p.19, for the category of (5.1)--(5.2)
(blueprint: lem-sfb-etale-descent-composition-refinement-calculus).

The fibre category, transport data and compatible realization squares are those of
`FpEtaleSpaceDescent`. Every base is quasi-separated. The ambient `S` only lets us
use a single existing category of algebraic spaces for all the objects over these bases.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Composition, refinement, and base locality for finitely presented étale spaces.
Source: Rydh, Propositions (5.6)--(5.7), printed p.19
(blueprint: lem-sfb-etale-descent-composition-refinement-calculus).

Proof:
1. Sheaf fibre products preserve algebraic spaces, chartwise étaleness, local finite
   presentation, and quasi-compactness of both the map and its relative diagonal.
   Quasi-separated scheme bases and their fibre products remain quasi-separated by
   the scheme qcqs permanence lemmas. Reassociation of tuples supplies coherent
   pullback comparisons. All subsequent arguments can be repeated after base change.
2. Prove refinement first. The refinement Hom lemma
   [lem-sfb-descent-data-refinement-hom] makes restriction from b-data to ba-data fully
   faithful when ba is universal descent. Its composite with the canonical functor
   is the canonical functor for ba. Hom bijectivity therefore gives Hom bijectivity
   for b. A specified realization for a restricted datum lifts, together with its
   inverse, through that fully faithful restriction, giving a realization for b.
3. For locality, let B over V realize the pulled datum, with comparison beta. Over
   T' ×_T (V ×_T V), the ratio beta₂⁻¹ beta₁ is a compatible arrow of q-data.
   Universal Hom descent for q uniquely lifts it and its inverse to an isomorphism
   lambda between the two pullbacks of B over V ×_T V.
4. The diagonal identity and triple cocycle for lambda follow by faithfulness from
   beta⁻¹ beta = 1 and cancellation in beta₃⁻¹ beta₂ beta₂⁻¹ beta₁. Thus B is a
   g-datum. Effective descent for g realizes it by C over T with comparison gamma.
5. The composite beta gamma descends uniquely along the base change of g to T'.
   Descend its inverse as well. Faithfulness after base change to T' ×_T T' checks
   compatibility with the original datum, giving its compatible realization square.
6. For composition, descend a compatible arrow first along a, then along b. Its
   b-compatibility can be checked on X ×_T X: the map to Y ×_T Y is a composite
   of two base changes of a, hence is faithful. This gives universal Hom descent
   for ba, with uniqueness by the successive Hom bijections.
7. Over Y, the base change r : X ×_T Y → Y of ba has the graph section
   s : X → X ×_T Y with s ≫ r = a. Refinement from step 2 makes r universal
   effective descent without using the composition assertion being proved.
8. Every ba-datum is thus effective after base change along b. Apply locality from
   steps 3--5 using universal Hom descent from step 6. This proves composition.
   Realization maps and their cartesian squares are retained at each step; lifts
   respect identities and composition by faithfulness. Identity maps and empty
   schemes require no nonempty-point or cover assumption. -/
theorem etale_descent_composition_refinement_calculus {S : Scheme.{u}} :
    (∀ (X Y T : Over S), QuasiSeparatedSpace X.left → QuasiSeparatedSpace Y.left →
      QuasiSeparatedSpace T.left → ∀ (a : X ⟶ Y) (b : Y ⟶ T),
        (IsUniversalEffectiveFpEtaleDescent a → IsUniversalEffectiveFpEtaleDescent b →
          IsUniversalEffectiveFpEtaleDescent (a ≫ b)) ∧
        (IsUniversalEffectiveFpEtaleDescent (a ≫ b) →
          IsUniversalEffectiveFpEtaleDescent b)) ∧
    (∀ (X T V P : Over S), QuasiSeparatedSpace X.left → QuasiSeparatedSpace T.left →
      QuasiSeparatedSpace V.left → QuasiSeparatedSpace P.left →
      ∀ (q : X ⟶ T) (g : V ⟶ T) (h : P ⟶ X) (r : P ⟶ V)
        (square : IsPullback h r q g),
        IsUniversalFpEtaleDescent q → IsUniversalEffectiveFpEtaleDescent g →
        ∀ (D : FpEtaleDescentData q) (E : FpEtaleDescentData r),
          FpEtaleDatumPullback square D E → Nonempty E.Realization →
            Nonempty D.Realization) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
