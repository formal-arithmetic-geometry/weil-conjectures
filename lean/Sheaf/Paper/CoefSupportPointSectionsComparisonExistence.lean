/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefSupportPointSectionsData

/-! # Existence of unit-normalized native point sections

Source: Stacks 0D6E and 0941
(blueprint: lem-coef-support-point-sections-comparison-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefSupportOpenTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Exact scalar restriction commutes with the native total derived point sections,
with the prescribed derived-unit equation.
Source: Stacks, sites-cohomology.tex, lemma-derived-pushforward-composition
(Tag 0D6E); support-open-tensor proof step 4.
(blueprint: lem-coef-support-point-sections-comparison-existence).

Proof: the ordinary quotient point functor is exact coefficient restriction
followed by ordinary completed-ring tower sections, including the constant R
module action. Present both as direct image along the ringed point square.
Apply derived direct-image composition to its two factorizations. Exact scalar
restriction is computed on every complex. Its inverse-image left adjoint is
computed on flat-term K-flat complexes, and the derived pullback composition
comparison identifies the two left adjoints. Uniqueness of right adjoints gives
the desired isomorphism of total derived functors; its construction from the
universal derived units gives sectionsComparisonUnit on every complex. The
comparison keeps the constant R action and no inverse limit is taken. This
argument does not require restriction to preserve K-injective complexes. -/
theorem sectionsComparison_exists (W : Scheme.{u}) :
    ∃ comparison : quotientSections l E W ≅
        coefficientSequenceDerivedRestriction.{u, u} l E W ⋙ integralSections l E W,
      sectionsComparisonUnit l E W comparison := by
  sorry

end WeilConjectures.CoefSupportOpenTensor
