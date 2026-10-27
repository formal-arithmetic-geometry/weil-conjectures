/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.SixFunctors.ScalarSixDefinitions
import Sheaf.SixFunctors.ScalarSixGeometry
import Sheaf.SixFunctors.ScalarSixDerivedPullbackNormalization
import Sheaf.SixFunctors.ScalarSixOpenComparison
import Sheaf.SixFunctors.ScalarSixImmersionComparison

/-! # Scalar comparison for inverse image and locally closed extension -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Ordinary coefficient change commutes canonically with exact inverse image and
locally closed extension by zero, with both composition and scalar-tower coherences.

Source: blueprint main-20261015, det-prop-scalar-six-pullback, clauses (1)--(3),
proof steps 1--8; Stacks Tags 0G7E, 0D6D, 09AA, 09BM, 09BN, 09AH
(blueprint: det-prop-scalar-six-pullback).

Proof:
1. Identify internal modules with sectionwise modules by the fixed equivalence, retaining
   the coefficient ring sheaf. The alpha isomorphism and coefficient naturality give the
   restriction/pullback square. Its mate is the ordinary balanced-tensor comparison.
2. Resolve by flat-term K-flat complexes. Pullback preserves these complexes (0G7E), so
   the mate computes the canonical derived tensor map without a flatness assumption.
   Direct and iterated maps agree on balanced pure tensors, proving theta composition.
3. Finite-type schemes over a field are Noetherian. The published locally closed
   extension coherence gives exact open and closed extensions on unbounded complexes,
   their normalized restriction, factorization independence and gamma.
4. For opens, conjugate the restriction/pullback square along the exact open and scalar
   adjunctions. Unit-normalized uniqueness gives precisely derivedOpenImmersionShriekIso.
5. For closed i, insert the unit of i* left adjoint to i_*, apply inverse theta, then
   the closed counit. Restriction to i is invertible; restriction to the complementary
   open vanishes. Open/closed detection proves the comparison is invertible.
6. Factor an immersion as closed then open and compose the two comparisons. Its
   restriction is inverse theta. Full faithfulness of extension proves independence
   and the immersion-composition equation, including mixed open/closed compositions.
7. Transitivity of restriction gives the normalized scalar-adjunction conjugate tau.
   On K-flat complexes it is c tensor (b tensor m) to cb tensor m, with inverse
   c tensor m to c tensor (1 tensor m).
8. The inverse-image/tower square agrees on these pure tensors. The open square follows
   by conjugation and unit normalization. Restrict the closed and locally closed squares;
   they become the inverse-image square. Faithfulness proves equality before restriction.
-/
theorem scalarSixPullback :
    ∃ G : ScalarSixGeometry.{u}, ∃ C : ScalarSixPullbackData.{u},
      ∀ (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
        [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)],
      ∃ E : LocallyClosedExtensionData.{u}, E.Coherent ∧
        ∃ D : E.DerivedCoherence, ∃ O : ScalarSixOpenComparison E G k,
          ScalarSixExtensionData E D G C k O := by
  obtain ⟨G⟩ := scalarSixGeometry_exists
  obtain ⟨C⟩ := scalarSixPullbackData_exists
  refine ⟨G, C, ?_⟩
  intro ell hell k hk hp hne
  obtain ⟨E, hE, ⟨D⟩⟩ := locallyClosedExtensionCoherence
  obtain ⟨O⟩ := scalarSixOpenComparison_exists E G k
  exact ⟨E, hE, D, O, scalarSixExtensionData_exists E hE D G C k O⟩

end AlgebraicGeometry.ProEtale.CondensedRing
