/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Paper.CompletedCoefficientPushforwardModels

/-! # Normalized direct image on completed-coefficient diagrams

Source: Stacks Tags 0D6E, 0A07 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedCoefficientPushforward
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Extend any normalized site-side models to the coherent direct-image comparison.
The supplied structural map is fixed by all its finite projections.
The conclusion concerns strict derived diagrams and their actual limit projections;
it makes no completeness or reconstruction assertion.

Source: Stacks sites-cohomology.tex, Tags 0D6E and 0A07; Zheng, Construction 4.1
(blueprint: lem-pur-completed-coefficient-direct-image-diagrams).
Proof:
1. The constant-section maps on finite quotient sheaves are natural in the quotient
ring. The structural-map theorem constructs their unique limit map. Use the supplied
c and hc as structureMap and structureProjection. The supplied constant integral square
records compatibility with the constant-to-completed map.
2. On module sheaves each coefficient square is the identity on underlying sections.
The scalar actions agree by the ring-square equality from step 1. On small equivalent
sites apply normalized ringed-topos derived composition, and transport back to the
original sites. Exact restriction and the factors retained by source and target
identify its terms with the supplied ExactImage models. The unit equation is exactly
Square.normalization. Uniqueness of derived transformations proves the identity,
successive-quotient and projection coherence equations.
3. Apply the same construction on the sequence ringed sites. Strict coefficient
systems have their given semilinear transitions; direct image is sectionwise at every
level. Its comparison with completed-ring towers has identity underlying sections.
The normalized derived-composition construction gives diagramSquare and the evaluation
squares. This constructs a comparison before evaluation, retaining every transition.
4. Direct image preserves ordinary limits. The ordinary comparison is limit.post.
Derive both factorizations of this common direct image of tower topoi. The K-injective
composition comparison gives limitComparison and its stated unit normalization.
After precomposition with the common derived unit, both projection composites are
the ordinary limit projection followed by direct image. The universal property of
the total right derived functor therefore proves limitProjection.
All constructions can use the supplied site models: their factorization and universal
unit equations identify them uniquely with the models used in the construction. Empty
sites and identity coefficient maps satisfy the same unit equations. -/
theorem directImageDiagrams_exists {X Y : Scheme.{t}} (f : X ⟶ Y)
    (source : SiteData l E X) (target : SiteData l E Y)
    (c : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X))
    (hc : ∀ n, c ≫ (ringPush.{t, u} f).map (projection l E X n) =
      projection l E Y n ≫ finiteStructure l E f n)
    (hconstant : integralConstantToCompletionOfUniverses l E Y ≫ c =
      constantStructure l E f ≫
        (ringPush.{t, u} f).map (integralConstantToCompletionOfUniverses l E X)) :
    ∃ D : DiagramComparisonData l E f,
      D.source = source ∧ D.target = target ∧ D.structureMap = c := by
  sorry

end WeilConjectures.CompletedCoefficientPushforward
