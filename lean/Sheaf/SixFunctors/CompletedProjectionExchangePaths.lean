module

public import Sheaf.SixFunctors.CompletedProjectionExchangeData

/-! # A step of the completed projection/base-change diamond

Source: blueprint fix-prop-coherence and fix-prop-projection-formula, projection diamond;
Stacks 0GL1 and 0E48 (blueprint: lem-sf-completed-projection-exchange-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralSystemRealization
namespace WeilConjectures.CompletedProjectionExchange

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {D : FiniteFieldDatum.{u}} (o : Operations l E) (ρ : Realizations l E D o)
  (Q : SixFunctorCompactifiedSquare D)

/-- The two concrete diamond paths have canonical integral generator realizations.
This only constructs paths; it asserts neither their equality nor input domain closure.
Source: projection diamond, generator-path portion of step 11 of
lem-sf-completed-projection-exchange-realization; Stacks 0941
(blueprint: lem-sf-completed-projection-exchange-paths).

Proof: expand each path into compactProjection, compactExchange, tensor pullback
and square-comparison letters. Use the corresponding BasicPair and
CanonicalIsoPair constructors at each letter. Close under the indicated pullback,
compact-support and tensor contexts, then compose the paths in their specified
order. For each ordinary-to-completed map, completionIso gives its inverse on the
supplied domain; use that inverse in CanonicalPair.basic. Intermediate domains are
subexpressions of the four supplied word domains, with their geometric proofs
retained. Thus no new boundedness assertion is part of this path-construction lemma.
Keep the open intermediate of every compact-support constructor. The resulting
integral composites are r₁ and r₂, with the two displayed CanonicalPair witnesses.
This uses no equality of the two system paths and no faithfulness of evaluation.
For identity letters the identity constructor applies; zero inputs give the same
composites of the unique maps involving zero objects.
-/
theorem completedProjectionExchangePaths
    (K : Integral l E Q.X.obj.left) (L : Integral l E Q.Y.obj.left)
    (g₀ : (word Q 0).geometric) (g₃ : (word Q 3).geometric)
    (h₀ : (word Q 0).domain l E o (inputs l E Q K L))
    (h₃ : (word Q 3).domain l E o (inputs l E Q K L))
    (_hwords : ∀ i : Fin 4, (word Q i).geometric ∧
      (word Q i).domain l E o (inputs l E Q K L)) :
    ∃ r₁ r₂ : integralSource l E Q K L ⟶ integralTarget l E Q K L,
      CanonicalPair l E o ρ.compositors ρ.openComparisons ρ.canonicalBridge ρ.properOpen
        ρ.ringedModels ρ.ringedOpenComparisons ρ.ringedProperOpen
        ((inputReduction l E (spaces Q)).obj (inputs l E Q K L))
        (inputs l E Q K L) (word Q 0) (word Q 3)
        (diamondLeft l E o ρ Q ((calculus l E Q.X.obj.left).reduction.obj K)
          ((calculus l E Q.Y.obj.left).reduction.obj L)) r₁ ∧
      CanonicalPair l E o ρ.compositors ρ.openComparisons ρ.canonicalBridge ρ.properOpen
        ρ.ringedModels ρ.ringedOpenComparisons ρ.ringedProperOpen
        ((inputReduction l E (spaces Q)).obj (inputs l E Q K L))
        (inputs l E Q K L) (word Q 0) (word Q 3)
        (diamondRight l E o ρ Q ((calculus l E Q.X.obj.left).reduction.obj K)
          ((calculus l E Q.Y.obj.left).reduction.obj L)) r₂ := by sorry

end WeilConjectures.CompletedProjectionExchange
