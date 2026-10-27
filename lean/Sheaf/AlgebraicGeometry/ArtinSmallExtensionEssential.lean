module

public import Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory

/-! # Small extensions are split or essential

Source: Stacks Project, Formal Deformation Theory, Tag 06H0, part (4), including
complete Noetherian local sources (blueprint: lem-sfb-artin-small-extension-essential).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ArtinDeformation

/-- A small extension either has a section in the marked test category or is
essential for both Artinian and complete Noetherian local marked sources.
Source: Stacks Project, Formal Deformation Theory, Tag 06H0, part (4)
(blueprint: lem-sfb-artin-small-extension-essential).

Proof: Put I = ker(p). It is nonzero, principal, and killed by the maximal ideal
of B, hence one-dimensional over the marked residue field k. For a marked local
map g with p g surjective, let C be its image in B. Then B = C + I, and C maps
onto k. If g is not surjective and C meets I nontrivially, any nonzero x in that
intersection spans I over k. Lift each scalar to C; multiplication by that lift
shows I is contained in C, contradicting B = C + I and C different from B.
Thus C intersects I trivially, and p restricted to C is bijective onto A.
Its inverse gives an R-algebra section into B: additivity, multiplicativity,
the unit and compatibility with R follow from uniqueness of inverse images.
The equality p s = id and the residue compatibility of p show that s preserves
the marking, hence is local and is a test-category arrow. If there is no such
section, g must therefore be surjective. This argument uses only the residue
condition on its source, so it applies both to Artinian sources and to complete
Noetherian local sources. Finally a section cannot itself be surjective, since
otherwise p would be an isomorphism, contradicting its nonzero kernel; thus the
section case is not essential. The notions used throughout are those of
`def-sfb-artin-deformation-test-category`. -/
theorem smallExtension_section_or_essential
    (R k : Type u) [CommRing R] [IsNoetherianRing R] [Field k] [Algebra R k]
    [Algebra.FiniteType R k] {A B : TestCategory R k} (p : B ⟶ A)
    (hp : IsSmallExtension p) :
    (∃ s : A ⟶ B, s ≫ p = 𝟙 A) ∨
      ((∀ (D : TestCategory R k) (g : D ⟶ B),
          Function.Surjective ((map p).comp (map g)) → Function.Surjective (map g)) ∧
        ∀ (D : CompleteLocalAlgebra R k) (g : LocalMap D B),
          Function.Surjective ((map p).comp g.hom) → Function.Surjective g.hom) := sorry

end AlgebraicGeometry.ArtinDeformation
