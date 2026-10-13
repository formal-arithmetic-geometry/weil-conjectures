module
public import Sheaf.AlgebraicGeometry.PicardUniversalRankMatch
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- The rank-match immersion is isomorphic over the base to a locally finitely presented
representative.  Decompose `S` into the open-and-closed loci on which the two relevant
cohomology ranks are fixed.  On each component, apply the finite-presentation rank-locus
construction to `E` and to its dual; their fibre product is an immersion locally of finite
presentation and represents the conjunction of the two rank conditions.  The componentwise
representatives agree on overlaps by the uniqueness part of the representing property, so
they glue to `j' : W' ⟶ S`.  The same representing property gives a unique isomorphism
`e : W ≅ W'` over `S`, hence `e.hom ≫ j' = j`.
(blueprint: lem-sc-picard-universal-rank-match-locus-lfp-iso) -/
theorem picardUniversalRankMatchLocus_exists_finitePresentation_iso
    {X S W : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (j : W ⟶ S) (hj : IsImmersion j)
    (hchar : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      (∃ h : T ⟶ W, h ≫ j = g) ↔ PicardUniversalRankMatch f E g) :
    ∃ (W' : Scheme.{u}) (j' : W' ⟶ S) (e : W ≅ W'),
      LocallyOfFinitePresentation j' ∧ e.hom ≫ j' = j := by
  sorry
end AlgebraicGeometry.Scheme
