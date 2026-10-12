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
/-- The representing immersion in Tag 0BDP is locally of finite presentation.
Source: Stacks Project, Tag 0BDP, rank decomposition and finite-presentation paragraphs.
(blueprint: lem-sc-picard-universal-rank-match-locus-lfp)
This is the locally finite-presentation part of the structural finiteness argument.  Decompose
the universal rank condition into the open-and-closed rank components of the base.  On each
component, finite local freeness of the module and its dual, together with proper flat finite
presentation of the family, gives the lowest-cohomology rank loci, each an immersion locally of
finite presentation.  Their fibre product represents the conjunction of the two rank conditions.
The componentwise immersions agree on overlaps by the universal property and hence glue; local
finite presentation is local on the target, yielding the displayed property for `j`.
-/
theorem picardUniversalRankMatchLocus_locallyOfFinitePresentation {X S W : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (j : W ⟶ S) (hj : IsImmersion j)
    (hchar : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      (∃ h : T ⟶ W, h ≫ j = g) ↔ PicardUniversalRankMatch f E g) :
    LocallyOfFinitePresentation j := by sorry
end AlgebraicGeometry.Scheme
