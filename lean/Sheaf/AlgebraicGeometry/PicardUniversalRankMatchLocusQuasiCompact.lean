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
/-- The representing immersion in Tag 0BDP is quasi-compact.
Source: Stacks Project, Tag 0BDP, rank decomposition and quasi-compactness paragraphs.
(blueprint: lem-sc-picard-universal-rank-match-locus-qc)
This is the quasi-compact part of the structural finiteness argument.  The rank
decomposition of the base has only finitely many components meeting any quasi-compact
target open.  On each such component the two lowest-cohomology rank loci are finitely
presented immersions, hence quasi-compact, and their fibre product is quasi-compact.
The componentwise pieces glue along the universal property; a finite union of these
quasi-compact pieces is quasi-compact, and quasi-compactness of an immersion is local
on the target.  This proves the displayed property for `j`.
-/
theorem picardUniversalRankMatchLocus_quasiCompact {X S W : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (j : W ⟶ S) (hj : IsImmersion j)
    (hchar : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      (∃ h : T ⟶ W, h ≫ j = g) ↔ PicardUniversalRankMatch f E g) :
    QuasiCompact j := by sorry
end AlgebraicGeometry.Scheme
