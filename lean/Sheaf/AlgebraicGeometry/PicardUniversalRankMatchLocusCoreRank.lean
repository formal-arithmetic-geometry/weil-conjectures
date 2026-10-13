module

public import Sheaf.AlgebraicGeometry.PicardUniversalRankMatch
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

abbrev PicardUniversalRankMatchCoreCondition {X S T : Scheme.{u}} (f : X ⟶ S)
    (E : X.Modules) (g : T ⟶ S) : Prop :=
  PicardUniversalRankMatch f E g

/-- Fix the rank of E before constructing the two direct-image loci of that same rank.
Source: Stacks Project, Tag 0BDP, first three proof paragraphs.
(blueprint: lem-sc-picard-universal-rank-match-locus-core-rank)

The universal structure-pushforward hypothesis makes each fibre connected. The locally
constant rank of E is therefore constant on each fibre. Flatness and finite presentation
make f open, and properness makes f closed, so these ranks give open-and-closed base
strata S_r. On S_r the pullback of E has rank r after every base change. Proper flat
cohomology and base change give perfect direct-image complexes for E and its dual,
concentrated in nonnegative degrees. Apply the lowest-cohomology rank-r locus construction
to both complexes. Their fibre product represents the two universal direct-image rank-r
conditions. It is an immersion, and the third rank clause holds on this stratum by
construction. Conversely that clause fixes the same rank r, so a test morphism satisfying
all three clauses factors through both loci locally. Uniqueness of factorization through
an immersion glues these local maps. Finally glue the constructions over the disjoint
open-and-closed strata. Empty test schemes satisfy both sides vacuously.
-/
theorem exists_picardUniversalRankMatchLocus_core_rank {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (E : X.Modules) [E.IsFiniteLocallyFree] :
    ∃ (W : Scheme.{u}) (j : W ⟶ S),
      IsImmersion j ∧ ∀ {T : Scheme.{u}} (g : T ⟶ S),
        (∃ h : T ⟶ W, h ≫ j = g) ↔ PicardUniversalRankMatchCoreCondition f E g := by sorry

/-- The corrected core condition and PicardUniversalRankMatch have identical definitions:
both require the two direct images and the pulled-back E to have the same local rank
universally under further base change. Unfolding the two definitions proves the equivalence
by reflexivity; no rank of E is inferred from the ranks of its direct images.
Source: Stacks Project, Tag 0BDP, rank fixed before the two lowest-cohomology loci.
(blueprint: lem-sc-picard-universal-rank-match-locus-core-compat) -/
theorem picardUniversalRankMatchCoreCondition_iff {X S T : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f] (E : X.Modules)
    [E.IsFiniteLocallyFree] (g : T ⟶ S) :
    PicardUniversalRankMatchCoreCondition f E g ↔ PicardUniversalRankMatch f E g := by rfl
end AlgebraicGeometry.Scheme
