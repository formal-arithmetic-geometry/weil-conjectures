module

public import Sheaf.AlgebraicGeometry.PicardUniversalRankMatch
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus
import Sheaf.AlgebraicGeometry.PicardUniversalRankMatchConjunction

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
        (∃ h : T ⟶ W, h ≫ j = g) ↔ PicardUniversalRankMatchCoreCondition f E g := by
  have : (Modules.dual E).IsFiniteLocallyFree := Modules.IsFiniteLocallyFree.dual E
  obtain ⟨W₁, j₁, hj₁, hW₁⟩ := exists_picardUniversalSingleRankLocus f hO E E
  obtain ⟨W₂, j₂, hj₂, hW₂⟩ :=
    exists_picardUniversalSingleRankLocus f hO E (Modules.dual E)
  have : IsImmersion j₁ := hj₁
  have : IsImmersion j₂ := hj₂
  let j : pullback j₁ j₂ ⟶ S := pullback.fst j₁ j₂ ≫ j₁
  refine ⟨pullback j₁ j₂, j, inferInstance, ?_⟩
  intro T g
  change (∃ h : T ⟶ pullback j₁ j₂, h ≫ j = g) ↔ PicardUniversalRankMatch f E g
  have hmatch : PicardUniversalRankMatch f E g ↔
      PicardUniversalSingleRankMatch f E E g ∧
        PicardUniversalSingleRankMatch f E (Modules.dual E) g := by
    constructor
    · intro hR
      constructor
      · intro T' h t
        obtain ⟨U, ht, r, hE, _, hr⟩ := hR h t
        exact ⟨U, ht, r, hE, hr⟩
      · intro T' h t
        obtain ⟨U, ht, r, _, hd, hr⟩ := hR h t
        exact ⟨U, ht, r, hd, hr⟩
    · rintro ⟨hE, hd⟩
      exact picardUniversalRankMatch_of_singleRankMatch f hO E g hE hd
  rw [hmatch]
  constructor
  · rintro ⟨h, hh⟩
    constructor
    · exact (hW₁ g).mp ⟨h ≫ pullback.fst j₁ j₂, by
        simpa only [Category.assoc] using hh⟩
    · exact (hW₂ g).mp ⟨h ≫ pullback.snd j₁ j₂, by
        rw [Category.assoc, ← pullback.condition]
        exact hh⟩
  · rintro ⟨h₁, h₂⟩
    obtain ⟨a, ha⟩ := (hW₁ g).mpr h₁
    obtain ⟨b, hb⟩ := (hW₂ g).mpr h₂
    refine ⟨pullback.lift a b (ha.trans hb.symm), ?_⟩
    dsimp only [j]
    rw [← Category.assoc, pullback.lift_fst, ha]

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
