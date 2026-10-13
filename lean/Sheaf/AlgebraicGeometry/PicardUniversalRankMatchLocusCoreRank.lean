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

def PicardUniversalRankMatchCoreCondition {X S T : Scheme.{u}} (f : X ⟶ S)
    (E : X.Modules) (g : T ⟶ S) : Prop :=
  ∀ {T' : Scheme.{u}} (h : T' ⟶ T) (t : T'),
    ∃ U : T'.Opens, t ∈ U ∧ ∃ r : ℕ,
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback U.ι).obj
          ((Modules.pushforward (pullback.snd f (h ≫ g))).obj
            ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj E))) r ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback U.ι).obj
          ((Modules.pushforward (pullback.snd f (h ≫ g))).obj
            ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj
              (Modules.dual E)))) r

/-- Rank decomposition and the fibre product of the two lowest-cohomology loci produce an
immersion representing the two direct-image rank clauses. Source: Stacks Project, Tag 0BDP,
first three proof paragraphs. (blueprint: lem-sc-picard-universal-rank-match-locus-core-rank)
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

/-- On the rank locus, the pulled-back module has the common rank; this is the final
identification in Tag 0BDP. Source: Stacks Project, Tag 0BDP.
(blueprint: lem-sc-picard-universal-rank-match-locus-core-compat) -/
theorem picardUniversalRankMatchCoreCondition_iff {X S T : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f] (E : X.Modules)
    [E.IsFiniteLocallyFree] (g : T ⟶ S) :
    PicardUniversalRankMatchCoreCondition f E g ↔ PicardUniversalRankMatch f E g := by sorry
end AlgebraicGeometry.Scheme
