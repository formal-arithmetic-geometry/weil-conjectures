/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import Sheaf.AlgebraicGeometry.PerfectLowestCohomologyLocus

/-! # The simultaneous rank-matched direct-image locus

Source: Stacks Project, Tag 0BDP, rank decomposition and lowest-cohomology paragraphs.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The direct image is finite locally free, and after every further base change the
module and the two direct images have the same locally constant rank. Both canonical
base-change maps are invertible. This is a concrete
condition on actual pushforwards, not a choice of a derived-category model or a locus.
Source: Stacks Project, Tag 0BDP, simultaneous degree-zero rank conditions.
(blueprint: def-sc-picard-direct-image-rank-condition) -/
def PicardDirectImageRankCondition {X S T : Scheme.{u}} (f : X ⟶ S)
    (E : X.Modules) (g : T ⟶ S) : Prop :=
  ((Modules.pushforward (pullback.snd f g)).obj
    ((Modules.tensorPullback (pullback.fst f g)).obj E)).IsFiniteLocallyFree ∧
  (∀ {T' : Scheme.{u}} (h : T' ⟶ T) (t : T'),
    ∃ U : T'.Opens, t ∈ U ∧ ∃ r : ℕ,
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback U.ι).obj
          ((Modules.pushforward (pullback.snd f (h ≫ g))).obj
            ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj E))) r ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback U.ι).obj
          ((Modules.pushforward (pullback.snd f (h ≫ g))).obj
            ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj
              (Modules.dual E)))) r ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback (pullback.fst f (U.ι ≫ h ≫ g))).obj E) r) ∧
  ∀ {T' : Scheme.{u}} (h : T' ⟶ T),
    IsIso (Modules.moduleBaseChangeMap (pullback.snd f g)
      (pullback.snd (pullback.snd f g) h) h (pullback.fst (pullback.snd f g) h)
      pullback.condition ((Modules.tensorPullback (pullback.fst f g)).obj E)) ∧
    IsIso (Modules.moduleBaseChangeMap (pullback.snd f g)
      (pullback.snd (pullback.snd f g) h) h (pullback.fst (pullback.snd f g) h)
      pullback.condition ((Modules.tensorPullback (pullback.fst f g)).obj (Modules.dual E)))

/-- The simultaneous universal rank condition is represented by a finitely presented
immersion. This stops before the cup-product or evaluation isomorphism condition.
Source: Stacks Project, Tag 0BDP, first three proof paragraphs, using Tags 0B91 and 0BDL.
(blueprint: lem-sc-picard-direct-image-rank-locus)

Proof: The structure-pushforward assumption makes each fibre nonempty and connected:
its global functions are its residue field, which has no nontrivial idempotents. The
rank loci of E in X are open and closed; flat finite presentation makes their images
open, and properness makes their images closed. Connectedness and nonemptiness give a
disjoint open-and-closed rank decomposition of S. Work on the component with rank r.
Both E and its dual are finitely presented and relatively flat. Their derived direct
images are perfect and commute with arbitrary base change by Tag 0B91. Their negative
cohomology vanishes after all base changes, so locally their Tor amplitude is [0,b].
Apply Tag 0BDL to degree zero and rank r for both complexes. Take the fibre product of
these two finitely presented immersions. Its universal property says exactly that both
ordinary direct images are universally locally free of rank r; the pulled-back E already
has rank r on this component. On this locus degree-zero cohomology commutes with base
change via the canonical maps: in the finite-free model beginning in degree zero,
the outgoing degree-zero matrix vanishes on the rank locus, so degree-zero cohomology
is the first free term. The canonical cohomology base-change map is then the identity
on its scalar extension. Under the derived direct-image comparison this is the ordinary
adjoint-defined module base-change map. This gives the final conjunct of the condition.
Conversely the
displayed condition, restricted to this rank component, is the
universal rank-r condition of Tag 0BDL for both complexes. Thus the fibre product
represents it, including for nonreduced test schemes. Glue these constructions across
the open cover used for Tor amplitude by their unique universal identifications, and
take their disjoint union over the open-and-closed rank components. Immersion and finite
presentation are local on the target; a quasi-compact target open meets only finitely
many rank components. The resulting immersion is quasi-compact and is separated, hence
quasi-separated. The direct image itself is finite locally free by the same local models.
For rank zero the empty matrix gives the full component; empty schemes are vacuous. -/
theorem exists_picardDirectImageRankLocus {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (E : X.Modules) [E.IsFiniteLocallyFree] :
    ∃ (W : Scheme.{u}) (j : W ⟶ S),
      IsImmersion j ∧ LocallyOfFinitePresentation j ∧ QuasiCompact j ∧
      QuasiSeparated j ∧ ∀ {T : Scheme.{u}} (g : T ⟶ S),
        (∃ h : T ⟶ W, h ≫ j = g) ↔ PicardDirectImageRankCondition f E g := by
  sorry

end AlgebraicGeometry.Scheme
