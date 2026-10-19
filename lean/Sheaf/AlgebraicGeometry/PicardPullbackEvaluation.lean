/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus
import Sheaf.AlgebraicGeometry.FiniteLocallyFreeTensorUnit
import Sheaf.AlgebraicGeometry.PicardPullbackLocalRanks
import Sheaf.AlgebraicGeometry.PicardPullbackBaseChange
import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Rank and evaluation for a module pulled back from the base

Source: Stacks Project, Tag 0BDP, projection-formula paragraph.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A module pulled back from a finite locally free base module satisfies the universal
rank condition, and its canonical evaluation map is invertible. This implication does
not construct or represent any locus. Source: Stacks Project, Tag 0BDP, paragraph using
Tag 01E8 (the projection formula for finite locally free modules).
(blueprint: lem-sc-picard-pullback-evaluation)

Proof: Put p = X_T → T and q = X_T → X. The projection formula and the unit isomorphism
at O_T give p_*p^*N ≅ N ⊗ p_*O_X_T ≅ N. This identification is the adjunction unit at N:
check on an open where N is finite free, where the unit is a finite direct sum of the
unit at O_T. Consequently this unit is invertible. The triangle identity then makes
the counit at p^*N invertible. Naturality transports invertibility along the supplied
isomorphism q^*E ≅ p^*N. The direct image of q^*E is thus isomorphic to N and is finite
locally free. After any further base change h : T' → T, pull back the supplied
isomorphism through the cartesian-square identifications, obtaining q'^*E ≅ p'^*h^*N.
Dualizing commutes with pullback for finite locally free modules, so the same assertion
holds for the dual and h^*N^dual. Apply the projection formula using the hypothesis at
h ≫ g to identify the two direct images with h^*N and its dual. On a neighbourhood U of
each point t of T', choose a frame of h^*N of finite rank r; its dual has the dual frame
of the same rank. Pulling that frame up to X_U shows that q_U^*E also has rank r. These
are exactly the three rank assertions in PicardDirectImageRankCondition. Finally the
canonical base-change maps are isomorphisms: under the projection-formula identifications
they are the identity on the pullback of N and its dual, as follows from their defining
adjunction units. This gives the remaining conjunct for every h. The empty
base has no points to check, and finite free rank zero uses the empty frame. -/
theorem picard_rankCondition_and_isIso_counit_of_pullback {X S T : Scheme.{u}}
    (f : X ⟶ S)
    (hO : ∀ {T' : Scheme.{u}} (g' : T' ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g'))).unit.app
          (SheafOfModules.unit T'.ringCatSheaf)))
    (E : X.Modules) [E.IsFiniteLocallyFree] (g : T ⟶ S) (N : T.Modules) [N.IsFiniteLocallyFree]
    (e : Nonempty ((Modules.tensorPullback (pullback.fst f g)).obj E ≅
      (Modules.tensorPullback (pullback.snd f g)).obj N)) :
    PicardDirectImageRankCondition f E g ∧
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).counit.app
          ((Modules.tensorPullback (pullback.fst f g)).obj E)) := by
  obtain ⟨e⟩ := e
  let p := pullback.snd f g
  let L := Modules.tensorPullback p
  let R := Modules.pushforward p
  let adj := Classical.choose (Modules.exists_tensorPullbackAdjunction p)
  have hη : IsIso (adj.unit.app N) :=
    isIso_tensorPullback_unit_of_finiteLocallyFree p (hO g) N
  let d : N ≅ R.obj ((Modules.tensorPullback (pullback.fst f g)).obj E) :=
    asIso (adj.unit.app N) ≪≫ (R.mapIso e).symm
  have hfree : (R.obj
      ((Modules.tensorPullback (pullback.fst f g)).obj E)).IsFiniteLocallyFree :=
    SheafOfModules.IsFiniteLocallyFree.of_iso.{u, u, u} d
  have hε : IsIso (adj.counit.app (L.obj N)) := by
    have : IsIso (L.map (adj.unit.app N) ≫ adj.counit.app (L.obj N)) := by
      change IsIso ((Modules.tensorPullback p).map (adj.unit.app N) ≫
        adj.counit.app ((Modules.tensorPullback p).obj N))
      rw [adj.left_triangle_components N]
      infer_instance
    exact IsIso.of_isIso_comp_left (L.map (adj.unit.app N)) _
  have hεE : IsIso (adj.counit.app
      ((Modules.tensorPullback (pullback.fst f g)).obj E)) := by
    have : IsIso (adj.counit.app
        ((Modules.tensorPullback (pullback.fst f g)).obj E) ≫ e.hom) := by
      rw [← adj.counit_naturality e.hom]
      infer_instance
    exact IsIso.of_isIso_comp_right _ e.hom
  exact ⟨⟨hfree, picard_pullback_local_ranks f hO E g N ⟨e⟩,
    picard_pullback_base_change f hO E g N ⟨e⟩⟩, hεE⟩

end AlgebraicGeometry.Scheme
