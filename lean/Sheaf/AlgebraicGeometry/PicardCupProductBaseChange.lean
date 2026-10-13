/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PicardCupProductMap
public import Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus
import Sheaf.AlgebraicGeometry.PullbackDualFiniteLocallyFree
import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapPasting

/-! # Base change of the degree-zero cup-product transpose

Source: Stacks Project, Tag 0BDP, the compatibility with arbitrary change of base
in the penultimate paragraph and cup product in the final paragraph.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The cup-product transpose commutes with arbitrary base change up to isomorphisms
of its source and target. This asserts a commuting square of actual morphisms;
it makes no assertion about the invertibility of an evaluation counit.

Source: Stacks Project, Tag 0BDP, final two paragraphs.
(blueprint: lem-sc-picard-cup-product-base-change-square)

Proof: Write N = p_*q^*E and D = p_*q^*(E^dual) on W, and N_T,D_T for the analogous
modules over T. The final conjunct of hR makes the canonical base-change maps for
N and D invertible. Compare the iterated fibre product with X_T by its canonical
cartesian isomorphism, and use the pullback composition isomorphisms. The map for
D then gives a : h^*D ≅ D_T; the map for N gives h^*N ≅ N_T. Since hR makes N
finite locally free, pullback of its dual identifies h^*(N^dual) with (h^*N)^dual.
Compose this with the inverse transpose of h^*N ≅ N_T to get b.
To check the square, uncurry the two composites. Both become the map obtained by
pulling evaluation E tensor E^dual → O_X to X_T and pushing it to T, followed by
the inverse structure-sheaf unit. The base-change maps were defined as adjoint
mates of the pullback units. Substituting those definitions and using the unit
and counit triangle identities identifies their composites with the same pulled
back evaluation map. Pullback composition and tensor comparisons commute by
naturality and associativity; structure units commute by their section formula
m ↦ 1 tensor m. Hence the uncurried maps agree and curry is injective.
This construction does not use reducedness or a flatness assumption on h. On a
rank-zero component all pairings are the unique maps between zero objects; the
empty base has only the unique sheaf morphisms, with the same identity. -/
theorem picardCupProduct_baseChange_square
    {X S W T : Scheme.{u}} (f : X ⟶ S) (E : X.Modules) [E.IsFiniteLocallyFree]
    (j : W ⟶ S) (h : T ⟶ W)
    (hO : IsIso ((Classical.choose
      (Modules.exists_tensorPullbackAdjunction (pullback.snd f j))).unit.app
        (SheafOfModules.unit W.ringCatSheaf)))
    (hOT : IsIso ((Classical.choose
      (Modules.exists_tensorPullbackAdjunction (pullback.snd f (h ≫ j)))).unit.app
        (SheafOfModules.unit T.ringCatSheaf)))
    (hR : PicardDirectImageRankCondition f E j) :
    ∃ (a : (Modules.tensorPullback h).obj
        ((Modules.pushforward (pullback.snd f j)).obj
          ((Modules.tensorPullback (pullback.fst f j)).obj (Modules.dual E))) ≅
        (Modules.pushforward (pullback.snd f (h ≫ j))).obj
          ((Modules.tensorPullback (pullback.fst f (h ≫ j))).obj (Modules.dual E)))
      (b : (Modules.tensorPullback h).obj
        (Modules.dual ((Modules.pushforward (pullback.snd f j)).obj
          ((Modules.tensorPullback (pullback.fst f j)).obj E))) ≅
        Modules.dual ((Modules.pushforward (pullback.snd f (h ≫ j))).obj
          ((Modules.tensorPullback (pullback.fst f (h ≫ j))).obj E))),
      (Modules.tensorPullback h).map (picardCupProductMap f E j hO) ≫ b.hom =
        a.hom ≫ picardCupProductMap f E (h ≫ j) hOT := by sorry

end AlgebraicGeometry.Scheme
