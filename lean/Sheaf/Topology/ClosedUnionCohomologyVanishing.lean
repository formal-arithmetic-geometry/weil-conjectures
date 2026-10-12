/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Category.Grp.AB
import Sheaf.Topology.ClosedImmersionPushforwardCohomology
import Sheaf.Topology.NoetherianOpenClosedCohomologySequence

/-! # Gluing universal vanishing over two closed subsets

Source: Stacks Project, Proposition 02UZ, component-reduction argument.
(blueprint: lem-sc-closed-union-cohomology-vanishing).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat

/-- Universal degree-q vanishing is stable under a binary union of closed subsets.
Source: Stacks Project, Proposition 02UZ, component-reduction argument, using
Lemma 02UV and the open-closed short exact sequence of Modules, Lemma 02UT.
(blueprint: lem-sc-closed-union-cohomology-vanishing).

Proof: Work on T = Z ∪ W, which is Noetherian as a subspace of X. Regard Z and
W as closed subspaces of T with their unchanged intrinsic topologies. Put
U = T \ Z. The open-closed short exact sequence for F has right term the
closed pushforward of F restricted to Z, whose degree-q cohomology is zero
by closed-pushforward comparison and hZ. Its left term j_!j^*F is the closed
pushforward of a sheaf G on closure(U). Since W is closed and contains U,
closure(U) is contained in W. Push G forward along the closed inclusion
closure(U) → W. Hypothesis hW and closed-pushforward comparison imply that
H^q(closure(U),G) is zero, hence the left term has zero degree-q cohomology
on T. Exactness at H^q(T,F) now makes it zero. For q=0 use the initial left
exact part of the same sequence. Empty, equal, and nested Z and W cause no
exception: the inclusions and support statement still apply. -/
theorem cohomology_vanishing_of_closed_union
    (X : Type u) [TopologicalSpace X] [NoetherianSpace X]
    (Z W : Closeds X) (q : ℕ)
    (hZ : ∀ G : Sheaf (Opens.grothendieckTopology (Z : Set X)) AddCommGrpCat.{u},
      IsZero (Sheaf.H' G q (⊤ : Opens (Z : Set X))))
    (hW : ∀ G : Sheaf (Opens.grothendieckTopology (W : Set X)) AddCommGrpCat.{u},
      IsZero (Sheaf.H' G q (⊤ : Opens (W : Set X))))
    (F : Sheaf (Opens.grothendieckTopology ((Z ⊔ W : Closeds X) : Set X))
      AddCommGrpCat.{u}) :
    IsZero (Sheaf.H' F q (⊤ : Opens ((Z ⊔ W : Closeds X) : Set X))) := by sorry

end TopCat
