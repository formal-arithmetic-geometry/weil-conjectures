/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
import Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Finite local constancy after forgetting an abelian structure

Source: Stacks Project, Tags 03RU and 03RW(1),(2).
(blueprint: lem-weil-pbc-finite-local-abelian-forget).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Finite local constancy of an abelian sheaf can be tested on its underlying set sheaf.
Source: Stacks Project, Definitions 03RU and 03RW(1),(2), the finite-value comparison.
(blueprint: lem-weil-pbc-finite-local-abelian-forget)

Proof: Forget an abelian trivialization to obtain a set trivialization; the stalk functor
commutes with forgetting because filtered colimits of abelian groups are computed on sets.
Conversely, choose a locally constant set trivialization. Discard its empty members. At a
geometric point on each remaining member its constant set is the finite underlying stalk.
Transport the abelian operations of this stalk to the constant finite set. The unit, inverse,
and addition of the given sheaf are locally equal to these operations: each operation is a
map between finite constant sets, so its values on the finitely many input tuples are
locally constant. Refine the cover so all these finitely many values agree with the stalk
operations. The resulting set trivialization is an abelian trivialization. The group laws
hold on stalks, or on the transported finite group. Stalks commute with forgetting, so the
finiteness conditions agree. The empty scheme has the empty cover, and needs no chosen stalk.
-/
theorem finite_local_abelian_forget_iff {Y : Scheme.{u}}
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsFiniteLocallyConstantEtaleSheafOfSets
      ((sheafCompose Y.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G) ↔
    IsLocallyConstantSheaf G ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
        Finite (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj G) := by
  sorry

end AlgebraicGeometry.Scheme
