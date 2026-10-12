/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker Y2
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Sheaf.AlgebraicGeometry.EtaleFieldGsets
public import Sheaf.RepresentationTheory.DiscreteContinuousRep
import Sheaf.CategoryTheory.EquivalenceInternalModule
import Sheaf.CategoryTheory.InternalModule

/-!
# Transport of abelian group objects across a set-valued sheaf equivalence

Source: Stacks Project, Tag 04JQ, proof of lemma-equivalence-abelian-sheaves-point.
(blueprint: lem-exc-abelian-sheaves-gmodules-transport)
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Tag 04JQ, proof of
`lemma-equivalence-abelian-sheaves-point` (and Tags 03QT, 03QW).
(blueprint: lem-exc-abelian-sheaves-gmodules-transport).

Proof: Identify abelian-group-valued sheaves with internal integer modules in
set-valued sheaves: forgetting the operations preserves and reflects the sheaf
condition, and products are computed on sections. Identify discrete continuous
integer representations with internal integer modules in discrete continuous
G-sets: equivariance of addition, negation and integer multiplication is precisely
linearity of the action; continuity of the discrete action is precisely openness
of all stabilizers. Apply equivalence_induces_internalModules to Eset and compose
with these two identifications. Its equality of underlying functors gives beta.
On morphisms the identifications send operation-preserving set maps to additive
maps, which are automatically integer-linear, and the inverse does the reverse.
The quasi-inverse obtained from Eset.inverse transports the operations back;
the unit and counit preserve all the operations by their naturality. Thus these
are inverse equivalences, with an equivariant comparison beta on underlying sets.
No geometric point or stalk comparison is used here.
The zero group and trivial action are allowed. -/
theorem abelianSheaves_transport
    {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    let D := Rep.DiscreteContinuousRep.{0, u, max (u + 1) v} ℤ G
    let U : D ⥤ Rep.{max (u + 1) v} ℤ G := ObjectProperty.ι _
    let V := ObjectProperty.ι (ContAction.IsDiscrete (V := Type (max (u + 1) v)) (G := G))
      ⋙ ObjectProperty.ι (Action.IsContinuous (V := Type (max (u + 1) v)) (G := G))
    ∀ (Eset : Sheaf J (Type (max (u + 1) v)) ≌
        DiscreteContAction (Type (max (u + 1) v)) G),
    ∃ (E : Sheaf J AddCommGrpCat.{max (u + 1) v} ≌ D),
      Nonempty
        (E.functor ⋙ U ⋙ Rep.RepToAction ℤ G ⋙
            (CategoryTheory.forget (ModuleCat.{max (u + 1) v} ℤ)).mapAction G ≅
          sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}) ⋙
            Eset.functor ⋙ V) := by
  sorry

end AlgebraicGeometry.Scheme
