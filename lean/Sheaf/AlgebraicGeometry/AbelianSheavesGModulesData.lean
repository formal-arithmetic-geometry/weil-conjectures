/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker J1
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Sheaf.AlgebraicGeometry.EtaleFieldGsets
public import Sheaf.RepresentationTheory.DiscreteContinuousRep
import Sheaf.CategoryTheory.EquivalenceInternalModule

/-!
# Lifting a stalk equivalence to abelian group objects

Source: Stacks Project, Tag 04JQ, the formal transport step.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Tag 04JQ, proof of
`lemma-equivalence-abelian-sheaves-point`.
(blueprint: lem-exc-abelian-sheaves-gmodules-core).

Proof: Equip the set-valued sheaf category and discrete continuous action category
with their cartesian products. An equivalence preserves those products, and hence
transports commutative group objects and their morphisms in both directions.
Commutative group objects in set-valued sheaves are abelian-group-valued sheaves:
products and the sheaf condition are computed on underlying sets. Commutative group
objects in discrete continuous actions are abelian groups with equivariant operations;
equivalently these are integer representations with open stabilizers. The transported
operations give the equivalence E and the underlying-action comparison. The natural
isomorphism j respects the transported operations, since stalks commute with finite
products; thus it lifts to an additive isomorphism i. Choose these comparisons using
the canonical comparison gamma between the underlying set of an additive stalk and
the set-valued stalk (Mathlib's Point.sheafFiberCompIso). It identifies germs of each
section. If beta is the underlying-action comparison, choose i so that
gamma composed with forget(i) equals j composed with forget(beta). Equivariance of
beta then identifies the actions conjugated by i and j under gamma. Apply gamma to
the desired additive germ equality; the supplied set-valued equality proves its image.
Injectivity of gamma gives the final implication.
The argument permits the zero group and makes no nonemptiness assumption on sections. -/
theorem abelianSheaves_equiv_discreteGModules_core
    {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (p : GrothendieckTopology.Point.{u} J)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    let D := Rep.DiscreteContinuousRep.{0, u, max (u + 1) v} ℤ G
    let U : D ⥤ Rep.{max (u + 1) v} ℤ G := ObjectProperty.ι _
    let V := ObjectProperty.ι (ContAction.IsDiscrete (V := Type (max (u + 1) v)) (G := G))
      ⋙ ObjectProperty.ι (Action.IsContinuous (V := Type (max (u + 1) v)) (G := G))
    ∀ (Eset : Sheaf J (Type (max (u + 1) v)) ≌
        DiscreteContAction (Type (max (u + 1) v)) G)
      (j : Eset.functor ⋙ V ⋙ Action.forget (Type (max (u + 1) v)) G ≅ p.sheafFiber),
    ∃ (E : Sheaf J AddCommGrpCat.{max (u + 1) v} ≌ D)
      (i : E.functor ⋙ U ⋙ Rep.RepToAction ℤ G ⋙
          Action.forget (ModuleCat.{max (u + 1) v} ℤ) G ⋙
          forget₂ (ModuleCat.{max (u + 1) v} ℤ) AddCommGrpCat ≅ p.sheafFiber),
      Nonempty
        (E.functor ⋙ U ⋙ Rep.RepToAction ℤ G ⋙
            (CategoryTheory.forget (ModuleCat.{max (u + 1) v} ℤ)).mapAction G ≅
          sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}) ⋙
            Eset.functor ⋙ V) ∧
      ∀ (F : Sheaf J AddCommGrpCat.{max (u + 1) v}) (g : G)
          (X : C) (x x' : p.fiber.obj X) (z : F.obj.obj (op X)),
        let Fset := (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v})).obj F
        (j.hom.app Fset) ((Eset.functor.obj Fset).obj.obj.ρ g
          ((j.inv.app Fset) (p.toPresheafFiber X x Fset.obj z))) =
            p.toPresheafFiber X x' Fset.obj z →
        (i.hom.app F) ((E.functor.obj F).obj.ρ g
          ((i.inv.app F) (p.toPresheafFiber X x F.obj z))) =
            p.toPresheafFiber X x' F.obj z := by
  sorry

end AlgebraicGeometry.Scheme
