/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker J1
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Sheaf.AlgebraicGeometry.EtaleFieldGsets
public import Sheaf.RepresentationTheory.DiscreteContinuousRep
import Sheaf.AlgebraicGeometry.AbelianSheavesGModulesTransport
import Mathlib.Algebra.Category.Grp.LeftExactFunctor
import Mathlib.Algebra.Category.Grp.AB

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
  dsimp
  intro Eset j
  obtain ⟨E, ⟨beta⟩⟩ := abelianSheaves_transport.{u, v} J G Eset
  let U := ObjectProperty.ι
    (fun X : Rep.{max (u + 1) v} ℤ G ↦ ∀ x : X.V, IsOpen {g : G | X.ρ g x = x})
  let V := ObjectProperty.ι (ContAction.IsDiscrete (V := Type (max (u + 1) v)) (G := G))
    ⋙ ObjectProperty.ι (Action.IsContinuous (V := Type (max (u + 1) v)) (G := G))
  let H := E.functor ⋙ U ⋙ Rep.RepToAction ℤ G ⋙
    Action.forget (ModuleCat.{max (u + 1) v} ℤ) G ⋙
    forget₂ (ModuleCat.{max (u + 1) v} ℤ) AddCommGrpCat
  let : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, max (u + 1) v, u, max (u + 1) v} _
  let : AB5OfSize.{u, u} AddCommGrpCat.{max (u + 1) v} :=
    AB5OfSize_shrink.{u, u, max (u + 1) v, max (u + 1) v} _
  let : Limits.HasFiniteBiproducts (Sheaf J AddCommGrpCat.{max (u + 1) v}) :=
    Limits.HasFiniteBiproducts.of_hasFiniteProducts
  let Q := sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v})
  let gamma := p.sheafFiberCompIso (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v})
  let alpha : H ⋙ CategoryTheory.forget AddCommGrpCat ≅
      p.sheafFiber ⋙ CategoryTheory.forget AddCommGrpCat :=
    Functor.isoWhiskerRight beta (Action.forget (Type (max (u + 1) v)) G) ≪≫
      Functor.associator Q (Eset.functor ⋙ V) (Action.forget _ G) ≪≫
      Functor.isoWhiskerLeft Q j ≪≫ gamma
  -- The stalk comparison proves left exactness; transport need not supply it.
  have : Limits.PreservesFiniteLimits (H ⋙ CategoryTheory.forget AddCommGrpCat) :=
    Limits.preservesFiniteLimits_of_natIso alpha.symm
  have : Limits.PreservesFiniteLimits H :=
    Limits.preservesFiniteLimits_of_reflects_of_preserves H
      (CategoryTheory.forget AddCommGrpCat)
  let L := AddCommGrpCat.leftExactFunctorForgetEquivalence
    (Sheaf J AddCommGrpCat.{max (u + 1) v})
  -- Full faithfulness lifts alpha together with its exact underlying map.
  let i' : LeftExactFunctor.of H ≅ LeftExactFunctor.of p.sheafFiber :=
    L.functor.preimageIso (ObjectProperty.isoMk _ alpha)
  let i : H ≅ p.sheafFiber := (ObjectProperty.ι _).mapIso i'
  refine ⟨E, i, ⟨beta⟩, ?_⟩
  have hi : Functor.isoWhiskerRight i (CategoryTheory.forget AddCommGrpCat) = alpha := by
    have h := L.functor.map_preimage (X := LeftExactFunctor.of H)
      (Y := LeftExactFunctor.of p.sheafFiber) (ObjectProperty.isoMk _ alpha).hom
    have h' := congrArg (fun f ↦ f.hom) h
    apply Iso.ext
    exact h'
  intro F g X x x' z hset
  have hif (a : (E.functor.obj F).obj.V) :
      (i.hom.app F) a = (gamma.hom.app F)
        ((j.hom.app (Q.obj F)) ((beta.hom.app F).hom a)) := by
    have h := congrArg (fun t ↦ t.hom.app F) hi
    exact ConcreteCategory.congr_hom h a
  have hgamma (y : p.fiber.obj X) :
      (gamma.hom.app F) (p.toPresheafFiber X y (Q.obj F).obj z) =
        p.toPresheafFiber X y F.obj z := by
    exact ConcreteCategory.congr_hom
      (p.toPresheafFiber_presheafFiberCompIso_hom_app
        (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}) X y F.obj) z
  have hcomm (a : (E.functor.obj F).obj.V) :
      (beta.hom.app F).hom ((E.functor.obj F).obj.ρ g a) =
        (Eset.functor.obj (Q.obj F)).obj.obj.ρ g ((beta.hom.app F).hom a) := by
    exact ConcreteCategory.congr_hom ((beta.hom.app F).comm g) a
  have hinv : (beta.hom.app F).hom
      ((i.inv.app F) (p.toPresheafFiber X x F.obj z)) =
        (j.inv.app (Q.obj F)) (p.toPresheafFiber X x (Q.obj F).obj z) := by
    apply (ConcreteCategory.bijective_of_isIso (j.hom.app (Q.obj F))).1
    apply (ConcreteCategory.bijective_of_isIso (gamma.hom.app F)).1
    rw [← hif]
    simp only [Iso.inv_hom_id_app_apply]
    exact (hgamma x).symm
  erw [hif, hcomm, hinv, hset]
  exact hgamma x'

end AlgebraicGeometry.Scheme
