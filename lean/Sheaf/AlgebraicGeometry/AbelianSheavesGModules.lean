/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker J1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
public import Sheaf.AlgebraicGeometry.EtaleFieldGsets
public import Sheaf.RepresentationTheory.DiscreteContinuousRep
import Sheaf.AlgebraicGeometry.EtaleSheaves
import Sheaf.AlgebraicGeometry.Sites.EtaleSheavesGsetsPoint
import Sheaf.CategoryTheory.EquivalenceInternalModule

/-!
# Abelian etale sheaves on a field and discrete Galois modules

Source: Stacks Project, Etale Cohomology, Tag 04JQ,
`lemma-equivalence-abelian-sheaves-point`, deduced from Tag 03QT
(blueprint: lem-exc-abelian-sheaves-gmodules).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Source: Stacks Project, Etale Cohomology, Tags 04JQ and 03QT
(blueprint: lem-exc-abelian-sheaves-gmodules).
The geometric stalk at the chosen algebraically closed extension is an equivalence from
abelian etale sheaves to discrete Galois modules. The abelian-group-valued stalk comparison
preserves
addition, zero, and inverse. The action-valued comparison expresses compatibility with
forgetting to the sheaf-of-sets/G-set equivalence. The last formula specifies the canonical
Galois action: a germ represented at a lift `x` is sent to the same section at `τ ∘ x`,
for any extension `τ` of `g`.

Proof:
1. The underlying set-valued stalk equivalence is
`lem-exc-etale-sheaves-gsets-point`, using the geometric stalk
`def-weil-pbc-geometric-stalks` and the small etale sheaves
`def-weil-pbc-etale-sheaves`.
2. An abelian sheaf is a sheaf of sets with a commutative group law. A discrete Galois
module is a discrete G-set with equivariant addition, zero, and inverse. The equivalence
preserves finite products, so transport these operations and their identities across it
(`lem-pod-equivalence-induces-module-objects`, with the ring of integers). Transport
morphisms in the same way; the quasi-inverse transports the structures back. This gives
the abelian equivalence, with the underlying comparison and all group operations. -/
theorem abelianSheaves_equiv_discreteGModules
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] :
    let S := Spec (.of K)
    let J := S.smallEtaleTopology
    let s := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
    let p := pointSmallEtale s
    let G := Gal(Ks/K)
    let D := Rep.DiscreteContinuousRep.{0, u, max (u + 1) v} ℤ G
    let U : D ⥤ Rep.{max (u + 1) v} ℤ G := ObjectProperty.ι _
    let V := ObjectProperty.ι (ContAction.IsDiscrete (V := Type (max (u + 1) v)) (G := G))
      ⋙ ObjectProperty.ι (Action.IsContinuous (V := Type (max (u + 1) v)) (G := G))
    ∃ (E : Sheaf J AddCommGrpCat.{max (u + 1) v} ≌ D)
      (Eset : Sheaf J (Type (max (u + 1) v)) ≌
        DiscreteContAction (Type (max (u + 1) v)) G)
      (i : E.functor ⋙ U ⋙ Rep.RepToAction ℤ G ⋙
          Action.forget (ModuleCat.{max (u + 1) v} ℤ) G ⋙
          forget₂ (ModuleCat.{max (u + 1) v} ℤ) AddCommGrpCat ≅
        p.sheafFiber)
      (j : Eset.functor ⋙ V ⋙ Action.forget (Type (max (u + 1) v)) G ≅
        p.sheafFiber),
      Nonempty
        (E.functor ⋙ U ⋙ Rep.RepToAction ℤ G ⋙
            (CategoryTheory.forget (ModuleCat.{max (u + 1) v} ℤ)).mapAction G ≅
          sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}) ⋙ Eset.functor ⋙ V) ∧
      (∀ (F : Sheaf J AddCommGrpCat.{max (u + 1) v}) (g : G)
          (τ : Ω ≃ₐ[K] Ω)
          (hτ : (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (X : S.Etale) (x x' : p.fiber.obj X)
          (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
          (z : F.obj.obj (op X)),
        (i.hom.app F) ((E.functor.obj F).obj.ρ g
          ((i.inv.app F) (p.toPresheafFiber X x F.obj z))) =
            p.toPresheafFiber X x' F.obj z) ∧
      (∀ (F : Sheaf J (Type (max (u + 1) v))) (g : G)
          (τ : Ω ≃ₐ[K] Ω)
          (hτ : (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (X : S.Etale) (x x' : p.fiber.obj X)
          (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
          (z : F.obj.obj (op X)),
        (j.hom.app F) ((Eset.functor.obj F).obj.obj.ρ g
          ((j.inv.app F) (p.toPresheafFiber X x F.obj z))) =
            p.toPresheafFiber X x' F.obj z) := by
  sorry

end AlgebraicGeometry.Scheme
