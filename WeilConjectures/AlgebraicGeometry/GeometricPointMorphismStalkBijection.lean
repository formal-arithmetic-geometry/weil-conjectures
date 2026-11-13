/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.GeometricPointMorphismCategoryEquivalence
import WeilConjectures.AlgebraicGeometry.GeometricPointMorphismSetStalk
import WeilConjectures.AlgebraicGeometry.GeometricPointMorphismAddCommGrpStalk

/-!
# Morphisms of geometric points and étale stalks

## References

* Stacks, Tag 04FN
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- A morphism of geometric points induces the indicated equivalence of pointed étale
neighbourhoods and the unique representative-preserving bijection on set-valued stalks;
for abelian sheaves the representative-preserving morphism is an isomorphism
(Stacks, Tag 04FN). -/
theorem geometricPointMorphism_stalk_bijection
    {S : Scheme.{u}} {k k' : Type u} [Field k] [IsAlgClosed k]
    [Field k'] [IsAlgClosed k'] (s : Spec (.of k) ⟶ S) (s' : Spec (.of k') ⟶ S)
    (a : Spec (.of k) ⟶ Spec (.of k')) (ha : a ≫ s' = s) :
    let b : Over.mk s ⟶ Over.mk s' := Over.homMk a ha
    let α : (pointSmallEtale s').fiber ⟶ (pointSmallEtale s).fiber :=
      Functor.whiskerLeft (Etale.forget S) (coyoneda.map b.op)
    (NatTrans.mapElements α).IsEquivalence ∧
    (∀ F : Sheaf S.smallEtaleTopology (Type (max u v)),
      let P := fun f : (pointSmallEtale s').sheafFiber.obj F →
          (pointSmallEtale s).sheafFiber.obj F ↦
        ∀ (U : S.Etale) (t : (pointSmallEtale s').fiber.obj U)
          (σ : F.obj.obj (op U)),
          f ((pointSmallEtale s').toPresheafFiber U t F.obj σ) =
            (pointSmallEtale s).toPresheafFiber U (α.app U t) F.obj σ
      (∃! f, P f) ∧ ∀ f, P f → Function.Bijective f) ∧
    (∀ F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max u v},
      let P := fun f : (pointSmallEtale s').sheafFiber.obj F ⟶
          (pointSmallEtale s).sheafFiber.obj F ↦
        ∀ (U : S.Etale) (t : (pointSmallEtale s').fiber.obj U),
          (pointSmallEtale s').toPresheafFiber U t F.obj ≫ f =
            (pointSmallEtale s).toPresheafFiber U (α.app U t) F.obj
      (∃! f, P f) ∧ ∀ f, P f → IsIso f) := by
  dsimp
  refine ⟨geometricPointMorphism_category_equivalence s s' a ha, ?_, ?_⟩
  · exact geometricPointMorphism_set_stalk s s' a ha
  · exact geometricPointMorphism_addCommGrp_stalk s s' a ha

end AlgebraicGeometry.Scheme
