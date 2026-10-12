/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Sheaf.AlgebraicGeometry.EtaleFieldGsets
import Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants

/-! Fullness of the canonical Galois stalk functor.
Source: Stacks Project, Tags 03QT and 04JM (blueprint: lem-exc-galois-stalk-action-full).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Tags 03QT and 04JM.
(blueprint: lem-exc-galois-stalk-action-full).

Proof: Let A be the subfield of Omega algebraic over K. It is algebraically closed and every
pointed etale neighbourhood factors uniquely through Spec A by finite separability of its
residue field. The resulting natural identifications of germs transport the invariant-section
bijections to Omega. The canonical germ formula identifies the action transported by j with this
action: extend each automorphism of Ks to A, then to Omega by fixing a transcendence
basis and extending across the remaining algebraic extension. Every germ has a representative,
so the formula determines the transported action. Over every finite separable intermediate
field, an equivariant map restricts to a map of invariant sets, hence to a map of sections.
Embedding compatibility makes these maps natural.
Every etale scheme is a disjoint union of finite separable components; the sheaf condition
extends these maps uniquely to the product of their section sets. These section maps constitute
a sheaf morphism. Every germ has a representative on a component, so the stalk map is the
specified equivariant map. Naturality of j then identifies its T image with that map, giving
fullness. Empty schemes use the empty product. -/
theorem galoisStalkActionFunctor_full
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] :
    let S := Spec (.of K); let J := S.smallEtaleTopology
    let s := Spec.map (CommRingCat.ofHom (algebraMap K Ω)); let p := pointSmallEtale s
    let G := Gal(Ks/K); let V := ObjectProperty.ι (ContAction.IsDiscrete
      (V := Type (max (u + 1) v)) (G := G)) ⋙ ObjectProperty.ι (Action.IsContinuous
      (V := Type (max (u + 1) v)) (G := G))
    ∀ (T : Sheaf J (Type (max (u + 1) v)) ⥤ DiscreteContAction (Type (max (u + 1) v)) G)
      (j : T ⋙ V ⋙ Action.forget (Type (max (u + 1) v)) G ≅ p.sheafFiber),
      (∀ (F : Sheaf J (Type (max (u + 1) v))) (g : G) (τ : Ω ≃ₐ[K] Ω)
          (hτ : (algebraMap Ks Ω).comp g.toRingHom = τ.toRingHom.comp (algebraMap Ks Ω))
          (X : S.Etale) (x x' : p.fiber.obj X)
          (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
          (z : F.obj.obj (op X)),
        (j.hom.app F) ((T.obj F).obj.obj.ρ g ((j.inv.app F) (p.toPresheafFiber X x F.obj z))) =
          p.toPresheafFiber X x' F.obj z) → T.Full := by sorry

end AlgebraicGeometry.Scheme
