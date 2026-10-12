/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Sheaf.AlgebraicGeometry.EtaleFieldGsets
import Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints

/-!
# The canonical Galois action functor on geometric stalks

Source: Stacks Project, Tag 03QW.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Tag 03QW, section-galois-action-stalks.
(blueprint: lem-exc-galois-stalk-action-functor).

The geometric stalk lifts to discrete continuous Galois actions; no full faithfulness
or essential surjectivity is asserted here.

Proof: Every germ is represented by a section on a pointed etale neighbourhood.
For g in Gal(Ks/K), extend g to a K-automorphism of Omega and precompose the pointed
lift with its spectrum. Such an extension exists: extend g first to the algebraic
closure of K in Omega, fix a transcendence basis, and extend to its algebraic closure.
The residue field of the lifted point is finite separable over K, so its image in
Omega lies in the image of Ks. Thus the new lift is independent of the extension.
Changing a representative by an etale restriction commutes with this operation,
which therefore descends to the stalk colimit. Precomposition and contravariance of
Spec give the identity and multiplication laws for a left action. A representative
has stabilizer containing the subgroup fixing its finite separable residue-field
image; this subgroup is open. Hence all stabilizers are open, which gives continuity
for the discrete topology. Sheaf morphisms act on the section in a representative
and commute with changes of lift, so their stalk maps are equivariant. Use these
objects and maps to define T. Their underlying sets and maps are the stalk functor,
giving the natural isomorphism j. The definition on representatives is the formula
below. Only finite separable residue-field images are used, so transcendental
extensions Omega and separably closed or imperfect base fields cause no change. -/
theorem exists_galoisStalkActionFunctor
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] :
    let S := Spec (.of K)
    let J := S.smallEtaleTopology
    let s := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
    let p := pointSmallEtale s
    let G := Gal(Ks/K)
    let V := ObjectProperty.ι (ContAction.IsDiscrete (V := Type (max (u + 1) v)) (G := G))
      ⋙ ObjectProperty.ι (Action.IsContinuous (V := Type (max (u + 1) v)) (G := G))
    ∃ (T : Sheaf J (Type (max (u + 1) v)) ⥤
        DiscreteContAction (Type (max (u + 1) v)) G)
      (j : T ⋙ V ⋙ Action.forget (Type (max (u + 1) v)) G ≅ p.sheafFiber),
      ∀ (F : Sheaf J (Type (max (u + 1) v))) (g : G)
          (τ : Ω ≃ₐ[K] Ω)
          (hτ : (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (X : S.Etale) (x x' : p.fiber.obj X)
          (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
          (z : F.obj.obj (op X)),
        (j.hom.app F) ((T.obj F).obj.obj.ρ g
          ((j.inv.app F) (p.toPresheafFiber X x F.obj z))) =
            p.toPresheafFiber X x' F.obj z := by sorry

end AlgebraicGeometry.Scheme
