/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Sheaf.AlgebraicGeometry.EtaleFieldGsets
import Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Sheaf.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Essential surjectivity of the canonical Galois stalk functor

Source: Stacks Project, Tags 03QT and 03QR.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Tag 03QT, theorem-equivalence-sheaves-point, proof;
Tag 03QR, the etale-scheme/Galois-set equivalence used there.
(blueprint: lem-exc-galois-stalk-action-essentially-surjective).

Any lift of the stalk functor with the canonical formula realizes every discrete G-set.

Proof: Fix a discrete continuous G-set M in Type w, where w = max (u + 1) v.
Its orbits are finite: an open stabilizer has finite index in the compact absolute
Galois group. Each orbit can therefore be represented by a finite set in Type u,
with its continuous G-action transported along a bijection. Apply etaleFieldGsets
to realize this small G-set by an etale K-scheme X. The representable presheaf h_X
is a sheaf, by smallEtaleRepresentablePresheaf_isSheaf. Lift its values to Type w.
The representable-stalk isomorphism identifies its stalk with the Omega-points
of X. Finite separable residue fields identify these points with the Ks-points
of X, naturally. The change-of-lift formula for T and j identifies the actions,
so T(h_X) is the chosen orbit, equivariantly. Form in sheaves with values in Type w
the coproduct of these sheaves, indexed by the orbit set of M, which is in Type w.
The stalk preserves this coproduct because it is left adjoint to the skyscraper
functor. Through the natural isomorphism j, its injections are the underlying
maps of the T-images of the sheaf coproduct injections, hence equivariant.
Their induced bijection from the disjoint union of orbits to T of the coproduct
is therefore an equivariant isomorphism. The disjoint union of orbits is M,
giving the required object in the essential image. For M empty use the empty
coproduct. This construction does not require a coproduct scheme in Type u,
even when the orbit set lies in the larger universe w. -/
theorem galoisStalkActionFunctor_essSurj
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
    ∀ (T : Sheaf J (Type (max (u + 1) v)) ⥤
        DiscreteContAction (Type (max (u + 1) v)) G)
      (j : T ⋙ V ⋙ Action.forget (Type (max (u + 1) v)) G ≅ p.sheafFiber),
      (∀ (F : Sheaf J (Type (max (u + 1) v))) (g : G)
          (τ : Ω ≃ₐ[K] Ω)
          (hτ : (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (X : S.Etale) (x x' : p.fiber.obj X)
          (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
          (z : F.obj.obj (op X)),
        (j.hom.app F) ((T.obj F).obj.obj.ρ g
          ((j.inv.app F) (p.toPresheafFiber X x F.obj z))) =
            p.toPresheafFiber X x' F.obj z) →
      T.EssSurj := by sorry

end AlgebraicGeometry.Scheme
