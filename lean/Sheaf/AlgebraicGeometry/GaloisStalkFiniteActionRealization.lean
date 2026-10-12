/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Sheaf.AlgebraicGeometry.EtaleFieldGsets
import Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Sheaf.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf

/-!
# Finite actions in the essential image of the Galois stalk functor

Source: Stacks Project, Tags 03QT and 03QR.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Tag 03QT, proof of theorem-equivalence-sheaves-point,
using Tag 03QR. (blueprint: lem-exc-galois-stalk-finite-action-realization).

Proof: Replace the finite underlying set of M by Fin n in Type u and transport its
continuous action along a bijection. Apply etaleFieldGsets to obtain an etale
K-scheme X with this small G-set of Ks-points. The representable presheaf of X
is a sheaf by smallEtaleRepresentablePresheaf_isSheaf; lift its values to
Type (max (u + 1) v). The representable-stalk isomorphism identifies its stalk
with the Omega-points of X. Every such point factors uniquely through Ks:
its residue field is finite separable over K, so its embedding into Omega lands
in the image of the separable closure. These factorizations identify Omega-points
with Ks-points. For each g extend its automorphism of Ks to Omega. The assumed
germ formula and the action formula in etaleFieldGsets show that this bijection,
transported through j, is equivariant. Its inverse is equivariant as well, hence
it gives the asserted isomorphism. The empty finite action is represented by
the empty etale scheme. This lemma asserts only finite-action realization. -/
theorem galoisStalkActionFunctor_finite_mem_essImage
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
      ∀ (M : DiscreteContAction (Type (max (u + 1) v)) G),
        Finite M.obj.obj.V → T.essImage M := by sorry

end AlgebraicGeometry.Scheme
