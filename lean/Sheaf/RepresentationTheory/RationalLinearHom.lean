module

public import Sheaf.AlgebraicGeometry.HopfCoactionLinearization
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Rational conjugation on linear Hom

Source: Milne, Algebraic Groups (2017), Remark 4.1, printed pp.83--84,
and Lemma 22.40 (b) to (a), printed p.477.
(blueprint: lem-sfb-rational-linear-hom)

Coactions use the right-comodule order M tensor k[G]. Scalar extensions use
A tensor M, as in LinearMap.baseChange; tensor symmetry identifies this with M tensor A.
An algebra-valued point is its coordinate algebra map k[G] to A. Its inverse is
composition with the canonical coordinate antipode. No finite-type assumption is used.
-/

set_option autoImplicit false

@[expose] public section

universe u v w t c

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace HopfAction

/-- Evaluate a right coaction at a coordinate-algebra point and extend A-linearly.
On a tensor a tensor m its value is a times the symmetry of (1 tensor g)rho(m).
Source: Milne, Remark 4.1, printed p.84.
(blueprint: lem-sfb-rational-linear-hom) -/
noncomputable def coactionPointAction
    (k : Type u) [Field k] (C : Type c) [CommRing C] [Algebra k C]
    (M : Type v) [AddCommGroup M] [Module k M]
    (A : Type t) [CommRing A] [Algebra k A]
    (ρ : M →ₗ[k] M ⊗[k] C) (g : C →ₐ[k] A) :
    A ⊗[k] M →ₗ[A] A ⊗[k] M :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton A (M →ₗ[k] A ⊗[k] M)
      ((TensorProduct.comm k M A).toLinearMap ∘ₗ g.toLinearMap.lTensor M ∘ₗ ρ))

/-- Finite-dimensional rational modules have a rational Hom coaction, with conjugation
on every scalar extension and fixed vectors exactly the equivariant maps.
Source: Milne, Remark 4.1, printed pp.83--84, and Lemma 22.40 (b) to (a), p.477.
(blueprint: lem-sfb-rational-linear-hom)

Proof:
1. The canonical Hom base-change map sends a tensor f to a times f.baseChange A.
   Choose finite bases e_i of V and w_j of W. If F(1 tensor e_i) is the sum of
   a_ji tensor w_j, its inverse sends F to the sum of a_ji tensor E_ji, where
   E_ji(e_l) = delta_il w_j. Expanding in the bases proves both inverse identities.
   These formulas commute with algebra maps. Empty bases give empty sums.
2. Apply lem-sfb-hopf-coaction-linearization with E = k and its trivial coaction,
   for V and W. It gives coordinate-algebra-linear automorphisms D_V and D_W,
   identity at the identity section and satisfying D_12 = D_1 D_2 on G times G.
3. Under the canonical Hom base-change isomorphism define D_H(T) = D_W T D_V^-1.
   Its inverse is T mapping to D_W^-1 T D_V. Its identity restriction is the identity.
   The two cocycles give D_H,1 D_H,2(T) =
   D_W,1 D_W,2 T D_V,2^-1 D_V,1^-1 = D_W,12 T D_V,12^-1.
   This equality holds over the coordinate algebra of G times G.
4. The reverse direction of lem-sfb-hopf-coaction-linearization recovers rho_H
   from D_H on f tensor 1 and proves counitality and coassociativity. Pull back
   along g and g^-1. The cocycle gives D_M(g)^-1 = D_M(g^-1), hence the displayed
   conjugation formula. These operators are exactly coactionPointAction.
5. Under the Hom base-change isomorphism at C, rho_H(f) = f tensor 1 says
   D_W f_C D_V^-1 = f_C, equivalently D_W f_C = f_C D_V. Evaluation on 1 tensor v
   gives the coaction square; extending C-linearly proves the converse, also the
   morphism clause of lem-sfb-hopf-coaction-linearization. Pulling back proves
   equivariance at every A-point. Conversely take A = C and its universal point
   id_C to recover the coaction square. This includes nonreduced group schemes.
-/
theorem rationalLinearHom
    (k : Type u) [Field k] (G : Scheme.{u}) [G.Over (Spec (.of k))]
    [GrpObj (G.asOver (Spec (.of k)))] [IsAffine G]
    (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (W : Type w) [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρV : V →ₗ[k] V ⊗[k] Γ(G, ⊤)) (ρW : W →ₗ[k] W ⊗[k] Γ(G, ⊤))
    (hVcoassoc : Coassociative k Γ(G, ⊤) V ρV) (hVcounit : Counital k Γ(G, ⊤) V ρV)
    (hWcoassoc : Coassociative k Γ(G, ⊤) W ρW) (hWcounit : Counital k Γ(G, ⊤) W ρW) :
    ∃ ρH : (V →ₗ[k] W) →ₗ[k] (V →ₗ[k] W) ⊗[k] Γ(G, ⊤),
      Coassociative k Γ(G, ⊤) (V →ₗ[k] W) ρH ∧
      Counital k Γ(G, ⊤) (V →ₗ[k] W) ρH ∧
      (∀ (A : Type (max u t)) [CommRing A] [Algebra k A],
        ∃ j : A ⊗[k] (V →ₗ[k] W) ≃ₗ[A] (A ⊗[k] V →ₗ[A] A ⊗[k] W),
          (∀ (a : A) (f : V →ₗ[k] W), j (a ⊗ₜ[k] f) = a • f.baseChange A) ∧
          ∀ (g : Γ(G, ⊤) →ₐ[k] A) (F : A ⊗[k] (V →ₗ[k] W)) (x : A ⊗[k] V),
            j (coactionPointAction k Γ(G, ⊤) (V →ₗ[k] W) A ρH g F) x =
              coactionPointAction k Γ(G, ⊤) W A ρW g
                (j F (coactionPointAction k Γ(G, ⊤) V A ρV
                  (g.comp (HopfAlgebra.antipodeAlgHom k Γ(G, ⊤))) x))) ∧
      (∀ f : V →ₗ[k] W,
        (ρH f = f ⊗ₜ[k] (1 : Γ(G, ⊤)) ↔
          ρW ∘ₗ f = f.rTensor Γ(G, ⊤) ∘ₗ ρV) ∧
        (ρW ∘ₗ f = f.rTensor Γ(G, ⊤) ∘ₗ ρV ↔
          ∀ (A : Type (max u t)) [CommRing A] [Algebra k A]
            (g : Γ(G, ⊤) →ₐ[k] A) (x : A ⊗[k] V),
            f.baseChange A (coactionPointAction k Γ(G, ⊤) V A ρV g x) =
              coactionPointAction k Γ(G, ⊤) W A ρW g (f.baseChange A x))) := by
  sorry

end HopfAction
