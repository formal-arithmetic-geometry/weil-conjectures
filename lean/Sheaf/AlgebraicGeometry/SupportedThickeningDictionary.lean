/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Sheaf.AlgebraicGeometry.ThickeningSystemsDictionary
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
import Sheaf.AlgebraicGeometry.QuotientBaseChangeIdeal
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction

/-! # Supported thickening systems and completion isomorphisms
Source: Stacks Project, Remark 088F and Lemma 087T.
(blueprint: lem-weil-pbc-supported-thickening-dictionary).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The annihilation and isomorphism portions of the thickening dictionary.
Source: Stacks Project, Remark 088F, Lemma 087T, and equation 0880.
(blueprint: lem-weil-pbc-supported-thickening-dictionary).
Proof: Obtain the dictionary functor Φ, its evaluation isomorphisms β, restriction
functor R, completion comparison ρ, and restriction comparison d from
thickeningSystems_dictionary, using tensor-pullback adjunctions. First align d with c:
at level n, d.inv followed by c.hom is a natural automorphism t of j_n^*. Extend t to
modules on X_n by evaluating at j_n,*H and conjugating by the counit
j_n^*j_n,*H ≅ H. This counit is invertible by fully faithful closed pushforward.
With counit ε_H, the induced automorphism is ε_H.inv ≫ t_(j_n,*H) ≫ ε_H.hom.
Naturality against the adjunction unit G → j_n,*j_n^*G and the triangle identity
identify its value at j_n^*G with t_G. Naturality then gives ψ ≫ t_H = t_G ≫ ψ for
any ψ : j_n^*G ≅ H. Replace φ_n by φ_n followed by the inverse of t_(F_n),
and apply Φ to that coherent system. The dictionary transition equation for this
modified system is equivalent, by this naturality equation, to the requested equation
with c and the original φ. This normalization avoids identifying two arbitrary
adjunction choices by uniqueness alone.
The evaluation isomorphisms β identify each formal term with j_n,*F_n. They are
linear, so hkill transports to annihilation of every formal term. On stalks, products
of germs of ideal sections and module sections vanish: represent the two germs on a
common open and apply hkill there. The ideal-module-product stalk formula identifies
its stalk with the span of these products, hence all its stalks are zero and the
product sheaf is zero. This is SupportedOn. The quotient-base-change ideal formula,
specialized to the identity of Spec A, identifies ker(Spec(A/I) → Spec A) with the
ideal associated to I; comap along f gives the displayed ideal. For any completion
isomorphism, use ρ and full faithfulness of Φ to obtain R(G) ≅ the modified system.
Evaluate and conjugate by r to get ψ. Its transition identity and the normalization
above prove the stated compatibility. No completeness or properness is used. -/
theorem supportedThickening_dictionary
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
    (hi : ∀ n : ℕ, i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))))
    (hp : ∀ n : ℕ, i n ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I :=
      I) (Nat.le_succ (n + 1))))))
    (c : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⋙ Scheme.Modules.tensorPullback (i n) ≅
      Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))))
    (hc : ∀ n : ℕ, c n = (Classical.choice (Scheme.Modules.nonempty_tensorPullbackComp (i n)
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 +
      1)))))))).symm ≪≫ eqToIso (congrArg Scheme.Modules.tensorPullback (hi n)))
    (F : ∀ n : ℕ, (pullback f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))).Modules)
    (φ : ∀ n : ℕ, (Scheme.Modules.tensorPullback (i n)).obj (F (n + 1)) ≅ F n)
    (hF : ∀ n : ℕ, RingedSpace.IsCoherent (pullback f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))).toRingedSpace (F n))
    (Z : Scheme.{u}) (j : Z ⟶ X) [IsClosedImmersion j]
    (hkill : ∀ (n : ℕ) (V : X.Opens) (a : Γ(X, V)),
        a ∈ j.ker.idealOfOpens V →
        ∀ t : Γ((Scheme.Modules.pushforward (pullback.fst f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj (F n), V),
          a • t = 0) :
    ∃ hX : IsNoetherian X,
      ∃ M : @CoherentFormalModule X hX
          ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f),
        @SupportedOn X Z hX
          ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f) M j _ ∧
        ∀ G : CoherentModules X,
          Nonempty ((@completion X hX
            ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f)).obj G ≅ M) →
          ∃ ψ : ∀ n : ℕ, (Scheme.Modules.tensorPullback (pullback.fst f
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G.obj ≅ F n,
            ∀ n : ℕ, (Scheme.Modules.tensorPullback (i n)).map (ψ (n + 1)).hom ≫
              (φ n).hom = (c n).hom.app G.obj ≫ (ψ n).hom := by sorry

end AlgebraicGeometry
