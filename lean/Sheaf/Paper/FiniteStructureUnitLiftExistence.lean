/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase

public import Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso
public import Sheaf.Paper.FiniteStructureAdjointTransitions

public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-! # Lift the unit of finite structure sheaves

Source: Stacks Project, Tag 09ZT
(blueprint: lem-weil-pbc-finite-structure-unit-lift-existence).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry

open Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

/-- Existence part of the unit lift through a proper supporting quotient.
Source: Stacks Project, Tag 09ZT, algebra structure paragraph, expanded using 088E, 088F
and 0CYS.

Proof: Since X is finite type over the Noetherian affine base, X is Noetherian.
Proper support and coherence give a coherent ideal sheaf J annihilating G, with
V(J) proper over A (0CYS). Put Q = O_X/J. This is coherent with proper support.
The image of J in O_Xn annihilates j_n^*G, hence also p_n,* O_Yn through psi_n.
Applying this annihilation to the section 1 shows that the structure map
O_Xn to p_n,* O_Yn kills J. It therefore factors through j_n^*Q. Transport
this map through psi_n inverse to obtain u_n : j_n^*Q to j_n^*G.
The cartesian base-change map preserves units. The given transition equation
for psi and the canonical composition comparison thus make the u_n compatible.
Full faithfulness of completion on coherent modules with proper support (088E,
088F) lifts this family to u : Q to G. Define eta as O_X to Q followed by u.
Its reductions are exactly the structure maps. Adjunction and pushforward
composition give the stated scalar formula, including the formula for r = 1.
Let L be the module endomorphism of G given by left multiplication by eta(1).
After tensor pullback to X_n and conjugation by psi_n, multiplicativity hmu
identifies L with multiplication by 1 on p_n,* O_Yn, hence with its identity.
Equality of these maps is checked locally on pure tensors, which generate the
pullback tensor product. Faithfulness of completion on G gives L = identity;
evaluating on sections proves the left-unit law. This uses proper support of
Q and G, never properness of O_X. If G is zero (including an empty scheme),
the quotient and all maps above are zero, and both asserted equations hold.
(blueprint: lem-weil-pbc-finite-structure-unit-lift-existence). -/
theorem finite_structure_unit_lift_existence
    (A : Type u) [CommRing A] (I : Ideal A)
    [IsNoetherianRing A] [IsAdicComplete I A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
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
    (hc : ∀ n : ℕ, c n = (Scheme.Modules.tensorPullbackCompositionIso (i n)
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) (hi n)).symm)
    (Yn : ℕ → Scheme.{u})
    (fnY : ∀ n, Yn n ⟶ pullback f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    [∀ n, IsFinite (fnY n)]
    (gn : ∀ n, Yn n ⟶ Yn (n + 1))
    (hcart : ∀ n, IsPullback (fnY n) (gn n) (i n) (fnY (n + 1)))
    (hw : ∀ n, gn n ≫ (fnY (n + 1) ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) =
      fnY n ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (hproper : Scheme.Modules.HasSupportProperOver f G)
    (ψ : ∀ n, (Scheme.Modules.tensorPullback (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G ≅
        (Scheme.Modules.pushforward (fnY n)).obj
          (SheafOfModules.unit (Yn n).ringCatSheaf))
    (hψ : ∀ n,
      (Scheme.Modules.tensorPullback (i n)).map (ψ (n + 1)).hom ≫
        (Scheme.Modules.moduleBaseChangeMap (fnY (n + 1)) (fnY n) (i n) (gn n)
          (hcart n).flip.w (SheafOfModules.unit (Yn (n + 1)).ringCatSheaf) ≫
          (Scheme.Modules.pushforward (fnY n)).map
            (Scheme.Modules.tensorPullbackObjUnitToUnit (gn n))) =
        (c n).hom.app G ≫ (ψ n).hom)
    (μ : G ⊗ G ⟶ G)
    (hcomm : ∀ (U : X.Opens) (x y : Γ(G, U)),
      μ.app U (tmulSection x y) = μ.app U (tmulSection y x))
    (hμ : ∀ (n : ℕ) (U : X.Opens),
        let a : Γ(G, U) → Γ(Yn n, (fnY n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1)))))) ⁻¹ᵁ U) :=
          fun x ↦ (Scheme.Modules.finiteStructureAdjoint
          (pullback.fst f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1)))))) (fnY n) G (ψ n).hom).app U x
        ∀ (x y : Γ(G, U)),
          a (μ.app U (tmulSection x y)) = a x * a y) :
    ∃ η : SheafOfModules.unit X.ringCatSheaf ⟶ G,
      (∀ (U : X.Opens) (x : Γ(G, U)),
        μ.app U (tmulSection ((η.val.app (op U)).hom (1 : Γ(X, U))) x) = x) ∧
      (∀ (n : ℕ) (U : X.Opens) (r : Γ(X, U)),
        (Scheme.Modules.finiteStructureAdjoint
          (pullback.fst f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1)))))) (fnY n) G (ψ n).hom).app U
          ((η.val.app (op U)).hom r) =
          (fnY n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1)))))).app U r) := by sorry

end AlgebraicGeometry
