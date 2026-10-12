/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Sheaf.AlgebraicGeometry.ThickeningSystemsDictionary
import Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import Sheaf.AlgebraicGeometry.FormalCompletionFullyFaithfulProper
import Sheaf.AlgebraicGeometry.CoherentFormalModule

/-! # Restriction of morphisms on a common proper closed support

Source: Stacks Project, Tags 088E and 088F
(blueprint: lem-weil-pbc-grothendieck-existence-supported-hom).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Restriction gives a bijection on morphisms for modules annihilated by one proper closed
subscheme. This is the proper-case reduction, before using the support characterization.
Source: Stacks, Theorem 088E, first paragraph; Lemmas 087T and 0883,
with the thickening formulation of Remark 088F.
(blueprint: lem-weil-pbc-grothendieck-existence-supported-hom).

Proof:
1. The given closed subscheme Z is proper over A and its ideal kills both modules.
2. Closed-immersion coherent equivalence lifts F and G to coherent modules on Z and
identifies their Hom sets. Its formal version identifies the Hom sets of their
completions, naturally in both modules and compatibly with completion of a morphism.
3. Completion on Z is fully faithful by the proper completion theorem. Transport this
bijection through the two Hom identifications to obtain the completion bijection on X.
4. The thickening-systems dictionary identifies formal morphisms with precisely the
compatible families below, and sends completed w to its restrictions. Therefore the
restriction map is bijective. Naturality of c verifies that every restricted w is a
compatible family; its canonical comparison is the one specified by hc. -/
theorem grothendieckExistence_supported_hom
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
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
    (hc : ∀ n : ℕ, c n = (Classical.choice (Scheme.Modules.nonempty_tensorPullbackComp (i n)
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 +
      1)))))))).symm ≪≫ eqToIso (congrArg Scheme.Modules.tensorPullback (hi n)))
    (F G : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (Z : Scheme.{u}) (j : Z ⟶ X) [IsClosedImmersion j] [IsProper (j ≫ f)]
    (hkillF : ∀ (V : X.Opens) (a : Γ(X, V)), a ∈ j.ker.idealOfOpens V →
      ∀ t : Γ(F, V), a • t = 0)
    (hkillG : ∀ (V : X.Opens) (a : Γ(X, V)), a ∈ j.ker.idealOfOpens V →
      ∀ t : Γ(G, V), a • t = 0) :
    Function.Bijective (fun w : G ⟶ F ↦
      (⟨fun n ↦
        (Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1))))))).map w, fun n ↦ ((c n).hom.naturality w).symm⟩ :
        {v : ∀ n : ℕ,
        (Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G ⟶
        (Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1))))))).obj F |
          ∀ n : ℕ, (c n).hom.app G ≫ v n =
          (Scheme.Modules.tensorPullback (i n)).map (v (n + 1)) ≫ (c n).hom.app F})) := by sorry

end AlgebraicGeometry
