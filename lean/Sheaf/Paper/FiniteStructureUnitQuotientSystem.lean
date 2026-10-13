/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Sheaf.Paper.FiniteStructureAdjointTransitions

/-! # Factor reduced units through a proper supporting quotient

Source: Stacks Project, Tag 09ZT
(blueprint: lem-weil-pbc-finite-structure-unit-quotient-system).
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

/-- The reduced structure maps factor compatibly through one proper supporting quotient.
Source: Stacks Project, Tag 09ZT, algebra structure paragraph, expanded using 0CYS,
01XZ, 01Y6, 0096 and affine base change.

Proof: X is Noetherian since it is finite type over the Noetherian affine base.
Use the scheme-theoretic support Z of G, defined by its annihilator ideal J.
Tag 0CYS makes Z proper over A. Let Q be the direct image of O_Z, equivalently
O_X/J, and q the quotient map. Q is quasi-coherent of finite type, hence coherent
by 01XZ, and has proper support. Pullback is right exact, so j_n^*Q is the quotient
of O_Xn by the image of J. That image annihilates j_n^*G and therefore the algebra
p_n,*O_Yn identified with it by psi_n. Acting on 1 shows that its structure map
kills J. The quotient universal property gives a unique map to p_n,*O_Yn;
compose with psi_n inverse to get v_n. Naturality of the quotient, base change's
preservation of 1, hpsi, and the pinned composition comparison show compatibility:
both sides agree after the epimorphic pullback of q. The section formula follows
by the canonical adjunction unit, which sends r to 1 tensor r, and pushforward
composition. No completion, multiplication on G, or lifted map is used here.
For G=0 the scheme-theoretic support and Q are zero; for I=0 the same quotient
factorization applies unchanged; on an empty scheme the equations are unique.
(blueprint: lem-weil-pbc-finite-structure-unit-quotient-system). -/
theorem finite_structure_unit_quotient_system
    (A : Type u) [CommRing A] (I : Ideal A)
    [IsNoetherianRing A]
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
        (c n).hom.app G ≫ (ψ n).hom) :
    ∃ Q : X.Modules, RingedSpace.IsCoherent X.toRingedSpace Q ∧
      Scheme.Modules.HasSupportProperOver f Q ∧
      ∃ (q : SheafOfModules.unit X.ringCatSheaf ⟶ Q)
        (v : ∀ n : ℕ, (Scheme.Modules.tensorPullback (pullback.fst f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj Q ⟶
          (Scheme.Modules.tensorPullback (pullback.fst f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G),
        (∀ n : ℕ, (c n).hom.app Q ≫ v n =
          (Scheme.Modules.tensorPullback (i n)).map (v (n + 1)) ≫ (c n).hom.app G) ∧
        (∀ (n : ℕ) (U : X.Opens) (r : Γ(X, U)),
          (Scheme.Modules.finiteStructureAdjoint
            (pullback.fst f (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (I ^ (n + 1)))))) (fnY n) Q (v n ≫ (ψ n).hom)).app U
            ((q.val.app (op U)).hom r) =
            (fnY n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (I ^ (n + 1)))))).app U r) := by sorry

end AlgebraicGeometry
