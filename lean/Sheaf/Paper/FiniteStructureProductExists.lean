/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase

public import Sheaf.Paper.FiniteStructureAdjointTransitions
import Sheaf.Paper.FiniteStructureProductCompatibility

public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

import Sheaf.Paper.FiniteStructureTensorPowersSupported
import Sheaf.AlgebraicGeometry.GrothendieckExistence
import Sheaf.AlgebraicGeometry.ModulePullbackTensor

/-! # Existence of a lifted finite-structure product

Source: Stacks Project, Tag 09ZT
(blueprint: lem-weil-pbc-finite-structure-product-exists).
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

/-- A product lifting the reduced products, before proving any ring laws.
Source: Stacks Project, Tag 09ZT, multiplication paragraph; Tags 088E and 088F.

Proof: Choose a proper closed supporting subscheme annihilating G (0CYS). Its ideal
annihilates the tensor square. On affine opens the square is the tensor product of two
finite modules, so it is quasi-coherent of finite type and hence coherent on the
Noetherian scheme X. Write P_n = j_n^*, Q_n = i_n^*, and delta_n for the tensor comparison of P_n.
Let m_n be the direct-image product characterized by m_n(x tensor y) = xy on all opens.
Define v_n = delta_n followed by (psi_n tensor psi_n), m_n, and psi_n inverse.
This is a morphism P_n(G tensor G) to P_n(G). The base-change algebra formula says
Q_n(m_(n+1)) followed by beta equals delta_i followed by (beta tensor beta) and m_n.
The composition comparison kappa = c_n satisfies the tensor equation
kappa_(G tensor G) followed by delta_n = Q_n(delta_(n+1)) followed by delta_i and
(kappa_G tensor kappa_G). Prove this equation by taking adjoints, evaluating on
x tensor y, and using the adjunction mate unit identity for the pinned comparison;
the tensor comparisons take these unit images to the tensor of the individual images.
The sheaf tensor universal property then makes the equality a morphism identity.
Substitute hpsi, the displayed tensor equation, and the base-change product equation;
use naturality of delta_i with psi in both factors and cancel psi_n. The resulting
identity is c_n.app (G tensor G) followed by v_n = Q_n(v_(n+1)) followed by c_n.app G.
Fullness of completion (088E,
in the formulation 088F) lifts the compatible family to a map mu. Evaluate its
reduction equation after the tensor-adjunction unit: the tensor comparison takes
x tensor y to the tensor of the unit images. Applying psi and pushforward
composition gives precisely the adjoint multiplicativity formula below. This
construction imposes no unit, associativity or symmetry. The argument also applies
to zero modules, empty schemes, and I equal to the zero or unit ideal.
(blueprint: lem-weil-pbc-finite-structure-product-exists). -/
theorem finite_structure_product_exists
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
        (c n).hom.app G ≫ (ψ n).hom) :
    ∃ μ : G ⊗ G ⟶ G,
      (∀ (n : ℕ) (U : X.Opens),
        let a : Γ(G, U) → Γ(Yn n, (fnY n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1)))))) ⁻¹ᵁ U) :=
          fun x ↦ (Scheme.Modules.finiteStructureAdjoint
          (pullback.fst f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1)))))) (fnY n) G (ψ n).hom).app U x
        ∀ (x y : Γ(G, U)),
          a (μ.app U (tmulSection x y)) = a x * a y) := by
  exact finite_structure_product_compatibility A I X f i hi hp c hc
    Yn fnY gn hcart hw G hG hproper ψ hψ

end AlgebraicGeometry
