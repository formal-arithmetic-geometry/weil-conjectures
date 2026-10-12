/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase

public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.AffinePushforwardBaseChange

import Sheaf.AlgebraicGeometry.GrothendieckExistence
import Sheaf.AlgebraicGeometry.ModuleSupportProperOverBase
import Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.TensorPullbackTilde
import Sheaf.AlgebraicGeometry.ModulePullbackTensor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal

/-! # Algebra structures on algebraized finite direct images

Source: Stacks Project, Tags 09ZT, 088E and 088F.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option autoImplicit false

set_option hygiene false in
local notation "𝒪⁎" g:max => Under.mk (⟨(g).c⟩ : Scheme.sheaf _ ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} (g).base).obj (Scheme.sheaf _))

/-- Lift the algebra structure on an already algebraized coherent module system.
Source: Stacks Project, Lemma 09ZT, the multiplication and unit paragraphs;
Theorem 088E and Remark 088F, and Schemes Lemma 01I9.

Proof: Choose a proper closed subscheme annihilating G by 0CYS. Its ideal also
annihilates the tensor square and cube of G and the quotient of the structure sheaf.
These modules are quasi-coherent and finite type, hence coherent. Tensor pullback
commutes with tensor products and their associativity, symmetry and unit constraints.
Conjugate the canonical multiplications by ψ. The base-change formula and hψ make
these maps a compatible family. Full faithfulness in 088E lifts multiplication
uniquely from the tensor square to G. Lift the units from the structure-sheaf quotient
on the proper supporting subscheme; its reductions map to the finite structure algebras
because their annihilators contain this ideal. Faithfulness on the tensor cube, square
and G checks associativity, commutativity and the unit identities. Define the ring sheaf
on the additive sheaf of G using these operations, and its structure map using the unit.
Its underlying module is canonically isomorphic to G. The adjoints of ψ are ring maps
by the multiplication and unit identities. Their compatibility is hψ after adjunction.
On an affine U, the thickening has coordinate ring R/J with J the kernel of j_n.app U.
Tensor pullback is extension of scalars, so ψ identifies its section ring with
B(U)/JB(U); this is the displayed ring equivalence and its formula on quotient classes.
The empty affine chart and zero module obey the same formulas. No witness is selected
from a mere existence statement to define data: the ring operations on G are uniquely
determined by full faithfulness, and the ring sheaf is explicitly constructed from them.
(blueprint: lem-weil-pbc-finite-structure-algebra-lift). -/
theorem finite_structure_algebra_lift
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
    (hc : ∀ n : ℕ, c n = (Classical.choice (Scheme.Modules.nonempty_tensorPullbackComp (i n)
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 +
      1)))))))).symm ≪≫ eqToIso (congrArg Scheme.Modules.tensorPullback (hi n)))
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
    ∃ B : X.CommAlgebraSheaf, Nonempty (B.toModule ≅ G) ∧
      ∃ b : ∀ n, B ⟶ 𝒪⁎(fnY n ≫ pullback.fst f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))),
        (∀ (n : ℕ) (U : X.Opens), IsAffineOpen U →
          ∃ e : (B.right.obj.obj (op U) ⧸
              (RingHom.ker ((pullback.fst f
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))).app U).hom).map
                (B.hom.hom.app (op U)).hom) ≃+*
              Γ(Yn n, (fnY n ≫ pullback.fst f
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) ⁻¹ᵁ U),
            ∀ x, e (Ideal.Quotient.mk _ x) = ((b n).right.hom.app (op U)).hom x) ∧
        (∀ (n : ℕ) (U : X.Opens),
          (b (n + 1)).right.hom.app (op U) ≫
            (gn n).appLE ((fnY (n + 1) ≫ pullback.fst f
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⁻¹ᵁ U)
              ((fnY n ≫ pullback.fst f
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) ⁻¹ᵁ U)
              (by rw [← Scheme.Hom.comp_preimage, hw n]) =
            (b n).right.hom.app (op U)) := by sorry

end AlgebraicGeometry
