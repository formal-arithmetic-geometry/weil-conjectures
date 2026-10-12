/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase

import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec
import Sheaf.AlgebraicGeometry.FinitePushforwardCoherent
import Sheaf.AlgebraicGeometry.AffinePushforwardBaseChange
import Sheaf.AlgebraicGeometry.GrothendieckExistence
import Sheaf.Topology.PresheafModuleStalkFunctor
import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import Sheaf.AlgebraicGeometry.ModuleSupportProperOverBase
import Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.TensorPullbackTilde
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal

/-! # Algebraization of the structure algebras of a finite formal system

Source: Stacks Project, Cohomology of Schemes, Lemma 09ZT, proof via 088F and 088E
(blueprint: lem-weil-pbc-algebraize-finite-structure-algebra).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option autoImplicit false

set_option hygiene false in
local notation "𝒪⁎" g:max => Under.mk (⟨(g).c⟩ : Scheme.sheaf _ ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} (g).base).obj (Scheme.sheaf _))

/-- Algebraize the structure algebras, retaining the ring maps to each reduction.
Source: Stacks Project, Lemma 09ZT, proof through the construction of the algebra F;
Theorem 088E and Remark 088F.

Proof: The finite direct images of O_Yn are coherent on the locally Noetherian Xn.
Affine base change gives compatible algebra transition isomorphisms. Their first support
is closed and contained in the proper image of Y0, hence proper. Apply Grothendieck
existence to obtain a coherent module F with proper support and compatible reductions.
Choose a proper closed subscheme Z annihilating F. Tensor squares and cubes of F and
O_X/I_Z are coherent with proper support. Full faithfulness algebraizes multiplication
from F tensor F and the unit from O_X/I_Z. Faithfulness checks associativity, symmetry
and the unit identity on every reduction. This gives the commutative algebra B with
underlying module F. The adjoints of the reduction algebra isomorphisms give b_n.
On an affine open U, Xn is defined by ker(j_n.app U), and tensor reduction identifies
B(U)/ker(j_n.app U)B(U) with O_Yn(r_n inverse U). Hence b_n is surjective with the
stated kernel. Compatibility of the module comparisons, multiplication and units gives
the displayed equality with g_n sharp on sections. Empty affine opens and zero algebras
have zero section rings; the same quotient formulas apply.
(blueprint: lem-weil-pbc-algebraize-finite-structure-algebra). -/
theorem algebraize_finite_structure_algebra
    (A : Type u) [CommRing A] (I : Ideal A)
    [IsNoetherianRing A] [IsAdicComplete I A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Yn : ℕ → Scheme.{u})
    (fnY : ∀ n, Yn n ⟶ pullback f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    [∀ n, IsFinite (fnY n)]
    (gn : ∀ n, Yn n ⟶ Yn (n + 1))
    (hcart : ∀ n, IsPullback (fnY n) (gn n)
      (pullback.map f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
        f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) (𝟙 X)
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))))
        (𝟙 _) (by simp)
        (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
              Ideal.Quotient.factor_comp_mk]))
      (fnY (n + 1)))
    [IsProper (fnY 0 ≫ pullback.snd _ _)]
    (hw : ∀ n, gn n ≫ (fnY (n + 1) ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) =
      fnY n ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) :
    ∃ B : X.CommAlgebraSheaf,
      B.toModule.IsQuasicoherent ∧ RingedSpace.IsCoherent X.toRingedSpace B.toModule ∧
      Scheme.Modules.HasSupportProperOver f B.toModule ∧
      ∃ b : ∀ n, B ⟶ 𝒪⁎(fnY n ≫ pullback.fst f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))),
        (∀ (n : ℕ) (U : X.Opens), IsAffineOpen U →
          Function.Surjective ((b n).right.hom.app (op U)).hom ∧
          RingHom.ker ((b n).right.hom.app (op U)).hom =
            (RingHom.ker ((pullback.fst f
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))).app U).hom).map
              (B.hom.hom.app (op U)).hom) ∧
        (∀ (n : ℕ) (U : X.Opens),
          (b (n + 1)).right.hom.app (op U) ≫
            (gn n).appLE ((fnY (n + 1) ≫ pullback.fst f
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⁻¹ᵁ U)
              ((fnY n ≫ pullback.fst f
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) ⁻¹ᵁ U)
              (by rw [← Scheme.Hom.comp_preimage, hw n]) =
            (b n).right.hom.app (op U)) := by sorry

end AlgebraicGeometry
