/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.Paper.IntegralHomReductionModels
public import Sheaf.Paper.CoefficientRingedTensorHomModel
import all Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction

/-! # Pure-section normalization of the chain tensor--Hom equivalence

Source: Stacks Tag 08J9 and blueprint `lem-coef-integral-hom-reduction.proof.md`,
paragraphs 1--2.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.homComplexFunctor

universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom

variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})

attribute [local instance 2000] abSheafify abLocallyBijective

/-- The chain tensor--Hom equivalence evaluates pure tensors without a sign when
its tensor factors are ordered as parameter first and Hom input second.
Source: Stacks Tag 08J9 and blueprint `lem-coef-integral-hom-reduction.proof.md`,
paragraphs 1--2
(blueprint: lem-sf-hom-complex-tensor-pure-equivalence).

Proof: use the constructed chain tensor--Hom equivalence. Its inverse sends a
map into the Hom complex to evaluation on each homogeneous tensor generator.
Apply this inverse formula to the image of a chain map; the inverse-image
identity for an equivalence gives the displayed formula. The Hom-complex sign
and the braiding sign cancel in this ordering. -/
theorem homComplexTensor_pure_equivalence
    (A L N : CochainComplex (Modules.{t, u} Y R) ℤ) :
    ∃ e : ((((totalTensor.{t, u} Y R).obj A).obj L) ⟶ N) ≃
        (A ⟶ homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) L N),
      ∀ (psi : (((totalTensor.{t, u} Y R).obj A).obj L) ⟶ N)
        (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
        (x : (A.X i).val.obj U) (y : (L.X j).val.obj U),
        evaluate.{t, u} Y R L N i j U (((e psi).f i).val.app U x) y =
          (psi.f (j + i)).val.app U
            (coefficientTensorGenerator.{u, t + 1, t}
              (AlgebraicGeometry.Scheme.ProEt.topology Y) R
              A L i j (j + i) (add_comm i j) U x y) := by
  let e := RingedDerivedNative.chainEquiv.{t + 1, t, u}
    (AlgebraicGeometry.Scheme.ProEt.topology Y) R A L N
  refine ⟨e, ?_⟩
  intro psi i j U x y
  have he := RingedDerivedNative.chainEquiv_symm_pure.{t + 1, t, u}
    (AlgebraicGeometry.Scheme.ProEt.topology Y) R A L N (e psi)
    i j (j + i) (add_comm i j) rfl U x y
  change ((e.symm (e psi)).f (j + i)).val.app U _ = _ at he
  rw [Equiv.symm_apply_apply] at he
  exact he.symm

end WeilConjectures.IntegralHom
