/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import all WeilConjectures.SixFunctors.IntegralHom.Tensor.TensorHomEvaluationExt

/-! # Equality of Hom-complex maps detected by homogeneous local evaluation

## Implementation details

Maps are compared degreewise; each degree of the Hom complex is a product of internal Hom
objects, whose projections are jointly injective, and identity-slice evaluation detects maps
into each internal Hom since naturality recovers every other slice.

## References

* Stacks Project, Tags 03EK, 03EO.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom
attribute [local implicit_reducible] homComplex evaluate projection
attribute [local irreducible] homComplexFunctor

/-- Homogeneous evaluations over identity slices detect maps into a Hom complex: two chain maps
into `Hom(A, I)` with the same evaluations on all local sections are equal. -/
theorem homComplex_evaluation_ext
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (A I X : CochainComplex (Modules.{t, u} Y R) ℤ)
    (f g : X ⟶ homComplex (R := R) A I)
    (h : ∀ (n p : ℤ) (U : Y.ProEtᵒᵖ) (v : (X.X n).val.obj U)
      (x : (A.X p).val.obj U),
      evaluate Y R A I n p U ((f.f n).val.app U v) x =
        evaluate Y R A I n p U ((g.f n).val.app U v) x) : f = g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ((Classical.choose_spec
    (homComplex_projections_exists.{t + 1, t, max u (t + 1), max u (t + 1)}
      (R := R))).1 A I n).some.hom_ext
  intro ⟨p⟩
  apply SheafOfModules.hom_ext
  apply hom_eval_ext
  intro U v x
  exact h n p U v x

end WeilConjectures.IntegralHom
