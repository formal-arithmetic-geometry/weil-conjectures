/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H8
-/
module

public import Sheaf.Paper.IntegralHomReductionModels

/-! # Scalar reduction computed by a coefficient resolution

Source: Stacks Tags 06YY and 07A4; the coefficient resolution in paragraph 1 of
`lem-coef-integral-hom-reduction.proof.md`.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe d t u
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Tensor with a K-flat coefficient resolution computes restricted derived reduction,
without an internal Hom or any tensor presentation as input.

Source: Stacks 06YY, 07A4, 07A6 and 08J7; blueprint
`lem-coef-integral-hom-reduction.proof.md`, paragraph 1.
(blueprint: lem-sf-reduction-tensor-resolution-comparison).

Proof: on a K-flat complex A, tensor the supplied augmentation with A. Its
localization is invertible by K-flatness of A. The ordinary balanced tensor
comparison identifies tensor with the restricted quotient unit with restriction
of scalar extension of A. The left-derived counit and the exact-restriction
factorization identify this with restricted derived reduction of Qloc(A).
For arbitrary C choose a K-flat resolution A -> C. Tensoring its augmentation
with the supplied K-flat Q is a quasi-isomorphism, so the preceding isomorphism
extends to C. Naturality on K-flat complexes, and the universal property of
localization, show that these comparisons extend to a natural isomorphism.
No boundedness or nonzero hypothesis on Q, C, the ring, or the site is used. -/
theorem reduction_tensor_resolution_comparison
    (n : ℕ) (Q : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (hQ : flat.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) Q)
    (epsilon : Q ⟶
      ((scalarReductionRestriction l E Y n).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor (scalarReductionTarget l E Y n) 0).obj
          (SheafOfModules.unit (integralCoefficientSheaf l E Y n))))
    (hepsilon : QuasiIso epsilon) :
    Nonempty (DerivedCategory.Q ⋙ integralDerivedReduction l E Y D hl n ⋙
        scalarReductionDerivedRestriction l E Y n ≅
      (totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).flip.obj Q ⋙
        DerivedCategory.Q) := by sorry

end WeilConjectures.IntegralHom
