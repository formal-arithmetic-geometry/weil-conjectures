/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.Algebra.Homology.TwoTermFreeHomTensorComponents

/-! # Normalization of Hom reduction on fixed chain representatives

Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraphs 1--2.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The localized signed map is the normalized reduction comparison, for fixed
resolutions and a fixed augmented two-term coefficient resolution.

Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraphs 1--2;
Stacks Tags 07A6, 08J7 and 08J9
(blueprint: lem-sf-integral-hom-representative-square).

Proof: the augmentation identifies Q with the finite coefficient unit after
restriction of scalars. Its two free terms make Q K-flat, and make I tensor Q
K-injective: it is the cone, with the appropriate shift, of the multiplication
map on I. Thus Hom(P,I) and Hom(P,I tensor Q) compute the two needed derived
internal Homs. Resolve Hom(P,I) by a K-flat complex when applying the tensor
presentation. The augmentation and the canonical derived scalar counit give
the source comparison s. For t, first apply the scalar internal-Hom adjunction
on every slice, then the same augmentation and the Hom localization comparison.
Transport these comparisons along eP and eI. They are isomorphisms because the
augmentations are quasi-isomorphisms, Q is K-flat, and the Hom targets are
K-injective. To check the square, transpose through the target tensor-Hom
adjunction and test using K-flat representatives. The evaluation condition in
a and the scalar-unit normalization in m identify both composites with the
reduction of evaluation. The signed formula for f gives the Koszul sign from
moving the coefficient factor across P; it cancels precisely the evaluation
ordering sign. The augmentation is used on both sides, so its chosen quotient
identification cancels too. Injectivity of the adjunction Hom equivalence gives
the equality. No invertibility of f is asserted or used. -/
theorem comparison_representative_square
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))
    (n : ℕ) (m : ReductionPresentation l E Y D hl a n)
    (K L : completedIntegralDerivedCategory l E Y D hl)
    (P I Q : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (hP : flat.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) P) (hI : I.IsKInjective)
    (eP : DerivedCategory.Q.obj P ≅ K)
    (eI : DerivedCategory.Q.obj I ≅ L)
    (hQ : flat.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) Q)
    (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
    (eNeg : Q.X (-1) ≅ (show completedIntegralModuleSheaves l E Y D hl from
      SheafOfModules.unit (completedIntegralCoefficientSheaf l E Y D hl)))
    (eZero : Q.X 0 ≅ (show completedIntegralModuleSheaves l E Y D hl from
      SheafOfModules.unit (completedIntegralCoefficientSheaf l E Y D hl)))
    (epsilon : Q ⟶
      ((scalarReductionRestriction l E Y n).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor (scalarReductionTarget l E Y n) 0).obj
          (SheafOfModules.unit (integralCoefficientSheaf l E Y n))))
    (hepsilon : QuasiIso epsilon)
    (f : ((totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj
          (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)}
            (R := completedIntegralCommRingSheaf l E Y D hl) P I)).obj Q ⟶
        homComplex.{t + 1, t, max u (t + 1), max u (t + 1)}
          (R := completedIntegralCommRingSheaf l E Y D hl) P
          (((totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj I).obj Q))
    (hf : IsSignedHomTensor Y (completedIntegralCommRingSheaf l E Y D hl) P I Q f) :
    let R := completedIntegralCommRingSheaf l E Y D hl
    let U := scalarReductionDerivedRestriction l E Y n
    let F := integralDerivedReduction l E Y D hl n
    ∃ (s : U.obj (F.obj ((hom.{t, u} Y R).obj (op K, L))) ≅
          DerivedCategory.Q.obj (((totalTensor.{t, u} Y R).obj
            (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)).obj Q))
        (t : U.obj ((hom.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)).obj
            (op (F.obj K), F.obj L)) ≅
          DerivedCategory.Q.obj
            (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P
              (((totalTensor.{t, u} Y R).obj I).obj Q))),
      U.map (comparison l E Y D hl m K L) ≫ t.hom =
        s.hom ≫ DerivedCategory.Q.map f := by sorry

end WeilConjectures.IntegralHom
