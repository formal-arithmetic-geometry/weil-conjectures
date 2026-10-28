/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y5
-/
module

public import Sheaf.Algebra.Homology.TwoTermFreeHomTensorComponents

/-! # Completed-ring representatives of reduced evaluation

Source: the finite-free calculation and evaluation sentence of
`lem-coef-integral-hom-reduction.proof.md`, paragraphs 1--2.
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
/-- The completed-ring reduction of evaluation is computed by signed chain evaluation.
This holds for an arbitrary K-flat coefficient resolution, with no boundedness
assumption on it. It contains no finite-coefficient internal Hom or comparison map.

Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraphs 1--2,
finite-free construction and compatibility with actual evaluation; Stacks 06YY,
07A4, 07A6, 08J7, 08J9 and 0A8X
(blueprint: lem-sf-integral-hom-reduced-evaluation-representative).

Proof: first tensor the augmentation epsilon with a K-flat representative A of
an arbitrary completed-ring complex C. The resulting quasi-isomorphism identifies
A tensor Q with A tensor the restricted quotient unit. Balanced scalar tensor
cancellation identifies the latter with restriction of ordinary extension of A.
The left-derived-to-ordinary scalar comparison is invertible on A. Tensoring a quasi-isomorphism
A -> C with Q is a quasi-isomorphism since Q is K-flat. These three comparisons
therefore give the normalized isomorphism from restricted derived reduction of
C to the localization of C tensor Q, independently of the K-flat resolution.
Apply this construction to I and to Hom(P,I), transporting by eI and by the
canonical Hom localization isomorphism and eP. These are r and s.

To verify the evaluation identity, resolve the testing complex by a K-flat
complex and represent its map into Hom(P,I) by a chain map, using the local
K-injective Hom computation. The evaluation field of a gives the factor
(-1)^(ij) in the order P tensor Hom(P,I). The formula hf for exchange adds
(-1)^(bp) when the coefficient degree b passes the input degree p. On total
degree i+j+b these are exactly the signs in the reduced evaluation. Apply the
ordinary scalar unit x -> 1 tensor x and the chain comparison in m.normalization:
its pure-tensor formula identifies the two evaluations before localization,
and its derived counit square identifies their localized composites. The
extension-restriction counit on F(Hom(K,L)) supplies the middle tensor map in
the displayed composite. Both composites use the same epsilon, so no choice of
quotient identification remains. Tensor-sheafification descent and the Hom
product projections extend the calculation from pure homogeneous sections to
chain maps; K-flat localization extends it to all testing maps. This proves the
displayed equality in the completed-ring derived category. Zero complexes,
the empty site, n=0 and a zero quotient require no separate nonvanishing premise. -/
theorem reduced_evaluation_representative
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))
    (n : ℕ) (m : ReductionPresentation l E Y D hl a n)
    (K L : completedIntegralDerivedCategory l E Y D hl)
    (P I Q : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (hP : flat.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) P) (hI : I.IsKInjective)
    (eP : DerivedCategory.Q.obj P ≅ K)
    (eI : DerivedCategory.Q.obj I ≅ L)
    (hQ : flat.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) Q)
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
    let adj := (derivedScalarExtensionRestrictionAdjunction l E Y n).choose
    let H := (hom.{t, u} Y R).obj (op K, L)
    let X := U.obj (F.obj H)
    let J := ((totalTensor.{t, u} Y R).obj I).obj Q
    ∃ (r : U.obj (F.obj L) ≅ DerivedCategory.Q.obj J)
      (s : X ≅ DerivedCategory.Q.obj (((totalTensor.{t, u} Y R).obj
        (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)).obj Q)),
      ((a.adjunction K).homEquiv X (U.obj (F.obj L))).symm
          (s.hom ≫ DerivedCategory.Q.map f ≫ homModelMap.{t, u} Y R P J ≫
            (hom.{t, u} Y R).map (Prod.mkHom eP.inv.op r.inv)) =
        adj.homEquiv (a.tensor.obj (K, X)) (F.obj L)
          (m.mu.hom.app (K, X) ≫
            m.target.tensor.map (Prod.mkHom (𝟙 (F.obj K)) (adj.counit.app (F.obj H))) ≫
            m.mu.inv.app (K, H) ≫ F.map ((a.adjunction K).counit.app L)) := by sorry

end WeilConjectures.IntegralHom
