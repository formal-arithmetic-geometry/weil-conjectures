/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D9
-/
module

public import Sheaf.Paper.IntegralTwistDerivedScalarCanonical
public import Sheaf.Paper.CompletedLineTensorCoherence

/-! # Normalization of a common ordinary twist/scalar model

Source: blueprint `prop-weil-twist-preserves`, final integral/common-stage sentence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (S : Scheme.{u}) [∀ x : S, Invertible (l : S.residueField x)]
  (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
  (G : Type u) [Field G] [Algebra (Padic l) G] [FiniteDimensional (Padic l) G]
  (ι : E →ₐ[Padic l] F) (κ : F →ₐ[Padic l] G)

/-- A common chain representative computes the ordinary associator followed by
ordinary twisting and the single completion comparison. No completed associator,
completed twist square, identity comparison, or rationalization occurs in this assertion.
Source: blueprint `prop-weil-twist-preserves`, final common-stage sentence;
Steps 2--5 of `lem-weil-integral-twist-scalar-coherence`; Stacks Tags 06YY and 07A4.
(blueprint: lem-weil-integral-twist-common-scalar-model).

Proof: the signed twist line is locally free of rank one. Tensoring with it and
with its dual are inverse exact equivalences, so twisting preserves flat terms
and K-flatness. On the twisted representative P, use the ordinary associator
from CompletedLineTensor.associatorData, then the single-extension chain
comparison of integral_twist_derived_scalar for E to G. Their composite sends
c tensor (b tensor (x tensor y)) to (c*kappa(b) tensor x) tensor theta(y): first
apply the associator's tensor formula, then the single comparison's formula.
These are maps of sheaves, verified after sheafification and local tensor
generation, so the computation does not assume global tensors generate.
For the descent equation use the associator's universal-counit normalization
at the twisted P. Naturality moves the two ordinary scalar functors applied
to W(e.inv) and to the exact-twist factorization through this associator.
The single comparison's counit equation then leaves mu at W(C), followed by
alpha for E to G, W of its counit, and the inverse exact-twist factorization.
Compose with W of Q(completionChain) followed by the inverse resolving
comparison and scalar extension of e.hom. The factorization isomorphisms
cancel; naturality of the completion comparison moves e.hom back to C,
and e.inv followed by e.hom cancels. Its representative normalization
identifies the remaining composite with W(chi at C), as asserted. All
inverses here are derived comparison isomorphisms, never chain inverses
to completion. The argument also covers zero complexes, empty S, negative
or zero m, repeated fields, and arbitrary ramification. -/
theorem integral_twist_common_scalar_model (m : ℤ) :
    (∀ (C : sfIntegralConstructibleCategory l E S)
      (P : (integralOperationsGoodComplex l E S).FullSubcategory)
      (e : DerivedCategory.Q.obj P.obj ≅ C.obj),
      ∃ a : (completedOrdinaryScalarComplex l F G κ S).obj
          ((completedOrdinaryScalarComplex l E F ι S).obj
            (((integralSheafTwist l E S m).mapHomologicalComplex (.up ℤ)).obj P.obj)) ≅
        ((integralSheafTwist l G S m).mapHomologicalComplex (.up ℤ)).obj
          ((completedOrdinaryScalarComplex l E G (κ.comp ι) S).obj P.obj),
        (∀ (i : ℤ) (U : S.ProEtᵒᵖ)
          (b : (completedIntegralCommRingSheafUnrestricted l F S).obj.obj U)
          (c : (completedIntegralCommRingSheafUnrestricted l G S).obj.obj U)
          (x : (P.obj.X i).val.obj U) (y : (integralTwistLine l E S m).val.obj U),
          (a.hom.f i).val.app U
              (completedScalarTensorSection l F G κ S _ U c
                (completedScalarTensorSection l E F ι S _ U b
                  (SheafOfModules.siteSheafTensorTmul
                    (A := completedIntegralCommRingSheafUnrestricted l E S) _ _ U x y))) =
            SheafOfModules.siteSheafTensorTmul
              (A := completedIntegralCommRingSheafUnrestricted l G S) _ _ U
              (completedScalarTensorSection l E G (κ.comp ι) S _ U
                (c * (completedCoefficientMap l F G κ S).hom.app U b) x)
              ((twistScalarMaps l E S G (κ.comp ι) m).val.app U y)) ∧
        (completedDerivedScalarExtension l F G κ S).map
            ((completedDerivedScalarExtension l E F ι S).map
              ((integralSheafTwist l E S m).mapDerivedCategory.map e.inv)) ≫
          (completedDerivedScalarExtension l F G κ S).map
            ((completedDerivedScalarExtension l E F ι S).map
              ((integralSheafTwist l E S m).mapDerivedCategoryFactors.hom.app P.obj)) ≫
          (completedDerivedScalarExtension l F G κ S).map
            (completedScalarCounit l E F ι S
              (((integralSheafTwist l E S m).mapHomologicalComplex (.up ℤ)).obj P.obj)) ≫
          completedScalarCounit l F G κ S
            ((completedOrdinaryScalarComplex l E F ι S).obj
              (((integralSheafTwist l E S m).mapHomologicalComplex (.up ℤ)).obj P.obj)) ≫
          DerivedCategory.Q.map a.hom ≫
          (integralSheafTwist l G S m).mapDerivedCategoryFactors.inv.app
            ((completedOrdinaryScalarComplex l E G (κ.comp ι) S).obj P.obj) ≫
          (integralSheafTwist l G S m).mapDerivedCategory.map
            ((DerivedCategory.Q.map
                ((completedScalarChainComparison l E G (κ.comp ι) S).app P.obj) ≫
              (integralScalarExtensionComparisonOfUniverses l E G (κ.comp ι) S).inv.app P) ≫
              (integralScalarExtensionOfUniverses l E G (κ.comp ι) S).map e.hom) =
        (CompletedLineTensor.associatorData l E S F ι G κ).derived.hom.app
            ((integralSheafTwist l E S m).mapDerivedCategory.obj C.obj) ≫
          (integralTwistOrdinaryBeta l E G (κ.comp ι) S m).hom.app C ≫
          (integralSheafTwist l G S m).mapDerivedCategory.map
            ((completedScalarComparison l E G (κ.comp ι) S).app C.obj)) := by sorry

end WeilConjectures
