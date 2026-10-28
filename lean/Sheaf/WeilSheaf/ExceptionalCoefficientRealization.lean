/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.WeilSheaf.CoefficientRealizationData
public import Sheaf.WeilSheaf.CoefficientEndpointObjects
public import WeilConjectures.WeilSheaf.LowerShriek

/-! # Ordinary equivariant realization at the exceptional constant pair

This is an ordinary derived comparison, prior to choosing any cohomological degree.
The Tate endpoint is not part of this statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
attribute [local instance 1100] CategoryTheory.instOverClass
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.ConstantPurityFrobenius
namespace WeilConjectures.NativeCoefficientCohomology

variable (P : PurityFiniteSetting.{u})
  (X₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [Fact (ringChar P.field.k₀ ≠ P.coefficients.l)]
  (c₀ : Compactification X₀.hom)
  (S : systems P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar X₀)

attribute [local instance] nativeStructureOver

/-- The normalized ordinary realization may be chosen so that it realizes the
exceptional constant pair with its actual inverse-exchange mate action.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction
paragraph; the first two steps of lem-sf-native-coefficient-cohomology-comparison.
(blueprint: lem-sf-exceptional-coefficient-realization)

Proof: restrict the fixed algebraic-closure isomorphism from P.coefficients.Qbar
to PadicAlgCl to every finite coefficient field. Scalar extension along these
restrictions, followed by the normalized ordinary realization, gives a coherent
cocone. Its balanced scalar associators descend the functor on common-stage
objects and representative arrows. Pull back through the geometric-fibre
isomorphism induced by IsAlgClosure.equiv over the finite base field, and undo
the section-module equivalence. This constructs the ordinary functor. The finite
integral representative formulas show full faithfulness, exactness, shift
compatibility and preservation of bounded constructibility. The realization
family's normalized comparison for arbitrary scheme isomorphisms includes
geometric Frobenius. Transport it through the section-module equivalence and
the geometric-fibre isomorphism to obtain the displayed natural isomorphism.
Its shift law follows from the same integral representative maps. The scalar
unit and pullback-unit normalizations give Data.unit.

Apply native_exceptional_forgetful at the constant point object. Its comparison
is normalized by the native counit and the ordinary adjunction counit. The
scalar_frobenius_counit theorem identifies the ordinary left comparison's
Frobenius square, including the scalar-unit comparison. Transpose the native
counit's equivariance through the ordinary adjunction Hom equivalence. Its
injectivity identifies the transported right action with exceptionalIso followed
by G of the constant action. Thus the ordinary comparison intertwines the two
invertible actions and lifts to an isomorphism of ordinary derived pairs. This
works for each supplied native adjunction; it does not identify native derived
morphism groups with morphisms between ordinary pairs. Neither this construction
nor the counit argument requires smoothness. Identity and empty models use the
same unit and counit equations. -/
theorem exceptional_realization :
    ∃ R : CoefficientRealization.Data P X₀,
      ∀ (J : WeilComplex P.field.k₀ P.coefficients.l (Spec (.of P.field.k₀)) ⥤
          WeilComplex P.field.k₀ P.coefficients.l X₀.left)
        (adj : WeilComplex.derivedLowerShriek P.field.k₀ P.coefficients.l X₀.hom ⊣ J),
        Nonempty
          ((NativePairCohomology.native P.field.k₀ P.coefficients.l X₀.left).obj
              (J.obj (WeilSheaf.toComplex.obj
                (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l
                  (Spec (.of P.field.k₀))))) ≅
            (CoefficientRealization.pairs P X₀ R).obj (exceptionalConstant P X₀ c₀ S)) := by sorry

end WeilConjectures.NativeCoefficientCohomology
