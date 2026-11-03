/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeExceptionalCompactSupportFinite

/-! # Integral transition equation for the specified compact-support scalar map -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard Padic
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
set_option allowUnsafeReducibility true in
attribute [local irreducible] WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageSystem
attribute [local instance 2000] Shrink.instField
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients

variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (source : Realization l X) (target : Realization l Y)
  (S : System.{u, 0} l (PadicAlgCl l) D hl (f := f)) (c : Compactification f)

/-- Integral-normalized finite scalar comparisons commute with field transitions.
Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15, common-field comparison;
step 3 of lem-sf-native-exceptional-compact-support-realization.
(blueprint: lem-sf-native-exceptional-compact-support-integral-transition).

Proof: represent the rational input by its unchanged underlying integral object.
Integral residue Tor regards this object as finite-Tor without changing it. Apply
faithful derived sections and insert the supplied integral component formulas.
The image of each integral map is its defining composite of inverse commonComparison,
rationalLeft, target integral realization, inverse completed compact-support
realization, the proper/open scalar mate, inverse source integral realization, and
inverse operationTransport. Insert S.common.commonCocycleLeft to move the closed
operation across the transition. The source and target common_field equations,
S.fields.rational_normalized and integralLeft_normalized identify the remaining
terms with the integral scalar square. The coefficient_scalar equations identify
successive integral-to-native maps with the direct one. The balanced tensor
associator, completion comparison and proper counit triangle identities identify
the proper scalar mates with their composite, as in comparison_composition. The
open comparison is the tensor-unit-normalized extension-by-zero map. Cancel the
intervening realization boundaries and reflect equality through faithful sections.
The integral component formula then gives precisely the displayed equality for
alpha. Repeated fields use the same tensor unit; zero inputs and empty schemes use
the same equations. This statement asserts only transition compatibility for a
supplied normalized family, not existence, invertibility, localization or descent. -/
-- STATEMENT-DISPUTED: System permits independent signs of rationalLeft at each field.
-- The signedSystem construction above preserves every System law, but changes the
-- prescribed integral component by that sign, by linearity of its defining composite.
-- At two fields
-- with different signs the equality cannot hold for both families when the
-- displayed right-hand composite is unequal to its negative.
-- transition_sign_obstruction isolates this conditional failure.
-- CoefficientConstructionNormalization.localizationIdentity would exclude this
-- freedom, but exists_system does not retain it in FieldSystem or System.
-- The checked obstruction above is conditional on distinct endpoint signs and a
-- component that is not its own negative; it does not construct a concrete scheme.
theorem systemFiniteTransition [G : NativeGeometry.{u} l]
    [∀ x : X, Invertible (l : X.residueField x)]
    (change : ∀ E : Index l (PadicAlgCl l),
      PurCompactSupport.Change (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (ha : ∀ (E : Index l (PadicAlgCl l)) (T : Scheme.{u})
      (C : CoefficientPresentation l T (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)),
      (change E).map T = C.integralMap l T)
    (alpha : ∀ E : Index l (PadicAlgCl l),
      systemFiniteSource l D hl target S c E ≅ systemFiniteTarget l source c E)
    (halpha : ∀ (E : Index l (PadicAlgCl l))
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
      (alpha E).hom.app ((sfRationalConstructibleLocalization l
        (Coefficient.{u} l (PadicAlgCl l) E) X).obj K) =
        (systemIntegralMap l D hl source target S c E (change E)
          (ha E X (source.coefficient E)) (ha E Y (target.coefficient E))).app K)
    (A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X)
    (E : Index l (PadicAlgCl l)) (h : A.stage ≤ E) :
    ((S.ring.operation c .closed).F ⋙ target.J).map
        (StageSystem.isoToStage
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X) A h).hom ≫
        (alpha E).hom.app (A.toStage h) =
      (alpha A.stage).hom.app A.obj ≫ (source.J ⋙ actual l c).map
        (StageSystem.isoToStage
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
          A h).hom := by sorry

end WeilConjectures.LocallyFiniteAdicCompactSupport
