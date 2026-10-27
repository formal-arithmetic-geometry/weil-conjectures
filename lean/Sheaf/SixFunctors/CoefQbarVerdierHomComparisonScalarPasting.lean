/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.CoefQbarVerdierHomComparisonComponents
import Sheaf.SixFunctors.RationalHomScalarEvaluation

/-! # Pasting the finite Hom scalar square into the common-stage component square

Source: blueprint thm-coef-qbar-verdier, retained proof step 5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CoefQbarVerdier.HomComparison
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (inclusion stageSystem)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Pasting lemma for the specified finite Hom scalar comparison.
Source: coefficient-transport paragraph of blueprint thm-coef-qbar-verdier,
retained thm-coef-qbar-verdier step 5.
(blueprint: lem-coef-qbar-verdier-hom-comparison-scalar-pasting).

Proof: expand the three factors in `component` and paste the finite Hom
scalar evaluation square with the beta and omega transition equations. The
remaining categorical cancellations are the unit and tower equations of the
specified Hom comparisons and the canonical inclusion-transition isomorphisms. -/
theorem component_extension_of_scalar_compatibility
    (B : Duality D l hl Ω X)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X)
    (L : Index l Ω) (h : K.stage ≤ L)
    (hs : RationalOperations.HomScalarCompatibility l
      (Coefficient.{u} l Ω K.stage) X D hl (Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω K.stage L h)
      (B.finite.omega K.stage) (B.finite.omega L)
      (B.finite.datum K.stage) (B.finite.datum L)
      (B.finite.hom K.stage) (B.finite.hom L)) :
    B.duality.dual.map ((stageSystem l Ω X).isoToStage K h).hom.op ≫
        (component l Ω X D hl B K).hom =
      (component l Ω X D hl B ((inclusion L).obj (K.toStage h))).hom ≫
        (homDual l Ω X B.omega (fun M ↦
          allPairs l Ω X D hl B.finite M B.omega)).map
          ((stageSystem l Ω X).isoToStage K h).hom.op := by
  sorry

end WeilConjectures.CoefQbarVerdier.HomComparison
