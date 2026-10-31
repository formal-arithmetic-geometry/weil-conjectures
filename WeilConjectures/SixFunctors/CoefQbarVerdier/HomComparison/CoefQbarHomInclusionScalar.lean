/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.HomComparison.CoefQbarVerdierHomComparisonComponents

/-! # Scalar compatibility of the canonical finite Hom inclusion

Source: the common-stage internal-Hom paragraph of def-weil-derived-pullback-tensor-hom
and the coefficient-transport step of thm-coef-qbar-verdier.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier.HomComparison
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The normalized Hom scalar comparison commutes with the canonical stage inclusions.
Source: the common-stage internal-Hom paragraph of def-weil-derived-pullback-tensor-hom;
thm-coef-qbar-verdier, coefficient transport in retained step 5.
(blueprint: lem-coef-qbar-hom-inclusion-scalar).

Proof: expand stageHomInclusion into the inverse of stageToSelf followed by removal
of its two self transitions. Express the displayed common-stage Hom arrow using
homToStage_naturality at a stage containing E and L. Expand homToStage into the
literal object equality, isoToStage and commonStageHomComparison. The tower equation
for the specified rational Hom scalar comparison identifies the two paths from the
coefficient compositum to that stage. Naturality moves the input transition
isomorphisms through Hom; the first input uses the inverse isomorphism because Hom
is contravariant there. The scalar Hom unit equation cancels the repeated-stage
unitors. The stage-system cocycle and inclusionTransition identify the remaining
output transition. Cancel the common target comparison to obtain the stated
identity. This uses no duality comparison, no evaluation or adjunction uniqueness,
and includes identity fields and zero input objects. -/
theorem stageHomInclusion_scalar (F : Finite D l hl Ω X)
    (E L : Index l Ω) (h : E ≤ L) (K M : Stage l Ω X E) :
    (inclusion L).map
        (rationalHomScalarComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) X
          ⟨(op K, M), (F.hom E).permitted K M⟩).hom ≫
      (stageHomInclusion l Ω X D hl F L).hom.app
        (op ((transition l Ω X E L h).obj K), (transition l Ω X E L h).obj M) ≫
      (commonStageDerivedInternalHom l Ω X).map
        (ObjectProperty.homMk
          (X := (stagePairs l Ω X D hl F L).obj
            (op ((transition l Ω X E L h).obj K), (transition l Ω X E L h).obj M))
          (Y := (stagePairs l Ω X D hl F E).obj (op K, M))
          (Prod.mkHom ((inclusionTransition l Ω X E L h).inv.app K).op
            ((inclusionTransition l Ω X E L h).hom.app M))) =
    (inclusionTransition l Ω X E L h).hom.app
        ((stageHom l Ω X D hl F E).obj (op K, M)) ≫
      (stageHomInclusion l Ω X D hl F E).hom.app (op K, M) := by sorry

end WeilConjectures.CoefQbarVerdier.HomComparison
