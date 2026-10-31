/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeConstructibleExceptionalInverseImage
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientCoherence

/-! # Constructible exceptional adjunction and coefficients -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures
namespace ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Compact support and the constructible exceptional functor form the specified
coefficient-compatible exact adjunction on the actual finite-Tor categories.
Source: current blueprint, sec-six-functors-basics, exceptional inverse image;
etale coefficient systems as in Zheng, Lemma 5.22
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients).

Proof (the three steps of the node):
1. `exists_coefficient_construction` (lem-sf-constructible-exceptional-coefficient-construction)
supplies the normalized record `P`: ring-stage operations, left realizations, finite right
functors, integral and rational compact-support realizations, scalar functors,
counit-normalized comparisons, common-field comparisons and refinement maps.
2. `coefficient_construction_coherence` (lem-sf-constructible-exceptional-coefficient-coherence),
applied to the same `P`, supplies the ring and rational scalar-composition cocycles and identity
laws, the common-field left and right cocycles, and the refinement identity and composition laws.
3. Assemble `System`: copy the operation, realization, scalar and refinement data from `P`,
complete each counit-normalized comparison by its adjunction transpose identities (`complete`),
and fill the ring, field, common-field and refinement law fields with the clauses of step 2.
-/
theorem exists_system (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Nonempty (System.{u, v} l Ω D hl (f := f)) := by
  obtain ⟨P⟩ := exists_coefficient_construction.{u, v} l Ω D hl (f := f)
  have H := coefficient_construction_coherence.{u, v} l Ω D hl (P := P)
  let R : RingSystem.{u, v} l Ω D hl (f := f) := {
    operation := P.ring.operation
    left := P.ring.left
    finiteRight := P.ring.finiteRight
    integralLeft := P.ring.integralLeft
    integralLeft_normalized := P.ring.integralLeft_normalized
    rationalLeft := P.ring.rationalLeft
    scalar := P.ring.scalar
    finiteScalar_eq := P.ring.finiteScalar_eq
    finiteScalar_normalized := P.ring.finiteScalar_normalized
    integralScalar_eq := P.ring.integralScalar_eq
    integralScalar_normalized := P.ring.integralScalar_normalized
    comparison := fun c {s t} a ha ↦
      (P.ring.comparison c (s := s) (t := t) a ha).complete l Ω
    comparison_normalized := P.ring.comparison_normalized
    scalarComposition := P.ring.scalarComposition
    cocycle := H.ring.cocycle
    scalarIdentity := P.ring.scalarIdentity
    identityLeft := H.ring.identityLeft
    identityRight := H.ring.identityRight
  }
  let F : FieldSystem.{u, v} l Ω D hl R := {
    rationalizationComparison := fun c E ↦ (P.fields.rationalizationComparison c E).complete l Ω
    rationalization_normalized := P.fields.rationalization_normalized
    rationalComparison := fun c E L i ↦ (P.fields.rationalComparison c E L i).complete l Ω
    rational_normalized := P.fields.rational_normalized
    rationalCocycle := H.fields.rationalCocycle
    rationalIdentityLeft := H.fields.rationalIdentityLeft
    rationalIdentityRight := H.fields.rationalIdentityRight
  }
  let M : CommonSystem.{u, v} l Ω D hl R F := {
    commonComparison := fun c i ↦ (P.common.commonComparison c i).complete l Ω
    common_normalized := P.common.common_normalized
    commonCocycleLeft := H.common.commonCocycleLeft
    commonCocycleRight := H.common.commonCocycleRight
  }
  let N : RefinementSystem.{u, v} l Ω D hl R F M := {
    refinement := P.refinements.refinement
    refinement_normalized := P.refinements.refinement_normalized
    refinementRational := P.refinements.refinementRational
    refinementCommon := P.refinements.refinementCommon
    refinementIdentity := H.refinements.refinementIdentity
    refinementComposition := H.refinements.refinementComposition
  }
  exact ⟨{ ring := R, fields := F, common := M, refinements := N }⟩

end ConstructibleExceptionalCoefficients
end WeilConjectures
