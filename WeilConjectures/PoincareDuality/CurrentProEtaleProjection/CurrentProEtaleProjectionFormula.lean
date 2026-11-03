/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalLocalizingProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowProEtaleComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
import WeilConjectures.AlgebraicGeometry.ProEtalePfAdmissibleModels
import WeilConjectures.AlgebraicGeometry.Projection.ProjectionComparisonEtaleOrigin
import WeilConjectures.AlgebraicGeometry.DetFiniteCondensedProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperProjectionFormulaField

/-! # The current finite and condensed pro-etale projection formula

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-pf-proetale,
statement and proof (blueprint: sk-thm-sf-pf-proetale).

The finite clause retains the supplied etale antecedents and their finite Tor intervals.
It uses the canonical projection in fixed-scalar sheaf coordinates; the intrinsic finite
projection is its image under the canonical module equivalence. The other three clauses
use internal modules over the pulled-back condensed rings and constant-model constructibility.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CurrentProEtaleProjection

/-- The finite-coefficient assertion, with specified etale-origin witnesses. The ring is
exactly the recorded quotient O_E / (varpi_E)^n, lifted only to the sheaf value universe.
Both endpoint bounds are included so that invertibility is asserted in D+, not merely D.
Source: current blueprint sk-thm-sf-pf-proetale, finite clause
(blueprint: sk-thm-sf-pf-proetale). -/
def finiteAssertion (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : Prop :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  ∀ (K : DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (wK : FixedEtaleOriginWitness X A K) (wL : FixedEtaleOriginWitness Y A L)
    (_hK : Etale.DerivedCategory.isBoundedConstructible A X wK.complex.obj)
    (_hL : Etale.DerivedCategory.isBoundedConstructible A Y wL.complex.obj)
    (_tK : ∃ a b : ℤ, Etale.DerivedCategory.hasTorAmplitudeIn A X a b wK.complex.obj)
    (_tL : ∃ a b : ℤ, Etale.DerivedCategory.hasTorAmplitudeIn A Y a b wL.complex.obj),
    ∃ (hS : DerivedCategory.TStructure.t.plus
        (((ProEtale.derivedTensorRightDerivedLowerShriek (ModuleCat.{u + 1} A) c).obj
          K.obj).obj L.obj))
      (hT : DerivedCategory.TStructure.t.plus
        (((ProEtale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
          (ModuleCat.{u + 1} A) c).obj K.obj).obj L.obj)),
      IsIso (ObjectProperty.homMk
        (((ProEtale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app K.obj).app
          L.obj) :
        (⟨_, hS⟩ : DerivedCategory.Plus (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A))) ⟶
          ⟨_, hT⟩)

/-- The condensed assertion is invertibility of the existing counit/open composite on
bounded constant-model constructible internal modules. The coefficient ring is pulled
back from the condensed point; tensor and pullback are the ordinary relative operations.
Source: current blueprint sk-thm-sf-pf-proetale, non-finite clause
(blueprint: sk-thm-sf-pf-proetale). -/
def condensedAssertion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : Prop :=
  ∀ (K : ProEtale.ConstantModelBoundedConstructible Λ X)
    (L : ProEtale.ConstantModelBoundedConstructible Λ Y),
    IsIso (ProEtale.CondensedRing.exceptionalProjectionMorphismOfCompactification
      Λ c K.obj L.obj)

/-- The projection formula for A_{E,n}, and directly for condensed O_E, E and Qbar_l.
The compactification is arbitrary. Only the condensed clauses require separated
structure morphisms; the finite clause requires only separatedness of f.

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-pf-proetale,
statement and proof (blueprint: sk-thm-sf-pf-proetale).

Proof: retain the supplied etale representatives and comparison isomorphisms. Exact
comparison gives intrinsically constructible pro-etale realizations and transports
both Tor intervals unchanged. The admissible-model lemma supplies bounded-below
models for open extension and its tensor with proper pullback. The projection
comparison equation identifies the pro-etale arrow with the etale projection,
conjugated by the compact-support and tensor comparisons. The proper etale projection
and open tensor comparison are invertible for the arbitrary supplied compactification.
All conjugating arrows are isomorphisms. Its endpoints lie in D+ by the same Tor bounds
and preservation of D+ under comparison. Naturality conjugates by the supplied origins.
For condensed coefficients, open extension preserves bounded constructibility. The
identification Dctf = Dbc places both proper-factor inputs in the localizing domain.
Apply the integral or field proper projection formula, then proper pushforward of the
open tensor isomorphism and the pullback compositor. This is exactly the existing
compactification projection morphism, hence is invertible. -/
theorem projection_formula
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f) :
    (∀ (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
      (n : ℕ) (hn : 1 ≤ n), finiteAssertion l E n hn c) ∧
    (∀ [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))],
      (∀ E : PadicAlgCl.FiniteIntermediateField l,
        condensedAssertion (Profinite.padicIntegersRingObj l E) c) ∧
      (∀ E : PadicAlgCl.FiniteIntermediateField l,
        condensedAssertion (Profinite.continuousMapRingObj E) c) ∧
      condensedAssertion (Profinite.padicAlgClRingObj l) c) := by
  sorry

end WeilConjectures.CurrentProEtaleProjection
