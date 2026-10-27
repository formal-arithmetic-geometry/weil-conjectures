/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Sheaf.Paper.IntegralLfpConstantModelComparison
public import Sheaf.Paper.AdicStratifiedPerfectData
public import Sheaf.AlgebraicGeometry.IntegralConstantCompletion
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.InternalSectionTotalComparison
public import Sheaf.Paper.FiniteDiscreteOrdinaryEncoding
public import Sheaf.Paper.CompletedIntegralCoefficients
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.IntegralCohomologicalAdicCriterion
import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
import Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence
import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import Mathlib.Order.CompletePartialOrder

/-!
# General locally finitely presented integral inputs have adic residue witnesses

Source: Bhatt--Scholze, Definitions 6.5.1, 6.8.10 and Proposition 6.8.11(3),
with the integral lfp/constant-model comparison
(blueprint: lem-sfb-general-lfp-adic-input-witness).

The input is an ordinary derived internal module over the actual pulled-back continuous
integral ring. The conclusion supplies the scalar-normalized coefficient isomorphism to
its quotient limit and reads the same object in the existing ringed-site presentation.

## Main definitions and statement

* `GeneralLfpAdicInput.IsNormalized`: the constant-scalar normalization.
* `GeneralLfpAdicInput.transport`: the actual termwise coefficient encoding.
* `GeneralLfpAdicInput.IsAdicRepresentative`: the published adic predicate after localization.
* `GeneralLfpAdicInput.HasResidueComparison`: the normalized finite-residue encoding.
* `generalLfpAdicInputWitness`: the general-lfp adic input witness.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale
namespace GeneralLfpAdicInput

/-- The coefficient comparison fixes every constant integral scalar. The source integers
are lifted only to the coefficient universe; `WithAbs` changes the topology-bearing type,
not the value. Fixing these scalars fixes all finite quotients and therefore the limit map.
Source: Bhatt--Scholze, Section 6.5 and Lemma 4.2.12; integral-limit clause of the node
(blueprint: lem-sfb-general-lfp-adic-input-witness). -/
def IsNormalized (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (c : Scheme.adicLisseCompletedRing X (IntegralConstantCompletion.ideal l E) ≅
      ModuleObjectRingedComparison.ring.{u} (integralCondensedRing.{u} l E) X) : Prop :=
  ∀ (U : X.ProEtᵒᵖ) (a : latticeCoefficientIntegers l E),
    c.hom.hom.app U
      ((Scheme.CompletedConstantReduction.base X (IntegralConstantCompletion.ideal l E)).hom.app U
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (IntegralConstantCompletion.integers l E)))).app U
          (ULift.up ⟨(WithAbs.equiv (Padic.coefficientExtensionAbsoluteValue l E)) a.val,
            a.property⟩))) =
      (FiniteDiscreteOrdinary.canonicalAbelianMap (latticeCoefficientIntegers l E) X).hom.app U
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (latticeCoefficientIntegers l E))))).app U
          (ULift.up a))

/-- The termwise section-action encoding followed by restriction along the normalized
coefficient isomorphism. Localization reads a representative of the same input object;
no completion is performed.
Source: Stacks 00YV, 05QI and 07A6; Bhatt--Scholze, Section 6.5
(blueprint: lem-sfb-general-lfp-adic-input-witness). -/
def transport (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (c : Scheme.adicLisseCompletedRing X (IntegralConstantCompletion.ideal l E) ≅
      ModuleObjectRingedComparison.ring.{u} (integralCondensedRing.{u} l E) X) :
    CochainComplex
        (ModuleObjectRingedComparison.Internal.{u} (integralCondensedRing.{u} l E) X) ℤ ⥤
      CochainComplex (Scheme.proEtaleRingModules.{u} X
        (Scheme.adicLisseCompletedRing X (IntegralConstantCompletion.ideal l E))) ℤ :=
  ModuleObjectRingedComparison.complexForward.{u} (integralCondensedRing.{u} l E) X ⋙
    (SheafOfModules.restrictScalars.{u + 1, u, u + 1, u + 1}
      ((Scheme.adicLisseForget X).map c.hom)).mapHomologicalComplex (.up ℤ)

/-- The published adic predicate on a completed-ring cochain representative, using its
standard localization and the coefficient-sized abelian instance explicitly. This only
fixes instance elaboration; it is the existing local-completeness and residue predicate.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: lem-sfb-general-lfp-adic-input-witness). -/
def IsAdicRepresentative (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (P : CochainComplex (Scheme.proEtaleRingModules.{u} X
      (Scheme.adicLisseCompletedRing X (IntegralConstantCompletion.ideal l E))) ℤ) : Prop :=
  letI : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X
  letI : Abelian (Scheme.proEtaleRingModules.{u} X
      (Scheme.adicLisseCompletedRing X (IntegralConstantCompletion.ideal l E))) :=
    SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1}
      ((Scheme.adicLisseForget X).obj
        (Scheme.adicLisseCompletedRing X (IntegralConstantCompletion.ideal l E)))
  letI : HasDerivedCategory.{u + 2} (Scheme.proEtaleRingModules.{u} X
      (Scheme.adicLisseCompletedRing X (IntegralConstantCompletion.ideal l E))) :=
    Scheme.proEtaleRingModules_hasDerivedCategory X
      (Scheme.adicLisseCompletedRing X (IntegralConstantCompletion.ideal l E))
  Scheme.IsSfbAdicConstructible.{u} X (IntegralConstantCompletion.ideal l E)
    ((@DerivedCategory.Q.{u + 2, u + 1, u + 2}
      (Scheme.proEtaleRingModules.{u} X
        (Scheme.adicLisseCompletedRing X (IntegralConstantCompletion.ideal l E))) _
      (SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1}
        ((Scheme.adicLisseForget X).obj
          (Scheme.adicLisseCompletedRing X (IntegralConstantCompletion.ideal l E))))
      (Scheme.proEtaleRingModules_hasDerivedCategory X
        (Scheme.adicLisseCompletedRing X (IntegralConstantCompletion.ideal l E)))).obj P)

/-- The finite residue uses the normalized constant-ring encoding. Its derived equivalence
is monoidal, preserves every ordered Tor interval, and identifies the finite constant
local models. The discrete topology is part of the residue-coefficient convention.
Source: Bhatt--Scholze, Section 6.5, coefficient convention before Definition 6.5.1
(blueprint: lem-sfb-general-lfp-adic-input-witness). -/
def HasResidueComparison (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) : Prop :=
  letI : TopologicalSpace (Padic.coefficientExtensionRing l E 1) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing l E 1) := ⟨rfl⟩
  ∃ e : FiniteDiscreteOrdinary.Encoding (Padic.coefficientExtensionRing l E 1) X,
    Nonempty (e.fixedDerived.functor.Monoidal) ∧
    (∀ (K : DerivedCategory
        (FiniteDiscreteOrdinary.Internal (Padic.coefficientExtensionRing l E 1) X))
      (a b : ℤ), a ≤ b →
      (DerivedCategory.torAmplitudeIn _ a b K ↔
        DerivedCategory.torAmplitudeIn _ a b (e.fixedDerived.functor.obj K))) ∧
    ∀ N : FiniteDiscreteOrdinary.Internal (Padic.coefficientExtensionRing l E 1) X,
      HasFiniteConstantLocalModel
          (FiniteDiscreteOrdinary.coefficient (Padic.coefficientExtensionRing l E 1)) X N ↔
        FiniteDiscreteOrdinary.ordinaryLocalModel (Padic.coefficientExtensionRing l E 1) X
          ((e.ordinary.functor ⋙ e.fixed.functor).obj N)

end GeneralLfpAdicInput

/-- Every bounded constructible general-lfp integral input has scalar-model constructible
cohomology, is locally derived complete, and has an étale constructible residue witness of
finite Tor amplitude. The canonical coefficient comparison is specified by its scalar
normalization and uniqueness. `IsSfbAdicConstructible` includes the actual derived residue
isomorphism and the Tor test against every degree-zero étale residue-module sheaf.

Source: Bhatt--Scholze, Definitions 6.5.1 and 6.8.10, Proposition 6.8.11(3);
Stacks 01T6 and 01OY (blueprint: lem-sfb-general-lfp-adic-input-witness).

Proof, following the five DAG steps:
1. A field is Noetherian. Affine quasi-compactness and finite type over a Noetherian scheme
   make X quasi-compact and locally Noetherian. Local Noetherianity gives quasi-separatedness;
   quasi-compactness extracts a finite affine Noetherian cover.
2. Apply `lem-weil-l-adic-extension-integers-dvr`. The uniformizer generates the maximal
   ideal, so A is its finite residue field. The extended absolute value of l is less than
   one; thus l vanishes in the nonzero residue field and its characteristic is l.
3. `det-prop-sfb-qlbar-colimit-x-integral-limit` identifies the pulled-back integral ring
   with the positive quotient limit. The finite-discrete coefficient equivalence identifies
   the residue with the constant field sheaf and preserves its relative tensor and models.
   Both coefficient maps fix constant scalars; finite quotient projections give uniqueness.
4. Apply `lem-sfb-integral-lfp-constant-model-comparison` to each cohomology sheaf. This
   changes arbitrary finite presentation matrices to scalar models, including torsion
   modules, without changing the complex or its bounds.
5. Apply implication (1) to (2) of `lem-sfb-integral-cohomological-adic-criterion`.
   `lem-sfb-module-object-ringed-site-derived-comparison` identifies the section-action
   encoding, its derived tensors and its slice restrictions with the given module objects.
   The output is local derived (t)-completeness and a bounded étale constructible residue
   complex with an isomorphism to the derived reduction and one ordered Tor interval for
   every degree-zero test sheaf. No completeness or scalar-model hypothesis is added.
-/
theorem generalLfpAdicInputWitness
    (l p : ℕ) [Fact l.Prime] [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    (_hpl : p ≠ l) (X : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (M : DerivedCategory.{u + 1, u + 1, u + 2}
      (ModuleObjectRingedComparison.Internal.{u} (integralCondensedRing.{u} l E) X.left))
    (_hM : boundedConstructible (condensedRingObj (integralCondensedRing.{u} l E) X.left) M) :
    (CompactSpace X.left ∧ IsLocallyNoetherian X.left ∧ QuasiSeparatedSpace X.left) ∧
    IsDiscreteValuationRing (Padic.coefficientExtensionIntegers l E) ∧
    IsField (Padic.coefficientExtensionRing l E 1) ∧
    Finite (Padic.coefficientExtensionRing l E 1) ∧
    CharP (Padic.coefficientExtensionRing l E 1) l ∧
    GeneralLfpAdicInput.HasResidueComparison l E X.left ∧
    (∀ q : ℤ, IsConstantModelConstructible (integralCondensedRing.{u} l E) X.left
      ((DerivedCategory.homologyFunctor _ q).obj M)) ∧
    ∃ c : Scheme.adicLisseCompletedRing X.left (IntegralConstantCompletion.ideal l E) ≅
        ModuleObjectRingedComparison.ring.{u} (integralCondensedRing.{u} l E) X.left,
      GeneralLfpAdicInput.IsNormalized l E X.left c ∧
      (∀ d, GeneralLfpAdicInput.IsNormalized l E X.left d → d = c) ∧
      ∃ P : CochainComplex
          (ModuleObjectRingedComparison.Internal.{u} (integralCondensedRing.{u} l E) X.left) ℤ,
        Nonempty ((DerivedCategory.Q.{u + 1, u + 1, u + 2}
          (C := ModuleObjectRingedComparison.Internal.{u}
            (integralCondensedRing.{u} l E) X.left)).obj P ≅ M) ∧
        GeneralLfpAdicInput.IsAdicRepresentative.{u} l E X.left
          ((GeneralLfpAdicInput.transport.{u} l E X.left c).obj P) := by
  sorry

end AlgebraicGeometry.ProEtale
