/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence
import Sheaf.Paper.IntegralLfpConstantModelComparison
import Sheaf.Paper.IntegralCohomologicalAdicCriterion
import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
import Sheaf.Algebra.Homology.RingedInternalHomDerivedComplete
import Sheaf.Paper.IntegralHomReduction
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
import Sheaf.Paper.FiniteFieldInternalHomFiniteness
import Sheaf.AlgebraicGeometry.ConstantFieldTorBounds
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

public import Sheaf.Paper.IntegralCriterionReductions
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.AdicStratifiedPerfectData
public import Sheaf.Paper.IntegralHomReductionComparison
public import Mathlib.Algebra.Field.ZMod

/-! # Complete residue witnesses for integral general-lfp internal Hom

Source: Bhatt--Scholze, Definition 6.5.1 and Proposition 6.8.11(3),
with Lemma 6.7.13 (blueprint: lem-sfb-integral-general-lfp-hom-finiteness).

## Main declarations

* `integralGeneralLfpPrimeDatum`: fill the unused characteristic datum of the reduction API.
* `integralGeneralLfpAdicImage`: canonical ordinary coefficient-presentation transport.
* `integral_general_lfp_hom_finiteness`: completeness, canonical reduction and etale witness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The prime-field datum only fills the unused characteristic parameter of the
published integral reduction interface; it imposes no finite-field condition on k.
Source: coefficient conventions of Bhatt--Scholze, Section 6.8
(blueprint: lem-sfb-integral-general-lfp-hom-finiteness). -/
def integralGeneralLfpPrimeDatum (p : ℕ) [Fact p.Prime] :
    WeilConjectures.FiniteFieldDatum.{0} where
  p := p
  a := 1
  q := p
  prime := Fact.out
  exponent_pos := le_refl 1
  cardinality_eq := (pow_one p).symm
  k₀ := ZMod p
  card_base := by simp [Nat.card_eq_fintype_card]
  k := AlgebraicClosure (ZMod p)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Read the same internal-module derived object in the completed ring-sheaf
presentation. Both coefficient isomorphisms are fixed by all quotient projections;
this functor applies no completion to its input.
Source: Bhatt--Scholze, Definitions 6.5.1 and 6.8.10
(blueprint: lem-sfb-integral-general-lfp-hom-finiteness). -/
def integralGeneralLfpAdicImage :
    DerivedCategory (AdicCompletion.Modules l E X) ⥤
      DerivedCategory (Scheme.proEtaleRingModules X
        (Scheme.adicLisseCompletedRing X (Scheme.pbcIntegralDatum l E).ideal)) :=
  (integralSectionDerivedEquivalence l E X).functor ⋙
    Scheme.integralDetailedTransport X l E ⋙
    Scheme.pbcDerivedRestrict (Scheme.pbcCompletedComparison X
      (Scheme.pbcIntegralDatum l E)).hom

/-- General-lfp bounded constructible integral inputs have complete internal Hom,
invertible canonical evaluation-transpose reduction, and a bounded constructible
finite-Tor etale residue witness. The Hom is the ambient ordinary unbounded Hom.
The canonical reduction comparison is written in its normalized ringed-site model,
under the fixed section-action equivalence; this equivalence preserves evaluation.

Source: Bhatt--Scholze, Definition 6.5.1, Proposition 6.8.11(3), Lemma 6.7.13;
Stacks Tags 099A and 09AL
(blueprint: lem-sfb-integral-general-lfp-hom-finiteness).

Proof:
1. A field is Noetherian, so finite type makes X Noetherian and hence qcqs.
The valuation ring is a DVR with finite residue field of characteristic l.
The projection-normalized coefficient comparison identifies B with its positive
quotient limit; finite discrete coefficients identify the residue with A_X.
2. Apply integralLfpConstantModelComparison on every cohomology sheaf and then
integral_cohomological_adic_criterion to K and L. This supplies their completeness
and bounded constructible finite-Tor etale residue models, including torsion inputs.
3. moduleObject_ringedSite_derived_comparison identifies the ambient Hom, tensor,
evaluation and every slice with their ringed-site models. The locally complete
second argument L makes Hom(K,L) locally complete by
isLocallyDerivedRingedIdealComplete_derivedInternalHom, with no perfectness of K.
4. integralHomReduction at exponent one makes the transpose of reduced evaluation
invertible. The same evaluation-preserving comparison carries this to the displayed
canonical ringed-site map; no arbitrary isomorphism replaces that map.
5. Constructible site comparison puts the two residue inputs in the finite constant
local-model category. finiteField_constantModel_internalHom gives bounded
constructible cohomology of their Hom. Step 4 gives this for the reduced ambient Hom.
6. Essential surjectivity of constructibleComparison gives its etale origin D.
exists_iso_Q_obj_of_isGE_of_isLE chooses an actually bounded representative.
Constructible finite-type values over the residue field are finite-dimensional.
7. constant_field_tor_bounds gives a common Tor interval on the pro-etale side;
finiteTorComparisonNoetherian reflects it to the etale side. In residue-field
coefficients every module sheaf is flat, so sfbEtaleTensorDegreeZero computes
precisely the derived tensor with each degree-zero test module sheaf. -/
theorem integral_general_lfp_hom_finiteness
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (K L : DerivedCategory (AdicCompletion.Modules l E X))
    (hK : boundedConstructible (AdicCompletion.ring l E X) K)
    (hL : boundedConstructible (AdicCompletion.ring l E X) L) :
    Scheme.IsSfbAdicComplete X (Scheme.pbcIntegralDatum l E).ideal
      ((integralGeneralLfpAdicImage l E X).obj
        (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj (op K)).obj L)) ∧
    IsIso (WeilConjectures.integralHomReductionComparison
      (integralGeneralLfpPrimeDatum (ringChar k)) l (Ne.symm (Fact.out : ringChar k ≠ l))
      E X 0 ((integralSectionDerivedEquivalence l E X).functor.obj K)
      ((integralSectionDerivedEquivalence l E X).functor.obj L)) ∧
    ∃ D : CochainComplex
        (Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (Scheme.PbcIntegralRing l E ⧸
            (Scheme.pbcIntegralDatum l E).ideal ^ (0 + 1)))) ℤ,
      (∃ a b : ℤ, a ≤ b ∧ D.IsStrictlyGE a ∧ D.IsStrictlyLE b) ∧
      (∀ q : ℤ, Scheme.IsConstructibleSheaf (D.homology q)) ∧
      Nonempty (DerivedCategory.Q.obj
          (((comparisonUpperStar
            (ModuleCat.{u + 1} (Scheme.PbcIntegralRing l E ⧸
              (Scheme.pbcIntegralDatum l E).ideal ^ (0 + 1))) X).mapHomologicalComplex
                (.up ℤ)).obj D) ≅
        DerivedCategory.Q.obj (Scheme.sfbResidueComplex X
          (Scheme.pbcIntegralDatum l E).ideal
          ((integralGeneralLfpAdicImage l E X).obj
            (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj
              (op K)).obj L)))) ∧
      ∃ a b : ℤ, a ≤ b ∧
        ∀ (N : Sheaf X.smallEtaleTopology
            (ModuleCat.{u + 1} (Scheme.PbcIntegralRing l E ⧸
              (Scheme.pbcIntegralDatum l E).ideal ^ (0 + 1)))) (q : ℤ),
          q < a ∨ b < q → IsZero
            ((Scheme.sfbEtaleTensorDegreeZero X _ D N).homology q) := by
  sorry

end AlgebraicGeometry.ProEtale
