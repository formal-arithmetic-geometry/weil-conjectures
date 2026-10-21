/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.RoosIntrinsicCompletenessEquivalence
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Sheaf.SixFunctors.IntegralOpenReductionComparison
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.GroupTheory.Torsion
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Paper.WeilCompletedTensorReflector
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.Paper.CompletedKoszulQuotientComparison
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.ExactProductFunctorStrictLimit
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenExtensionProducts
import Sheaf.SixFunctors.OpenSemilinearTensorModel
import Sheaf.SixFunctors.OpenTensorNormalization

/-! # Actual open completion units and the complete open adjunction

Source: Stacks Project, Tags 099M, 099N (2),(5), and 09BN; Bhatt--Scholze,
Proposition 3.5.1 and Definition 3.5.2, p.24
(blueprint: lem-sf-open-roos-unit-adjunction).

The quotient completion and its unit are the published strict augmented Roos
construction. The comparison is characterized uniquely by compatibility with this
unit; the normalized exact-product construction gives precisely that comparison.
The index n denotes the positive exponent n+1. Coefficient and site universes are
independent, and all derived categories and complexes are unbounded.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.OpenRoos

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The published intrinsic Koszul-unit condition, specialized to the actual uniformizer.
Quantification over representatives avoids adding a choice to complete objects.
Source: Stacks 099B, 0A0E; the integral specialization of intrinsic completion in
RoosIntrinsicCompletenessEquivalence (blueprint: lem-sf-open-roos-unit-adjunction). -/
abbrev Intrinsic (T : Scheme.{t}) (K : IntegralOnSlice.D l E T none) : Prop :=
  ∀ (C : IntegralOnSlice.Cx l E T none) (e : DerivedCategory.Q.obj C ≅ K),
    IsIso (integralKoszulIntrinsicUnit l E T K C e)

/-- The four reflector assertions, all for the actual quotient-augmentation unit.
Source: Stacks 099M and 099B (blueprint: lem-sf-open-roos-unit-adjunction). -/
def ReflectorAssertions (T : Scheme.{t}) : Prop :=
  (∀ H : IntegralOnSlice.D l E T none,
    Intrinsic l E T ((IntegralOnSlice.completion l E T none).obj H)) ∧
  (∀ H L : IntegralOnSlice.D l E T none, Intrinsic l E T L →
    Function.Bijective (fun f : (IntegralOnSlice.completion l E T none).obj H ⟶ L ↦
      (IntegralOnSlice.completionUnit l E T none).app H ≫ f)) ∧
  (∀ H : IntegralOnSlice.D l E T none,
    IntegralOnSlice.IsComplete l E T none H ↔
      IsIso ((IntegralOnSlice.completionUnit l E T none).app H)) ∧
  (∀ H : IntegralOnSlice.D l E T none,
    IsIso ((IntegralOnSlice.completionUnit l E T none).app H) ↔ Intrinsic l E T H)

/-- The full complete category, using the recorded Roos-triangle predicate verbatim.
Source: Bhatt--Scholze Definition 3.5.2
(blueprint: lem-sf-open-roos-unit-adjunction). -/
abbrev Complete (T : Scheme.{t}) :=
  ObjectProperty.FullSubcategory (IntegralOnSlice.IsComplete l E T none)

variable {V W : Scheme.{t}} (e : V ⟶ W) [IsOpenImmersion e]
  (o : IntegralOpenReduction.Operations l E e)

/-- Literal restriction of the ordinary derived extension to complete objects.
Source: Stacks 09BN (blueprint: lem-sf-open-roos-unit-adjunction). -/
def completeExtension
    (h : ∀ M, IntegralOnSlice.IsComplete l E V none M →
      IntegralOnSlice.IsComplete l E W none ((IntegralOpenReduction.shriek l E e o).obj M)) :
    Complete l E V ⥤ Complete l E W :=
  ObjectProperty.lift _
    ((ObjectProperty.ι (IntegralOnSlice.IsComplete l E V none)) ⋙
      IntegralOpenReduction.shriek l E e o)
    (fun M ↦ h M.obj M.property)

/-- Literal restriction of ordinary derived open restriction to complete objects.
Source: Stacks 099N (2),(5) (blueprint: lem-sf-open-roos-unit-adjunction). -/
def completeRestriction
    (h : ∀ H, IntegralOnSlice.IsComplete l E W none H →
      IntegralOnSlice.IsComplete l E V none ((IntegralOpenReduction.star l E e o).obj H)) :
    Complete l E W ⥤ Complete l E V :=
  ObjectProperty.lift _
    ((ObjectProperty.ι (IntegralOnSlice.IsComplete l E W none)) ⋙
      IntegralOpenReduction.star l E e o)
    (fun H ↦ h H.obj H.property)

/-- The actual pulled quotient tower's Roos derived-limit model on good representatives.
The restriction is applied to the entire strict tower, retaining its transitions.
Source: Stacks 099N (5), 0941 (blueprint: lem-sf-open-roos-unit-adjunction). -/
def pulledRoos : (IntegralOnSlice.Good l E W none).FullSubcategory ⥤
    IntegralOnSlice.D l E V none :=
  (IntegralOnSlice.Good l E W none).ι ⋙ IntegralOnSlice.tower l E W none ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj
      ((IntegralOpenReduction.restriction l E e o).mapHomologicalComplex (.up ℤ)) ⋙
    integralOperationsRoosFunctor ⋙ DerivedCategory.Q

/-- The actual pulled augmentation: apply restriction to (gamma,0), then the map
which is the canonical product comparison in BOTH Roos coordinates.
Source: Stacks 099N (5), 0941 (blueprint: lem-sf-open-roos-unit-adjunction). -/
def pulledUnit (P : IntegralOnSlice.Cx l E W none) :=
  ((IntegralOpenReduction.restriction l E e o).mapHomologicalComplex (.up ℤ)).map
      (IntegralOnSlice.roosUnit l E W none P) ≫
    scalarRoosMap (IntegralOpenReduction.restriction l E e o)
      ((IntegralOnSlice.tower l E W none).obj P)

/-- Roos completeness, reflection by the actual unit, and the complete open adjunction.

Source: Stacks 099M, 099N (2),(5), 09BN; Bhatt--Scholze 3.5.1--3.5.2, p.24
(blueprint: lem-sf-open-roos-unit-adjunction).

Proof:
1. The extension-integers DVR theorem gives a Noetherian PID R and a nonzero
uniformizer. Finite DVR quotients are finite, hence A_1 is additive torsion.
Multiplication by t^(n+1) is injective with cokernel A_(n+1), giving the displayed
rank-one finite free resolution and every adic-datum hypothesis.
2. Finite type over the field gives Noetherian V,W, hence qcqs. Every open in a
Noetherian scheme is quasi-compact; therefore e is quasi-compact, including the empty open.
3. Weakly-etale localization identifies the open site with the slice. Constant
sections identify each finite coefficient. Quotient maps commute on constants;
immersion inverse image preserves the completed limit and every projection.
4. The ringed Koszul reflector and the unit-compatible completed Koszul/quotient
comparison identify the Koszul unit (u,0) with the actual strict quotient unit.
Strict Roos comparison preserves this augmentation. The Roos/intrinsic equivalence
then gives complete output, the stated Hom bijection and both predicate equivalences.
5. Take a flat-term K-flat representative. Exact ringed restriction preserves it.
The tensor restriction map sends each tensor to the same restricted tensor, commuting
with every quotient and with x mapped to x tensor 1. This yields one strict tower
comparison before localization, natural and independent of representatives.
6. Apply the normalized exact-product strict-limit comparison to that tower map.
Its augmentation clause proves rho composed with e*eta equals eta on e*H.
The reflector Hom bijection makes this unit-compatible natural isomorphism unique.
The pulledRoos model is the strict pulled quotient tower, and pulledUnit retains
both product coordinates. Descent supplies C,c,chi; b identifies it with completion
of restriction, and chi followed by b is exactly the actual completion unit.
Thus restriction preserves completeness and this comparison is invertible on
complete inputs.
7. Exact open extension preserves countable products since e is quasi-compact.
The simultaneous open semilinear tensor model commutes with reductions and their
augmentations. Exact-product strict limits therefore show it preserves completeness.
8. Restrict the actual exact open adjunction to the full complete subcategories.
Its unit and counit are those of the ambient adjunction, as the two formulas assert.
The slice unit is summand insertion, and collapse on the open is its inverse; hence
it is the identity under that section identification. Termwise localization gives
the representative formula below, and invertibility of the unit gives full faithfulness. -/
theorem openRoosUnitAdjunction
    (D : FiniteFieldDatum.{t}) (_hl : l ≠ D.p)
    [V.Over (Spec (CommRingCat.of D.k))] [W.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (V ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (W ↘ Spec (CommRingCat.of D.k))]
    [e.IsOver (Spec (CommRingCat.of D.k))] :
    IsNoetherian V ∧ IsNoetherian W ∧ CompactSpace V ∧ CompactSpace W ∧
    QuasiSeparatedSpace V ∧ QuasiSeparatedSpace W ∧ QuasiCompact e ∧
    IsNoetherianRing (Padic.coefficientExtensionIntegers l E) ∧
    IsAddTorsion (Padic.coefficientExtensionRing l E 1) ∧
    (∃ d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E),
      d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E}) ∧
    (∀ n : ℕ, Finite (Padic.coefficientExtensionRing l E (n + 1)) ∧
      Function.Injective (fun x : Padic.coefficientExtensionIntegers l E ↦
        Padic.coefficientExtensionUniformizer l E ^ (n + 1) * x) ∧
      Function.Exact (fun x : Padic.coefficientExtensionIntegers l E ↦
        Padic.coefficientExtensionUniformizer l E ^ (n + 1) * x)
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) ∧
      Function.Surjective
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))) ∧
    ReflectorAssertions l E W ∧ ReflectorAssertions l E V ∧
    ∃ o : IntegralOpenReduction.Operations l E e,
      (∀ n : ℕ, IsIso (o.finiteMap n)) ∧ IsIso o.completedMap ∧
      (∀ n : ℕ,
        o.finiteMap (n + 1) ≫
          ((IntegralOpenReduction.sliceSite e).sheafPushforwardContinuous
            CommRingCat.{max u (t + 1)} ((ProEt.topology W).over
              (IntegralOpenReduction.openObject e)) (ProEt.topology V)).map
                (coefficientSequenceCommRingTransition l E V n) =
        ((ProEt.topology W).overPullback CommRingCat.{max u (t + 1)}
          (IntegralOpenReduction.openObject e)).map
            (coefficientSequenceCommRingTransition l E W n) ≫ o.finiteMap n) ∧
      (∃! rho : IntegralOnSlice.completion l E W none ⋙ IntegralOpenReduction.star l E e o ≅
          IntegralOpenReduction.star l E e o ⋙ IntegralOnSlice.completion l E V none,
        ∀ H : IntegralOnSlice.D l E W none,
          (IntegralOpenReduction.star l E e o).map
              ((IntegralOnSlice.completionUnit l E W none).app H) ≫ rho.hom.app H =
            (IntegralOnSlice.completionUnit l E V none).app
              ((IntegralOpenReduction.star l E e o).obj H)) ∧
      (∃ (C : IntegralOnSlice.D l E W none ⥤ IntegralOnSlice.D l E V none)
        (c : IntegralOnSlice.qGood l E W none ⋙ C ≅ pulledRoos l E e o)
        (chi : IntegralOpenReduction.star l E e o ⟶ C)
        (b : C ≅ IntegralOpenReduction.star l E e o ⋙ IntegralOnSlice.completion l E V none),
        (∀ P : (IntegralOnSlice.Good l E W none).FullSubcategory,
          chi.app (DerivedCategory.Q.obj P.obj) ≫ c.hom.app P =
            (IntegralOpenReduction.restriction l E e o).mapDerivedCategoryFactors.hom.app P.obj ≫
              DerivedCategory.Q.map (pulledUnit l E e o P.obj)) ∧
        (∀ H : IntegralOnSlice.D l E W none,
          chi.app H ≫ b.hom.app H = (IntegralOnSlice.completionUnit l E V none).app
            ((IntegralOpenReduction.star l E e o).obj H))) ∧
      ∃ (hExtension : ∀ M, IntegralOnSlice.IsComplete l E V none M →
          IntegralOnSlice.IsComplete l E W none
            ((IntegralOpenReduction.shriek l E e o).obj M))
        (hRestriction : ∀ H, IntegralOnSlice.IsComplete l E W none H →
          IntegralOnSlice.IsComplete l E V none
            ((IntegralOpenReduction.star l E e o).obj H)),
        (∀ H : IntegralOnSlice.D l E W none, IntegralOnSlice.IsComplete l E W none H →
          IsIso ((IntegralOnSlice.completionUnit l E V none).app
            ((IntegralOpenReduction.star l E e o).obj H))) ∧
        (∀ M : IntegralOnSlice.D l E V none, IntegralOnSlice.IsComplete l E V none M →
          IsIso ((IntegralOpenReduction.openAdjunction l E e o).unit.app M)) ∧
        (∀ P : IntegralOnSlice.Cx l E V none,
          (IntegralOpenReduction.openAdjunction l E e o).unit.app (DerivedCategory.Q.obj P) =
            DerivedCategory.Q.map
              (((IntegralOpenReduction.ordinaryAdjunction l E e o).mapHomologicalComplex
                (.up ℤ)).unit.app P) ≫
            (IntegralOpenReduction.restriction l E e o).mapDerivedCategoryFactors.inv.app _ ≫
            (IntegralOpenReduction.star l E e o).map
              ((IntegralOpenReduction.extension l E e o).mapDerivedCategoryFactors.inv.app P)) ∧
        Nonempty ((completeExtension l E e o hExtension).FullyFaithful) ∧
        ∃ a : completeExtension l E e o hExtension ⊣ completeRestriction l E e o hRestriction,
          (∀ M : Complete l E V,
            (a.unit.app M).hom = (IntegralOpenReduction.openAdjunction l E e o).unit.app M.obj) ∧
          (∀ H : Complete l E W,
            (a.counit.app H).hom =
              (IntegralOpenReduction.openAdjunction l E e o).counit.app H.obj) := by
  sorry

end WeilConjectures.OpenRoos
