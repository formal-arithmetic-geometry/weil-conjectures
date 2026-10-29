/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Field.ULift
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import WeilConjectures.Algebra.Homology.RhomGlobalSections
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
public import WeilConjectures.Algebra.Homology.RingedTensorComplexConstraints
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.AlgebraicGeometry.IntegralDerivedReduction
public import WeilConjectures.AlgebraicGeometry.IntegralReductionTowerUnrestricted
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.RingTheory.WContractibleGeometricCriterion

/-! # The coefficient ringed sequence site and canonical functors

Source: Stacks Project, Tags 0941, 06YY, 079P and 07A6
(auxiliary; not a blueprint node).

## Main definitions

- `coefficientSequenceTopology`: the product sequence site with vertical covers.
- `coefficientSequenceCommRingSheaf`: the actual quotient coefficient ring sheaf.
- `coefficientSequenceModules`: module sheaves on this ringed site.
- `coefficientSequenceEvaluation`: exact restriction to the nth vertical slice.
- `coefficientSequenceLimit`: total derived limit after exact scalar restriction.
- `coefficientSequenceProjection`: its canonical, resolution-normalized projections.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Use coefficient-universe sheafification: the generic instance requires a successor.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u c v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

/-- The vertical covering condition for a sequence site.
Source: Stacks 0941, sequence-site construction
(auxiliary; not a blueprint node). -/
def coefficientSequenceCovering {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (X : ℕ × C) (S : Sieve X) : Prop :=
  S.functorPullback (Prod.sectR X.1 C) ∈ J X.2

/-- The vertical covering condition satisfies the topology axioms.
Source: Stacks 0941 (auxiliary; not a blueprint node).
Proof: the slice of the maximal sieve is maximal. For pullback along (h,f), the
vertical slice contains the pullback along f of the old vertical slice, so covering
stability and upward closure apply. For local character, test the supplied condition
on every vertical arrow in the covering slice and apply local character in J. -/
theorem coefficientSequenceTopologyAxioms {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) :
    (∀ X : ℕ × C, coefficientSequenceCovering J X ⊤) ∧
    (∀ {X Y : ℕ × C} {S : Sieve X} (f : Y ⟶ X),
      coefficientSequenceCovering J X S → coefficientSequenceCovering J Y (S.pullback f)) ∧
    (∀ {X : ℕ × C} {S : Sieve X}, coefficientSequenceCovering J X S →
      ∀ R : Sieve X,
        (∀ {Y : ℕ × C} {f : Y ⟶ X}, S f →
          coefficientSequenceCovering J Y (R.pullback f)) →
        coefficientSequenceCovering J X R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X
    change (⊤ : Sieve X.2) ∈ J X.2
    exact J.top_mem X.2
  · intro X Y S f hS
    apply J.superset_covering _ (J.pullback_stable f.2 hS)
    intro Z g hg
    change S ((Prod.sectR Y.1 C).map g ≫ f)
    have hs := S.downward_closed hg (Prod.mkHom f.1 (𝟙 Z))
    have he : (Prod.sectR Y.1 C).map g ≫ f =
        Prod.mkHom f.1 (𝟙 Z) ≫ (Prod.sectR X.1 C).map (g ≫ f.2) := by
      ext <;> simp
    exact he.symm ▸ hs
  · intro X S hS R hR
    apply J.transitive hS
    intro Y f hf
    have hr := hR (f := (Prod.sectR X.1 C).map f) hf
    change (R.functorPullback (Prod.sectR X.1 C)).pullback f ∈ J Y
    change (R.pullback ((Prod.sectR X.1 C).map f)).functorPullback
      (Prod.sectR X.1 C) ∈ J Y at hr
    rwa [Sieve.functorPullback_pullback] at hr

/-- The actual sequence topology, with covering determined by the vertical slice.
Source: Stacks 0941 (auxiliary; not a blueprint node). -/
def coefficientSequenceTopology {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) : GrothendieckTopology (ℕ × C) where
  sieves X := {S | coefficientSequenceCovering J X S}
  top_mem' := (coefficientSequenceTopologyAxioms J).1
  pullback_stable' := fun {_ _ _} f h ↦ (coefficientSequenceTopologyAxioms J).2.1 f h
  transitive' := fun {_ _} h R hh ↦
    (coefficientSequenceTopologyAxioms J).2.2 h R (fun {_ _} hf ↦ hh hf)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

end WeilConjectures
