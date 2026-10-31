/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CompactSupportCondensedRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.Compactification.RefinementCategory

/-! # Data for filtered descent of condensed representing pairs

Source: blueprint sec-smooth-purity, sk-thm-sp-qbar proof, filtered Hom-colimit display
and its model-independence paragraph; sk-prop-sp-unique-adjoint-categorical proof,
Transposes, Naturality, Inverse and Uniqueness.
(blueprint: def-pur-filtered-condensed-representing-pair-data).

All categories, scalar functors, and compact-support functors below are the recorded
condensed module-object constructions. The small helper records only package the data
and conclusions of this one statement. No integral model or exceptional tower is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.FilteredCondensedRepresentingPair
variable (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y} (c : Compactification f.left)

/-- The existing finite-coefficient proper/open composite, restricted to bounded constructibles.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
abbrev finiteSupport (E : PadicAlgCl.FiniteIntermediateField l) :=
  CondensedRing.ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification l E c

/-- The same existing proper/open composite for the finite-subfield-valued closure ring.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
abbrev omegaSupport :=
  CondensedRing.boundedConstructibleLowerShriekOfCompactification l c

open CompactSupportCondensedRealization

/-- The existing inclusion comparison for the finite-coefficient support functor.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
abbrev finiteCompatibility (E : PadicAlgCl.FiniteIntermediateField l) :=
  CondensedRing.ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactificationCompatibility
    l E c

/-- The existing inclusion comparison for the closure-coefficient support functor.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
abbrev omegaCompatibility :=
  CondensedRing.boundedConstructibleLowerShriekOfCompactificationCompatibility l c

/-- The finite and closure scalar comparisons for the fixed compactification.
Their canonical normalization is imposed by `ScalarComparisons.IsCanonical`; no arbitrary
comparison is allowed by the main theorem.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
structure ScalarComparisons where
  finite : ∀ {E H : PadicAlgCl.FiniteIntermediateField l} (h : E ≤ H),
    finiteSupport l k c E ⋙ constructibleExtendScalars Y.left l h ≅
      constructibleExtendScalars X.left l h ⋙ finiteSupport l k c H
  omega : ∀ E : PadicAlgCl.FiniteIntermediateField l,
    finiteSupport l k c E ⋙ constructibleToPadicAlgCl Y.left l E ≅
      constructibleToPadicAlgCl X.left l E ⋙ omegaSupport l k c

/-- A supplied finite representing pair and all its finite-overfield Hom bijections.
The counit at the base field is `t`; `Pair.IsCompatible` expresses naturality and
scalar compatibility by the counit formula, including identity scalar extension.
Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit and model-independence paragraphs;
sk-prop-sp-unique-adjoint-categorical, Transposes and Naturality.
(blueprint: def-pur-filtered-condensed-representing-pair-data). -/
structure Pair (s : ScalarComparisons l k c) (E : PadicAlgCl.FiniteIntermediateField l) where
  M : PadicSubfieldConstructible X.left l E
  L : PadicSubfieldConstructible Y.left l E
  t : (finiteSupport l k c E).obj M ⟶ L
  beta : ∀ (H : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ H)
    (C : PadicSubfieldConstructible X.left l H),
    (C ⟶ (constructibleExtendScalars X.left l h).obj M) ≃
      ((finiteSupport l k c H).obj C ⟶
        (constructibleExtendScalars Y.left l h).obj L)

end WeilConjectures.FilteredCondensedRepresentingPair
