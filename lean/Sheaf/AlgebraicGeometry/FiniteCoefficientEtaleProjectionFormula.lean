/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula
/-!
# The finite-coefficient projection formula on the small étale site

Source: Weil blueprint, `sec-smooth-purity/sk-thm-sf-pf-finite/thm-sf-pf-finite.md`,
order 1879 (blueprint: thm-sf-pf-finite).

The projection transformation is the existing natural transformation of bifunctors
`Etale.projectionMapOfCompactification`. Its components use the ordinary étale tensor,
exact pullback,
and the compact-support functor of the chosen compactification. The conclusion includes
membership of both endpoints in the full bounded-below subcategory, so invertibility
in the ambient derived category is precisely invertibility in `D⁺`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The existing Nagata compactification, specialized to a separated quasi-compact target
of finite type over the fixed field. Compactness and quasi-separatedness of the target
are obtained from its structure morphism, rather than assumed separately.
Source: Weil blueprint, `sk-thm-sf-pf-finite/thm-sf-pf-finite.md`, compactification
in proof Step 1 (blueprint: thm-sf-pf-finite). -/
noncomputable def finiteCoefficientProjectionCompactification
    (D : WeilConjectures.FiniteFieldDatum.{u}) {X Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of D.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Compactification f :=
  letI : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of D.k))
  letI : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (CommRingCat.of D.k))
  HasCompactification.compactification f

/-- The canonical compact-support projection transformation is invertible at the stated
finite coefficients and bounded constructible inputs, with finite Tor amplitude for `L`.
Naturality in both inputs is part of `projectionMapOfCompactification`, a natural transformation of
bifunctors. Constructibility uses the underlying set sheaf and the exact predicate of
`def-weil-pbc-etale-sheaves`, including constructible locally closed strata.

Source: Weil blueprint, `sec-smooth-purity/sk-thm-sf-pf-finite/thm-sf-pf-finite.md`,
order 1879 (blueprint: thm-sf-pf-finite).

Proof plan: Apply the étale assertion of `lem-weil-finite-compact-projection-formula`
with `A = Padic.coefficientExtensionRing l E n` and precisely these `f`, `K`, `L`.
The fixed finite-field datum, separated finite-type schemes and morphism, bounded
constructible cohomology, and tensor-vanishing definition of finite Tor amplitude
are exactly its hypotheses. The projection transformation in that assertion is
`projectionMapOfCompactification`, formed by proper pushforward projection followed by the inverse
open-extension tensor comparison. Its assertion gives invertibility and naturality.
Boundedness below follows from the bounded input complexes, the finite Tor interval,
exactness of extension by zero and left exactness of the proper direct image.
Only the étale assertion is used; no pro-étale realization is required. -/
theorem isIso_projectionMap_coefficientExtensionRing
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n)
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X)
    (L : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) Y)
    (_hKc : ∀ i : ℤ, Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)))).obj
        ((_root_.DerivedCategory.homologyFunctor _ i).obj K)))
    (_hKb : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj K))
    (_hLc : ∀ i : ℤ, Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)))).obj
        ((_root_.DerivedCategory.homologyFunctor _ i).obj L)))
    (_hLb : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj L))
    (_hLt : ∃ a b : ℤ, a ≤ b ∧
      DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) Y a b L) :
    _root_.DerivedCategory.TStructure.t.plus
      (((derivedTensorRightDerivedLowerShriek
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
        (finiteCoefficientProjectionCompactification D f)).obj K).obj L) ∧
    _root_.DerivedCategory.TStructure.t.plus
      (((rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
        (finiteCoefficientProjectionCompactification D f)).obj K).obj L) ∧
    IsIso (((projectionMapOfCompactification
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
      (finiteCoefficientProjectionCompactification D f)).app K).app L) := by
  sorry

end AlgebraicGeometry.Etale
