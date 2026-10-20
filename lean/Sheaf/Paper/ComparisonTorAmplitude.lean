/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.FiniteCoefficientFlatModel
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedTensor
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.AlgebraicGeometry.ComparisonTorInterval
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.IntrinsicComparisonConstructibility
import Sheaf.Paper.IntrinsicComparisonTorAmplitude
import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-!
# Comparison of étale and pro-étale Tor amplitude

Source: Weil conjectures blueprint, `lem-sf-comparison-tor-amplitude.md`
(blueprint: lem-sf-comparison-tor-amplitude).

## Main statements

- `finiteCoefficient_comparison_preserves_torAmplitude`: clause (i).
- `finiteCoefficient_comparison_reflects_torAmplitude`: clause (ii).

The étale coefficients are the canonical universe lift of the same quotient ring.
The pullback is the existing intrinsic comparison, obtained by constant-scalar
associated-module-sheaf realization after the specified site inverse image.
The interval is ordered, as in the cited flat-model and pro-étale Tor predicates.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- Clause (i): comparison preserves the specified Tor interval and bounded constructibility.
Source: blueprint `sec-six-functors/sk-prop-sf-rf-shriek-preservation/`
`lem-sf-comparison-tor-amplitude.md`, (i) (blueprint: lem-sf-comparison-tor-amplitude).

Proof: first identify the comparison inverse image of the constant coefficient ring with
its pro-étale constant ring, using the lifted ring-object adjunction and the universal
property of the constant sheaf. The canonical intrinsic realization implements this
identification. Exact comparison is applied termwise and commutes with cohomology
(lem-weil-pbc-exact-functor-derived-factorization and its cohomology companion).
Apply the étale clause of lem-sf-flat-model to obtain a flat model supported in [a,b].
By lem-exc-constant-inverse-image-flat its pullback remains flat and has the same support.
It is K-flat by lem-pc-bounded-above-flat-kflat-site, so tensoring with any degree-zero
module computes derived tensor and has no cohomology outside [a,b]. Finally clause (ii)
of lem-sf-proetale-constructible-origin gives bounded constructibility. -/
theorem finiteCoefficient_comparison_preserves_torAmplitude
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hlp : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (T : Scheme.{u}) [∀ x : T, Invertible (l : T.residueField x)]
    (a b : ℤ) (_hab : a ≤ b)
    (K' : Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) T)
    (_hK' : @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) inferInstance
      ((Equiv.ulift : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n) ≃
        Padic.coefficientExtensionRing l E n).finite_iff.mpr
          (Padic.finite_coefficientExtensionRing l E n hn)) T K')
    (_hTor' : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) T a b K') :
    Scheme.intrinsicFiniteTorsionConstructible l E n hn T
        ((@ProEtale.finiteCoefficientIntrinsicDerivedComparison.{u} T
          (Padic.coefficientExtensionRing l E n) inferInstance
          (Padic.finite_coefficientExtensionRing l E n hn)).obj K') ∧
      Scheme.HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E n)
        ((@ProEtale.finiteCoefficientIntrinsicDerivedComparison.{u} T
          (Padic.coefficientExtensionRing l E n) inferInstance
          (Padic.finite_coefficientExtensionRing l E n hn)).obj K') a b := by
  exact ⟨intrinsicComparison_boundedConstructible D l _hlp E n hn T K' _hK',
    intrinsicComparison_torAmplitude D l _hlp E n hn T a b _hab K' _hK' _hTor'⟩

/-- Clause (ii): comparison reflects the Tor interval of a bounded-below étale origin.
Source: blueprint `sec-six-functors/sk-prop-sf-rf-shriek-preservation/`
`lem-sf-comparison-tor-amplitude.md`, (ii) (blueprint: lem-sf-comparison-tor-amplitude).

Proof: A = A_{E,n} is finite for n ≥ 1. Regard K' as an object of D⁺ by the
bounded-below hypothesis; the ordered interval a ≤ b is part of HasProEtaleTorAmplitude. Apply
the reverse implication of lem-exc-comparison-tor-interval
(ProEtale.comparison_torAmplitudeIn_iff). Its pro-étale side is the intrinsic realization
after the bounded-below site pullback, canonically isomorphic to the derived functor of
the composite (mapDerivedCategoryCompIso). Compose with the given K ≅ ν*K'; any
representative isomorphism Q(L) ≅ ν*K' composed with its inverse gives Q(L) ≅ K, so the
assumed K-flat tensor test on K yields the same vanishing. This is the premise of the
reverse implication, hence the étale Tor bound. -/
theorem finiteCoefficient_comparison_reflects_torAmplitude
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hlp : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (T : Scheme.{u}) [∀ x : T, Invertible (l : T.residueField x)]
    (a b : ℤ)
    (K' : Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) T)
    (_hPlus : _root_.DerivedCategory.TStructure.t.plus K')
    (K : Scheme.proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E n))
    (_hK : Scheme.intrinsicFiniteTorsionConstructible l E n hn T K)
    (_hTor : Scheme.HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E n) K a b)
    (_e : K ≅ (@ProEtale.finiteCoefficientIntrinsicDerivedComparison.{u} T
          (Padic.coefficientExtensionRing l E n) inferInstance
          (Padic.finite_coefficientExtensionRing l E n hn)).obj K') :
    Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) T a b K' := by
  let A := Padic.coefficientExtensionRing l E n
  have : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T
  let G := ProEtale.finiteCoefficientIntrinsicRealization T A
  let Kplus : _root_.DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
    ⟨K', _hPlus⟩
  apply (ProEtale.comparison_torAmplitudeIn_iff A T a b _hTor.1 Kplus).mpr
  have ecomp := (Functor.mapDerivedCategoryCompIso F G).app K'
  have e : K ≅ G.mapDerivedCategory.obj (F.mapDerivedCategory.obj K') :=
    _e ≪≫ ecomp
  refine ⟨_hTor.1, ?_⟩
  intro L P hL f hf hP M i hi
  exact _hTor.2 L P (hL.map (fun eL ↦ eL ≪≫ e.symm)) f hf hP M i hi

end AlgebraicGeometry
