/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
import Sheaf.Paper.ProEtaleLisseFiniteModelsFromLisse
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Unbounded reflection of bounded constructibility and Tor intervals

Source: Stacks Project, proetale.tex, Tags 099T and 09AK; blueprint main-20261015,
`det-pe-finite-tor-comparison-noetherian`
(blueprint: lem-sp-unbounded-finite-tor-comparison-reflection).

The comparison is the exact termwise inverse image on ordinary unbounded derived
categories. Both sites use the fixed-coefficient module-sheaf presentation of modules
over the constant ring. No boundedness of the etale input is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Exact comparison reflects the specified cohomological and Tor intervals and intrinsic
constructibility, even for an arbitrary unbounded etale input.

Source: Stacks Project, Tags 099T and 09AK; blueprint main-20261015,
`det-pe-finite-tor-comparison-noetherian`
(blueprint: lem-sp-unbounded-finite-tor-comparison-reflection).

Proof:
1. The existing comparison functor is exact and fully faithful on module sheaves.
   Its mapDerivedCategoryHomologyFunctorIso identifies inverse image of H^q(C)
   with H^q of its unbounded derived inverse image. Full faithfulness reflects
   zero objects, giving the same cohomology interval [c,d] on the etale side.
2. On each stratum of the intrinsic constructibility partition, use
   finite_models_of_fixed_lisse to replace local constancy and finite geometric
   stalks by finite constant models. Thus each image cohomology sheaf satisfies
   the source library's pro-etale constructibility predicate.
3. The source fixed-module constructible-origin theorem supplies a constructible
   etale sheaf G with inverse image isomorphic to the image cohomology sheaf.
   Compose with the cohomology comparison and lift the resulting isomorphism by
   full faithfulness. Transport constructibility to H^q(C), then apply the proved
   equivalence with the finite-constant-value etale constructibility predicate.
4. The source theorem torAmplitudeIn_mapDerivedCategory_iff reflects the given Tor
   interval for arbitrary unbounded complexes. Convert its t-structure formulation
   to hasTorAmplitudeIn using hasTorAmplitudeIn_iff_torAmplitudeIn. This avoids the
   coefficient-model Noetherian comparison theorem and preserves exactly [a,b].
5. Package the constructible cohomology and the interval [c,d] into bounded
   constructibility. DerivedCategory.isGE_iff gives the lower bound c and hence
   membership in the bounded-below subcategory. -/
theorem unbounded_finiteTor_comparison_reflection
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (R : Type (u + 1)) [CommRing R] [Finite R]
    [TopologicalSpace R] [DiscreteTopology R]
    (C : Etale.DerivedCategoryModule R T)
    (c d a b : ℤ) (_hcd : c ≤ d) (_hab : a ≤ b)
    (_hVanishing : ∀ q : ℤ, q < c ∨ d < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R)) q).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory.obj C)))
    (_hConstructible : ∀ q : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf T R
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R)) q).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory.obj C)))
    (_hTor : ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} R) T a b
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory.obj C)) :
    (∀ q : ℤ, q < c ∨ d < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) q).obj C)) ∧
    (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) q).obj C)) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn R T a b C ∧
    Etale.DerivedCategory.isBoundedConstructible R T C ∧
    _root_.DerivedCategory.TStructure.t.plus C := by
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) T
  have hVanishing : ∀ q : ℤ, q < c ∨ d < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) q).obj C) := by
    intro q hq
    exact IsZero.of_full_of_faithful_of_isZero F _
      ((_hVanishing q hq).of_iso ((F.mapDerivedCategoryHomologyFunctorIso q).app C))
  have hConstructible : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) q).obj C) := by
    intro q
    have hc : ProEtale.IsConstructible R
        ((_root_.DerivedCategory.homologyFunctor
          (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R)) q).obj
            (F.mapDerivedCategory.obj C)) := by
      obtain ⟨S, _, _, hS⟩ := _hConstructible q
      exact ⟨S, fun i ↦ Scheme.finite_models_of_fixed_lisse (S.domain i) R _ (hS i)⟩
    obtain ⟨G, hG, ⟨e⟩⟩ :=
      ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj R hc
    let e' := F.preimageIso (e ≪≫ ((F.mapDerivedCategoryHomologyFunctorIso q).app C).symm)
    apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
    have : Scheme.IsConstructibleSheaf G := hG
    exact Scheme.IsConstructibleSheaf.of_iso e'
  have hTor : Etale.DerivedCategory.hasTorAmplitudeIn R T a b C := by
    apply Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
    exact (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b C).mp _hTor
  exact ⟨hVanishing, hConstructible, hTor,
    ⟨hConstructible, c, d, _hcd, hVanishing⟩,
    ⟨c, (_root_.DerivedCategory.isGE_iff C c).mpr
      (fun q hq ↦ hVanishing q (Or.inl hq))⟩⟩

end AlgebraicGeometry
