/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.ComparisonTorInterval
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit

/-!
# Exceptional adjunction transport from etale to pro-etale sheaves

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-sf-rf-shriek-preservation, final restriction paragraph; the explicit transport
argument of the DAG (blueprint: lem-sf-etale-proetale-exceptional-transport).

The domain below uses intrinsic constructible cohomology, rather than assuming etale
origin. All Tor predicates test every module sheaf on the respective site.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The etale objects occurring in the transport statement: the intersection of the
recorded bounded constructibility and finite Tor predicates. Source: blueprint
main-20261015, sk-prop-sf-rf-shriek-preservation, final restriction paragraph
(blueprint: lem-sf-etale-proetale-exceptional-transport). -/
def exceptionalTransportEtaleObjects (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) : ObjectProperty (Etale.DerivedCategoryModule A T) :=
  Etale.DerivedCategory.isBoundedConstructible A T ⊓
    fun K ↦ ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A T a b K

/-- The intrinsic pro-etale domain of transport: bounded cohomology, every cohomology
sheaf constructible on a global finite partition, and finite Tor amplitude against all
pro-etale module sheaves. Source: blueprint main-20261015,
sk-prop-sf-rf-shriek-preservation, final restriction paragraph
(blueprint: lem-sf-etale-proetale-exceptional-transport). -/
def exceptionalTransportProEtaleObjects (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) : ObjectProperty
      (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :=
  fun K ↦ _root_.DerivedCategory.TStructure.t.bounded K ∧
    (∀ i : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf T A
      ((_root_.DerivedCategory.homologyFunctor _ i).obj K)) ∧
    ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) T a b K

/-- The functor `K ↦ ν_X^* R(E(K))`, for a functorial etale origin `E` and the ordinary
etale right adjoint `R`. This is a composite of the specified functors, with no choice of
an ambient pro-etale adjoint. Source: blueprint main-20261015,
sk-prop-sf-rf-shriek-preservation, final restriction paragraph
(blueprint: lem-sf-etale-proetale-exceptional-transport). -/
def exceptionalTransportImage (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (R : Etale.DerivedCategoryModule A Y ⥤
      Etale.DerivedCategoryModule A X)
    (E : (exceptionalTransportProEtaleObjects A Y).FullSubcategory ⥤
      Etale.DerivedCategoryModule A Y) :=
  E ⋙ R ⋙ (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory

/-- Exceptional adjunction transport for one fixed compactification, including functorial
etale origins and the transported ordinary counit. Naturality in `K` is expressed by the
functor `E`, its natural origin isomorphism, and the natural transformation `t`.
Bijectivity of `h ↦ G(h) ≫ t_K` expresses the Hom equivalence and its naturality in `M`.
Source: blueprint main-20261015, sk-prop-sf-rf-shriek-preservation, final restriction
paragraph; the six-step DAG transport argument
(blueprint: lem-sf-etale-proetale-exceptional-transport).

Proof:
1. Finite coefficients and finite-type schemes over a field are Noetherian. Apply
`sk-thm-pe-constructible-comparison` to obtain bounded constructible etale origins.
`lem-exc-comparison-tor-interval` reflects the given finite Tor interval to each origin.
2. The assumed preservation by `R` makes its value bounded constructible of finite Tor
amplitude. Exact comparison commutes with cohomology, and inverse image on each finite
constructible stratum preserves local trivializations with finite values. The forward
Tor-interval comparison tests all pro-etale module sheaves. A quasi-inverse to comparison
on constructible complexes supplies the functor `E`.
3. Compose the exact open-extension comparison
`lem-cbc-proetale-extension-zero-comparison` with the proper direct-image comparison
`sk-thm-pe-direct-image-comparison`. Bounded below injective resolutions identify these
with the unbounded compact-support composites restricted to D-plus, giving beta.
4. For bounded below `M`, comparison full faithfulness identifies Hom(GPM,K) with
Hom(FM,E(K)); the ordinary etale adjunction identifies this with Hom(M,R(E(K))).
Comparison full faithfulness on X identifies the latter with Hom(PM,PR(E(K))).
5. Full faithfulness lifts every map of origins uniquely. Identity and composition
therefore lift to identity and composition; two choices of origins give canonically
isomorphic functors. The Hom bijections respect these maps and isomorphisms.
6. Define t_K as beta inverse at R(E(K)), then comparison of the ordinary counit,
then the origin isomorphism. Counit naturality makes t natural. Lift h uniquely as P(u);
naturality of beta rewrites the Hom bijection as G(h) followed by t_K.
-/
theorem etale_proEtale_exceptional_transport
    (k : Type u) [Field k] (p l : ℕ) [CharP k p]
    (_hp : p.Prime) (_hl : l.Prime) (_hlp : l ≠ p)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (_hA : ∃ n : ℕ, (l ^ n : A) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]
    [IsSeparated (f ≫ s)] [LocallyOfFiniteType (f ≫ s)] [QuasiCompact (f ≫ s)]
    (c : Compactification f) [IsSeparated (c.g ≫ s)]
    [LocallyOfFiniteType (c.g ≫ s)] [QuasiCompact (c.g ≫ s)]
    (R : Etale.DerivedCategoryModule A Y ⥤ Etale.DerivedCategoryModule A X)
    (adj : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ R)
    (_hR : ∀ K, exceptionalTransportEtaleObjects A Y K →
      exceptionalTransportEtaleObjects A X (R.obj K)) :
    ∃ β : _root_.DerivedCategory.Plus.ι ⋙
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ≅
      _root_.DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c,
    ∃ E : (exceptionalTransportProEtaleObjects A Y).FullSubcategory ⥤
        Etale.DerivedCategoryModule A Y,
    ∃ α : E ⋙ (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ≅
        (exceptionalTransportProEtaleObjects A Y).ι,
      (∀ K, exceptionalTransportEtaleObjects A Y (E.obj K)) ∧
      (∀ K, exceptionalTransportProEtaleObjects A X
        ((exceptionalTransportImage A R E).obj K)) ∧
      ∃ t : exceptionalTransportImage A R E ⋙
          rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⟶
          (exceptionalTransportProEtaleObjects A Y).ι,
        (∀ K, ∃ hRE : _root_.DerivedCategory.TStructure.t.plus (R.obj (E.obj K)),
          t.app K = β.inv.app ⟨R.obj (E.obj K), hRE⟩ ≫
            (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
              (adj.counit.app (E.obj K)) ≫ α.hom.app K) ∧
        ∀ (K : (exceptionalTransportProEtaleObjects A Y).FullSubcategory)
          (M : _root_.DerivedCategory.Plus
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
          Function.Bijective
            (fun h : (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M.obj ⟶
                (exceptionalTransportImage A R E).obj K ↦
              (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map h ≫
                t.app K) := by
  sorry

end AlgebraicGeometry.ProEtale
