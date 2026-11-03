/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison

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

private theorem exceptionalTransport_object_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T] :
    exceptionalTransportProEtaleObjects A T =
      (exceptionalTransportEtaleObjects A T).map
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory := by
  let N := (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  have hc := exceptionalTransport_constructible_comparison A T
  funext K
  apply propext
  constructor
  · rintro ⟨hbd, hcs, a, b, hab, ht⟩
    have hbc : (Etale.DerivedCategory.isBoundedConstructible A T).map N K :=
      (congrFun hc K).mp ⟨hbd, hcs⟩
    obtain ⟨H, hH, ⟨e⟩⟩ := hbc
    have ht' : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) T a b (N.obj H) :=
      (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e.symm ht
    refine ⟨H, ⟨hH, a, b, hab, ?_⟩, ⟨e⟩⟩
    exact Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
      ((DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b H).mp ht')
  · rintro ⟨H, ⟨hH, a, b, hab, ht⟩, ⟨e⟩⟩
    have hbc : (Etale.DerivedCategory.isBoundedConstructible A T).map N K :=
      ⟨H, hH, ⟨e⟩⟩
    obtain ⟨hbd, hcs⟩ := (congrFun hc K).mpr hbc
    refine ⟨hbd, hcs, a, b, hab, ?_⟩
    exact (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e
      ((DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b H).mpr
        (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp ht))

end AlgebraicGeometry.ProEtale
