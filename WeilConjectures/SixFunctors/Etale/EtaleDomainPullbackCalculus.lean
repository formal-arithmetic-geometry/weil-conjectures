/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-! # Generic coefficient-domain pullback calculus

The generic statement shares coefficient-category instances before finite specialization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures
attribute [local instance 2000] CommRing.toRing
attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
  Etale.upperStar ProEtale.pbcFixedScalarExtension Etale.scalarExtensionRepresentative
  Etale.scalarSheafPullbackComplexIso Etale.scalarGeometricRepresentative

private theorem finiteHomDomain_boundedConstructible_iff
    (R : Type (u + 1)) [CommRing R] [Finite R] (W : Scheme.{u})
    (M : Etale.DerivedCategoryModule R W) :
    Etale.DerivedCategory.isBoundedConstructible R W M ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} R) W M := by
  constructor
  · rintro ⟨hc, a, b, -, hz⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc i)⟩
    · exact (_root_.DerivedCategory.isGE_iff M a).mpr fun i hi ↦ hz i (.inl hi)
    · exact (_root_.DerivedCategory.isLE_iff M b).mpr fun i hi ↦ hz i (.inr hi)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr (hc i),
      min a b, b, min_le_right _ _, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff M a).mp ha i
        (hi.trans_le (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff M b).mp hb i hi

/-- Exact geometric pullback preserves the original finite-Tor constructible domain,
and its specified scalar comparison satisfies the K-flat representative equation.
Source: Stacks 04JC, 05VD, 095G, 07A4 and 0G7E; the finite-Hom opening domain paragraph.
(blueprint: lem-coef-etale-domain-pullback-calculus).

Proof: convert bounded constructibility to the cohomological form, apply exact etale
pullback stability, and convert back. Apply the existing Tor-interval pullback theorem
without changing either endpoint. The normalized scalar/pullback isomorphism is chosen
from its existence-and-uniqueness theorem, whose choose_spec is exactly the displayed
representative equation. All three facts hold before finite quotient specialization. -/
theorem scalarDomain_pullback
    (R S : Type (u + 1)) [CommRing R] [CommRing S] [Finite R]
    (φ : R →+* S) (X Y : Scheme.{u}) (f : Y ⟶ X) :
    exactFunctor _ _ (Etale.upperStar (ModuleCat.{u + 1} R) f) ∧
    (∀ (a b : ℤ), a ≤ b → ∀ T : Etale.DerivedCategoryModule R X,
      Etale.DerivedCategory.isBoundedConstructible R X T →
      Etale.DerivedCategory.hasTorAmplitudeIn R X a b T →
      Etale.DerivedCategory.isBoundedConstructible R Y
        ((Etale.upperStar (ModuleCat.{u + 1} R) f).leftDerivedFunctor.obj
          T) ∧
      Etale.DerivedCategory.hasTorAmplitudeIn R Y a b
        ((Etale.upperStar (ModuleCat.{u + 1} R) f).leftDerivedFunctor.obj
          T)) ∧
    (∀ P : CochainComplex
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ,
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      (Etale.scalarPullbackIso φ f).hom.app
          (_root_.DerivedCategory.Q.obj P) ≫
        (Etale.scalarExtension φ Y).map
          (Etale.scalarGeometricRepresentative R f P) ≫
        Etale.scalarExtensionRepresentative φ Y
          (((Etale.upperStar (ModuleCat.{u + 1} R)
            f).mapHomologicalComplex
            (.up ℤ)).obj P) =
      (Etale.upperStar (ModuleCat.{u + 1} S) f).leftDerivedFunctor.map
        (Etale.scalarExtensionRepresentative
            φ X P) ≫
        Etale.scalarGeometricRepresentative S f
          (((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        _root_.DerivedCategory.Q.map
          ((Etale.scalarSheafPullbackComplexIso φ f).hom.app P)) := by
  refine ⟨(exactFunctor_iff _).mpr ⟨inferInstance, inferInstance⟩, ?_, ?_⟩
  · intro a b _ T hT ht
    refine ⟨(finiteHomDomain_boundedConstructible_iff _ Y _).mpr
      (Etale.boundedConstructible_leftDerivedUpperStar _ f
        ((finiteHomDomain_boundedConstructible_iff _ X _).mp hT)), ?_⟩
    exact Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
      (Etale.torAmplitudeIn_leftDerivedUpperStar _ f a b
        (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp ht))
  · exact (Etale.scalarPullbackIso_existsUnique φ f).choose_spec.1

end WeilConjectures
