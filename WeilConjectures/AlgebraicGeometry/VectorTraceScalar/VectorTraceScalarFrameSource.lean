/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarData
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackUnitCoherence
import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarFrameSourceRaw
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartUnitNormalization
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteSingleUnitPullback

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open WeilConjectures.PurityFiniteSetting
namespace AlgebraicGeometry.Etale.VectorTraceScalar

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]

/-- The glued integration map restricts to the prescribed frame trace, after scalar
extension and the coefficient unit comparison.
Source: blueprint/latest, sec-smooth-purity/sk-prop-an, paragraph 2.
(blueprint: new-lem-pur-vector-scalar-frame-source).
-/
theorem frame_scalar_source (N : ℕ) (hN : 0 < N) (φ : A →+* B)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (r : ℕ) (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank r]
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S r F V)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT) :
    (scalarPullbackIso φ V.ι).hom.app (vectorIntegrationSource A N hA S r F) ≫
        (scalarExtension φ V.toScheme).map
          (vectorIntegrationLocalTrace N hN A hA t D S hS r F V e) ≫
        (unit φ V.toScheme) ≫ (ordinaryFiniteUnitPullback B V.ι).inv =
      (ordinaryFinitePullback B V.ι).map
        ((scalarExtension φ S).map (vectorBundleIntegration N hN A hA S hS r F) ≫
          unit φ S) := by
  apply (cancel_mono (ordinaryFiniteUnitPullback B V.ι).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let hp := (existsUnique_vectorIntegrationGluing N hN A hA S hS r F).2
  rw [frame_scalar_source_raw N hN φ hA hB S hS r F V e t D]
  simp only [vectorBundleIntegration, vectorIntegrationGluing]
  simp only [ordinaryFinitePullback]
  rw [Functor.map_comp]
  have hn := (scalarPullbackIso φ V.ι).hom.naturality
    ((Classical.choose hp.exists).1.hom ≫
      (DerivedCategory.singleFunctor _ 0).map (Classical.choose hp.exists).2)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc]
  rw [← reassoc_of% hn]
  rw [ordinaryChartUnitMap_eq φ V.toScheme, ordinaryChartUnitMap_eq φ S]
  have hUA := ordinaryFiniteSingleUnitPullback_hom A V.ι
  have hUA' := congrArg (fun z => (scalarExtension φ V.toScheme).map z) hUA
  have hUA'' : (scalarExtension φ V.toScheme).map
        ((ordinaryFiniteUnitPullback A V.ι).hom ≫
          (ordinaryFiniteSingleUnitIso A V.toScheme).hom) =
      (scalarExtension φ V.toScheme).map
        ((ordinaryFinitePullback A V.ι).map
          (ordinaryFiniteSingleUnitIso A S).hom ≫
          (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) V.ι).hom) := by
    simpa only [ordinaryFiniteSingleUnitIso] using hUA'
  have hmap := (scalarExtension φ V.toScheme).map_comp
    (ordinaryFiniteUnitPullback A V.ι).hom
    (ordinaryFiniteSingleUnitIso A V.toScheme).hom
  simp only [Category.assoc]
  rw [← reassoc_of% hmap, hUA'']
  have hmap2 := (scalarExtension φ V.toScheme).map_comp
    ((ordinaryFinitePullback A V.ι).map (ordinaryFiniteSingleUnitIso A S).hom)
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) V.ι).hom
  rw [hmap2]
  have hs := (scalarPullbackIso φ V.ι).hom.naturality
    (ordinaryFiniteSingleUnitIso A S).hom
  dsimp only [Functor.comp_map] at hs
  simp only [Category.assoc]
  simp only [ordinaryFiniteUnit, ordinaryFiniteDegreeZero, ordinaryFinitePullback] at hs ⊢
  rw [← reassoc_of% hs]
  rw [reassoc_of% (etaleScalarPullback_unit φ V.ι)]
  have hunitInv :
      (ordinaryFinitePullback B V.ι).map
          (ordinaryFiniteSingleUnitIso B S).inv ≫
          (ordinaryFiniteUnitPullback B V.ι).hom =
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} B) V.ι).hom ≫
          (ordinaryFiniteSingleUnitIso B V.toScheme).inv := by
    apply (cancel_mono (ordinaryFiniteSingleUnitIso B V.toScheme).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hcomp := congrArg (fun z ↦
      (ordinaryFinitePullback B V.ι).map (ordinaryFiniteSingleUnitIso B S).inv ≫ z)
      (ordinaryFiniteSingleUnitPullback_hom B V.ι)
    rw [← ordinaryFiniteSingleUnitIso_eq B S,
      ← ordinaryFiniteSingleUnitIso_eq B V.toScheme] at hcomp
    have hmapid := (ordinaryFinitePullback B V.ι).map_comp
      (ordinaryFiniteSingleUnitIso B S).inv
      (ordinaryFiniteSingleUnitIso B S).hom
    rw [Iso.inv_hom_id, (ordinaryFinitePullback B V.ι).map_id] at hmapid
    have hright :
        (ordinaryFinitePullback B V.ι).map (ordinaryFiniteSingleUnitIso B S).inv ≫
            (ordinaryFinitePullback B V.ι).map (ordinaryFiniteSingleUnitIso B S).hom ≫
            (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} B) V.ι).hom =
          (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} B) V.ι).hom := by
      rw [← Category.assoc, ← hmapid, Category.id_comp]
    rw [hright] at hcomp
    simpa only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      Functor.map_id, Category.comp_id, ordinaryFiniteSingleUnitIso_eq] using hcomp
  rw [← hunitInv]
  simp only [← Category.assoc]
  simp only [ordinaryFinitePullback]
  simp only [← Functor.map_comp]


end AlgebraicGeometry.Etale.VectorTraceScalar
