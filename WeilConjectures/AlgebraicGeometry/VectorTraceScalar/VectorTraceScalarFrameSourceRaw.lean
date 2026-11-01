/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarData

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open WeilConjectures.PurityFiniteSetting
namespace AlgebraicGeometry.Etale.VectorTraceScalar

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]

/-- The local frame trace can be replaced by the pullback of the canonical glued
integration map before scalar transport.  This is the raw gluing step in the frame
source calculation.
Source: blueprint/latest, sec-smooth-purity/sk-prop-an, paragraph 2.
(blueprint: new-lem-pur-vector-scalar-frame-source-raw).
-/
theorem frame_scalar_source_raw (N : ℕ) (hN : 0 < N) (φ : A →+* B)
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
        (unit φ V.toScheme) =
      (scalarPullbackIso φ V.ι).hom.app (vectorIntegrationSource A N hA S r F) ≫
        (scalarExtension φ V.toScheme).map
          ((ordinaryFinitePullback A V.ι).map
              ((vectorIntegrationGluing N hN A hA S hS r F).1.hom ≫
                (DerivedCategory.singleFunctor _ 0).map
                  (vectorIntegrationGluing N hN A hA S hS r F).2) ≫
            (ordinaryFiniteUnitPullback A V.ι).hom) ≫
        (unit φ V.toScheme) := by
  have hn := (existsUnique_vectorIntegrationGluing N hN A hA S hS r F).2.exists.choose_spec
  have hlocal := hn.2 t D V e
  have hmap := congrArg
    (fun z ↦ (scalarExtension φ V.toScheme).map z ≫ unit φ V.toScheme) hlocal
  have hmap' := congrArg
    (fun z ↦ (scalarPullbackIso φ V.ι).hom.app
      (vectorIntegrationSource A N hA S r F) ≫ z) hmap.symm
  simpa only [vectorIntegrationGluing, Functor.map_comp, Category.assoc,
    ordinaryFiniteUnit, ordinaryFiniteConstant] using hmap'


end AlgebraicGeometry.Etale.VectorTraceScalar
