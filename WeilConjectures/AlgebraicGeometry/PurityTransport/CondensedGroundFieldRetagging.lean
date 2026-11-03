/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportAffineGeometry

/-! # Retagging a smooth datum without changing its relative geometry

Source: current blueprint, purity base change, the opening coefficient-transport
and orientation paragraphs. Retagging changes only the two structural maps.
(blueprint: def-pur-condensed-ground-field-retagging).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- Retagging keeps the source scheme literally unchanged.
Source: purity base change, identification of sites
(blueprint: def-pur-condensed-ground-field-retagging). -/
theorem retagSmoothDatum_X (D : WeilConjectures.FiniteFieldDatum.{u})
    (σ : D.k ≃+* D.k) (s : SmoothDatum D) :
    (retagSmoothDatum D σ s).X.left = s.X.left := rfl

/-- Retagging keeps the target scheme literally unchanged.
Source: purity base change, identification of sites
(blueprint: def-pur-condensed-ground-field-retagging). -/
theorem retagSmoothDatum_Y (D : WeilConjectures.FiniteFieldDatum.{u})
    (σ : D.k ≃+* D.k) (s : SmoothDatum D) :
    (retagSmoothDatum D σ s).Y.left = s.Y.left := rfl

/-- Neither the relative morphism nor its dimension and compactification changes.
Source: purity base change, identical diagonal and compact-support composite
(blueprint: def-pur-condensed-ground-field-retagging). -/
theorem retagSmoothDatum_relative (D : WeilConjectures.FiniteFieldDatum.{u})
    (σ : D.k ≃+* D.k) (s : SmoothDatum D) :
    (retagSmoothDatum D σ s).map = s.map ∧
      (retagSmoothDatum D σ s).dim = s.dim ∧
      (retagSmoothDatum D σ s).compactification = s.compactification :=
  ⟨rfl, rfl, rfl⟩

/-- The retagged standard affine chart is the standard affine chart of the
retagged base. All structure-map proof fields agree by proof irrelevance.
Source: purity base change, unchanged Kummer-normalized affine-line integration
(blueprint: def-pur-condensed-ground-field-retagging). -/
theorem retagSmoothDatum_affine (D : WeilConjectures.FiniteFieldDatum.{u})
    (σ : D.k ≃+* D.k) (Y : Over (Spec (.of D.k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] :
    retagSmoothDatum D σ (affineDatum D Y) =
      affineDatum D (retagSmoothDatum D σ (affineDatum D Y)).Y := by
  dsimp [retagSmoothDatum, affineDatum]
  congr 1


end AlgebraicGeometry.ProEtale.PurityTransport
