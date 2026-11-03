/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.DncCoefficientTransport.DncCoefficientTransportData
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartExceptionalScalar
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-! # Smooth dualizing coefficient comparison in ordinary etale coordinates -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem ordinary_smooth_coordinate_chart
    {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (g : V ⟶ S) [IsSeparated g] (d : ℕ) [SmoothOfRelativeDimension d g] (x : V) :
    ∃ (W : V.Opens) (_ : x ∈ W) (e : W.toScheme ⟶ affineTraceTower S d),
      AlgebraicGeometry.Etale e ∧ IsSeparated e ∧ LocallyOfFiniteType e ∧
        QuasiCompact e ∧ W.ι ≫ g = e ≫ affineTraceProjection S d := by
  obtain ⟨T, W, hT, hW, _, hx, hWT, e₀, he₀, he₀g⟩ :=
    Smooth.exists_etale_to_affineSpace g d x
  have : IsAffine W.toScheme := hW
  have : AlgebraicGeometry.Etale e₀ := he₀
  have : IsOpenImmersion (AffineSpace.map (ULift.{u} (Fin d)) T.ι) :=
    MorphismProperty.of_isPullback
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin d)) T.ι).flip
      (inferInstance : IsOpenImmersion T.ι)
  let a := e₀ ≫ AffineSpace.map (ULift.{u} (Fin d)) T.ι
  have ha : W.ι ≫ g = a ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) := by
    dsimp only [a]
    rw [Category.assoc, AffineSpace.map_over, ← Category.assoc, he₀g,
      Scheme.Hom.resLE_comp_ι]
  have : IsSeparated a := inferInstance
  let e := a ≫ (affineTraceAffineSpaceIso S d).inv
  have : AlgebraicGeometry.Etale e := inferInstance
  have : IsSeparated e := inferInstance
  have : LocallyOfFiniteType e := inferInstance
  have : QuasiCompact e := inferInstance
  refine ⟨W, hx, e, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  have hp : affineTraceToAffineSpace S d ≫
      (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = affineTraceProjection S d :=
    AffineSpace.homOfVector_over _ _
  rw [ha, ← hp]
  change a ≫ _ = a ≫ (affineTraceAffineSpaceIso S d).inv ≫
    (affineTraceAffineSpaceIso S d).hom ≫ _
  rw [Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Etale
