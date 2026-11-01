/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationDirectSumCounit.VectorIntegrationDirectSumCounitMaps
import all WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationOverlapCoordinates
import all WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry

/-! # Coordinates of the flattened simultaneous bundle chart

This comparison is entirely a statement about morphisms of schemes.
(blueprint: lem-pur-vector-integration-total-counit-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

open Opposite VectorBundleZeroSection
attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom

section Frames
variable (S : Scheme.{u}) (r s : ℕ) (F G : S.Modules)
  (V U : S.Opens) (eF : Trivialization S r F V) (eG : Trivialization S s G U)
  (W : S.Opens) (hWV : W ≤ V) (hWU : W ≤ U)

end Frames

private theorem transport_projection (T : Scheme.{u}) {d e : ℕ} (h : d = e) :
    eqToHom (congrArg (affineTraceTower T) h) ≫ affineTraceProjection T e =
      affineTraceProjection T d := by
  cases h
  exact Category.id_comp _

end AlgebraicGeometry.Etale
