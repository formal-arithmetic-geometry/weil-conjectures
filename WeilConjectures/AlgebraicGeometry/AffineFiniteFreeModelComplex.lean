/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.Extend

/-! # The explicit complex associated to an affine resolution

Source: Stacks Project, Tag 068C.
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The sheafification of a chain complex of modules on an affine chart, extended using
`n ↦ -n` and transported to the localized site (Stacks, Tag 068C). -/
noncomputable def affineFiniteFreeModelComplex {Y : Scheme.{u}}
    (U : Y.Opens) (hU : IsAffineOpen U)
    (K : ChainComplex (ModuleCat.{u} (Γ(Y, U) : Type u)) ℕ) :
    CochainComplex (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U)) ℤ :=
  ((Scheme.Modules.overEquiv U).inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((((tilde.functor Γ(Y, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapHomologicalComplex
       (ComplexShape.down ℕ)).obj K).extend ComplexShape.embeddingDownNat)

end AlgebraicGeometry
