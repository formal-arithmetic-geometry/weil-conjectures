/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.AlgebraicGeometry.Adic.AdicLisseModuleSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.Topology.Stratification
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower

/-!
# Uniformly bounded constructible adic towers

Source: blueprint sec-proper-base-change/sk-thm-properbasechange,
def-weil-pbc-bounded-constructible-tower, order 1250; Stacks Tags 09AI and 09BT
(blueprint: def-weil-pbc-bounded-constructible-tower).

Positive level n+1 is indexed by n : ℕ. Normalizations are stored for every comparable
pair; their cocycle determines the nonconsecutive ones from the consecutive ones.
Compatibility is expressed on their adjoints M_b→Res(M_a). The tensor-unit normalized
scalar-extension adjunction makes this equivalent to the displayed normalization
identities in the blueprint. This permits restrictions to retain their actual
inverse-image coefficients, without choosing a tensor/pullback comparison.

## Main definitions

* `AdicTower`: a derived strict tower with quotient-linear normalized levels.
* `AdicTowerLocalModel`: one bounded local complex and its compatible reductions.
* `IsUniformlyBoundedConstructibleAdicTower`: common bounds, finite strata and local models.
* `pbcLevelConstantComparison` and `pbcCompletedComparison`: canonical coefficient
  presentation comparisons fixed on constant sections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

variable {X} {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)

variable {B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
  (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)

variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

variable {X} {Y : Scheme.{u}} (g : Y ⟶ X)

end AlgebraicGeometry.Scheme
