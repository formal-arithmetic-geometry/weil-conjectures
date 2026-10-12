/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence

/-! # Affine-local cohomology of derived pullback

Source: Stacks Project, Tag 08DW, part (1), with its affine calculation in part (2).
(blueprint: lem-pc-derived-pullback-qcoh-component).
-/

@[expose] public section

universe uX wD

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- Affine-local cohomology calculation for derived pullback.
Source: Stacks Project, Tag 08DW(1), proof using Tag 08DW(2) and Tag 06Z0.
Proof: the affine opens U and V give a morphism U → V. Exact restriction
commutes with cohomology. On U, restriction of the pullback is the pullback of E|V,
by the open-restriction comparison. Represent E|V by tilde of a module complex using
06Z0. The affine pullback comparison expresses its pullback as tilde of the module
complex obtained by derived base change. Exactness of tilde identifies its cohomology
with tilde of module cohomology, which is quasi-coherent. Transfer along the comparison
isomorphisms and pass to the over category of U. This includes empty opens and arbitrary degrees;
no boundedness or flatness of f is used.
(blueprint: lem-pc-derived-pullback-qcoh-component). -/
theorem derivedPullback_cohomology_over_affine {X Y : Scheme.{uX}} (f : X ⟶ Y)
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings Y.toRingedSpace))]
    (E : schemeDerivedCategory Y) (hE : schemeDerivedQCohProperty Y E)
    (n : ℤ) (U : X.Opens) (V : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) :
    (((DerivedCategory.homologyFunctor
      (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) n).obj
        ((derivedPullback f).obj E)).over U).IsQuasicoherent := by
  sorry

end AlgebraicGeometry
