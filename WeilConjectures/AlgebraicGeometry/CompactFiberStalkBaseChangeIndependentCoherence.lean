/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactifCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.KunnethDefs
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness

/-!
# Finite-coefficient compactification coherence for stalk exchange

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/thm-pur-rank-one-thom.proof.md, Step 3,
compact-support compatibility (blueprint: lem-pur-cfiber-stalk-base-change-independent-coherence).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The canonical compactification comparison transported along an étale-origin witness.
Source: the compact-support compatibility calculation in Step 3 of the rank-one Thom proof
(blueprint: lem-pur-cfiber-stalk-base-change-independent-coherence). -/
noncomputable def transportedCompactificationComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} A))}
    (α : (D(ν^*(X)[ModuleCat.{u + 1} A])).obj L.obj ≅ K) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).obj K :=
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map α.inv ≫
    (comparisonUpperStarPlusEtaleOriginCompIso A c).hom.app L ≫
    D(ν^*(Y)[ModuleCat.{u + 1} A]).map
      (DerivedCategory.Plus.ι.map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c d).hom.app L)) ≫
    (comparisonUpperStarPlusEtaleOriginCompIso A d).inv.app L ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map α.hom

end AlgebraicGeometry.ProEtale
