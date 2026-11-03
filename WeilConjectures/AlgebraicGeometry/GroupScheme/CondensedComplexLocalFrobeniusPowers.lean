/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedDerived.CondensedScalarDerivedLocalFrobenius
public import WeilConjectures.SmoothPurity.WeilSheafComplex

import WeilConjectures.AlgebraicGeometry.Closed.ClosedPointField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.PathCategory.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented.Sections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-! # Local Frobenius powers on ordinary scalar stalk complexes

Source: latest blueprint, part-duality-trace-formula/sec-trace-formula/sec-tf-determinants/
sk-thm-trace-transport/thm-trf-l-function-euler-product.proof.md, Step 1, Local powers,
and Step 3.
(blueprint: lem-trf-condensed-complex-local-frobenius-powers).

The point sections are exact. Thus their derived functor is their
termwise localization, and these are the ordinary scalar derived stalks in the node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures
open NativeCondensedModule NativeCondensedDerived

/-- Semilinear return after n geometric Frobenius steps; the positive-power API uses n-1.
Source: latest blueprint, Step 1, Local powers, input (b).
(blueprint: lem-trf-condensed-complex-local-frobenius-powers). -/
abbrev scalarLocalReturn (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) (n : ℕ) : Prop :=
  z ≫ localPositivePower (D.geometricFrobenius X₀).hom (n - 1) =
    localPositivePower (frobeniusPointIso D).hom (n - 1) ≫ z

end WeilConjectures
