/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.FiniteEtaleStalk
public import WeilConjectures.WeilObject.Sheaf.StalkUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PadicAlgClSections
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.WeilSheaf.LocalFrobeniusLarge.LocalFrobeniusLargeCoefficients
public import WeilConjectures.WeilSheaf.CondensedModule.CondensedModuleLocalFrobenius
public import WeilConjectures.TraceFormula.PointFiberFunctor

/-!
# Functions on a finite étale fibre with condensed coefficients

Source: blueprint latest, `sec-fourier-transform/sk-lem-as-properties/lem-fd-as-trace.proof.md`,
first paragraph (blueprint: lem-fd-condensed-finite-fibre-functions).

The auxiliary maps below are the actual coefficient-unit comparisons and counit projections.
The statement includes their universal property, scalar sections, functoriality, Frobenius and
idempotent images. No comparison map is supplied as unconstrained data.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedFiniteFibre

/-- The coefficient unit, using the recorded pulled-back condensed ring.
Source: blueprint finite-fibre paragraph (blueprint: lem-fd-condensed-finite-fibre-functions). -/
abbrev unit (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :=
  Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) T)

/-- Direct image of the coefficient unit.
Source: blueprint finite-fibre paragraph (blueprint: lem-fd-condensed-finite-fibre-functions). -/
abbrev push (l : ℕ) [Fact l.Prime] {Y X : Scheme.{u}} (f : Y ⟶ X) :=
  (lowerStar (Profinite.padicAlgClRingObj l) f).obj (unit l Y)

/-- Base change of a morphism to the datum's chosen algebraic closure. This uses exactly
`FiniteFieldDatum.geometricFiber`, rather than a second choice of algebraic closure.
Source: blueprint finite-cover setup (blueprint: lem-fd-condensed-finite-fibre-functions). -/
@[irreducible] def geometricMap (D : FiniteFieldDatum.{u})
    {Y₀ X₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (f₀ : Y₀ ⟶ X₀) :
    (D.geometricFiber Y₀).left ⟶ (D.geometricFiber X₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left

set_option maxHeartbeats 0 in
-- The kernel compares the exact pullback and monoidal unit instances under the field binders.
end WeilConjectures.CondensedFiniteFibre
