/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.LatticePairRestriction
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperations
public import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackage

/-!
# Strict-perfect packages with independent site universes

Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
The original package is reexported; this interface retains the small pro-etale site.
-/

@[expose] public section

set_option autoImplicit false
attribute [instance] CategoryTheory.module_overFunctor_preservesZero

universe u v w r

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

end SheafOfModules

namespace SheafOfModules

section SmallRingedSite

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}

end SmallRingedSite

end SheafOfModules

namespace AlgebraicGeometry.Scheme

/-- The locally bijective sheafification criterion on that same slice.
Source: Stacks, Tag 03DA (blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
instance strictPerfectSliceLocallyBijective (X : Scheme.{u}) (V : X.ProEt) :
    ((ProEt.topology X).over V).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  letI : EssentiallySmall.{u + 1} (Over V) := essentiallySmallSelf.{0} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

end AlgebraicGeometry.Scheme
