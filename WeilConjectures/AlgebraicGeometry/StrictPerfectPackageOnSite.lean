/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperations
public import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackage

/-!
# Strict-perfect packages with independent site universes

The original package is reexported; this interface retains the small pro-etale site.

## References

* [Stacks Project, Tag 03DA](https://stacks.math.columbia.edu/tag/03DA)
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

/-- Abelian sheafification on a small pro-etale slice in the coefficient universe. -/
instance strictPerfectSliceSheafify (X : Scheme.{u}) (V : X.ProEt) :
    HasSheafify ((ProEt.topology X).over V) AddCommGrpCat.{u + 1} :=
  letI : EssentiallySmall.{u + 1} (Over V) := essentiallySmallSelf.{0} _
  hasSheafifyEssentiallySmallSite _ _

/-- The locally bijective sheafification criterion on that same slice. -/
instance strictPerfectSliceLocallyBijective (X : Scheme.{u}) (V : X.ProEt) :
    ((ProEt.topology X).over V).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  letI : EssentiallySmall.{u + 1} (Over V) := essentiallySmallSelf.{0} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

end AlgebraicGeometry.Scheme
