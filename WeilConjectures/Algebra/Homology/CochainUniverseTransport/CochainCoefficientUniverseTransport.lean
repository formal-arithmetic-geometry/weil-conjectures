/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Sites.SheafOfTypes

import Mathlib.Algebra.Category.Ring.Adjunctions
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-! # Canonical coefficient and module size transport

Source: Stacks, Modules on Sites, 03DA and 03EK, using the invariance of
sheaf conditions and balanced tensors under sectionwise isomorphism
(blueprint: def-pur-cochain-coefficient-universe-transport).

All carriers below are explicitly ULift, all restrictions apply the original
restriction to ULift.down, and all scalars act through ULift.down. In particular
this construction does not equate site, ring, or module universes.
-/

@[expose] public section
universe uC vC r m w z
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules.CochainUniverseTransport
set_option autoImplicit false
set_option linter.checkUnivs false

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}

variable (R : Sheaf J CommRingCat.{r})

-- Lift a bilinear map without unfolding the surrounding sheaf constructions.

-- The sectionwise tensor equivalence is compatible with every restriction.

-- The tensor map is the lifted sheafification unit, up to the tensor equivalence.

end SheafOfModules.CochainUniverseTransport
