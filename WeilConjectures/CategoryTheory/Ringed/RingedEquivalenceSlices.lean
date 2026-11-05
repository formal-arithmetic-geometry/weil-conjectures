/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Ringed.RingedPresentationData
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-! # Auxiliary ringed presentation comparisons -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
namespace CategoryTheory
-- Cache the sheaf limit instances used repeatedly by the slice comparisons.

-- Products over a sheaf, and their images under the supplied fibre equivalences.

attribute [local instance] ringSections

-- Transport the ring operations through the product/fibre comparison.

-- Fibrewise pullbacks give the further-restriction comparison.

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

-- Compatibility of the product comparisons with further restriction.
attribute [irreducible] sliceComparison

-- Recover module inverse images from their specified adjunctions and linearity.

attribute [irreducible] inverseModulesIso

-- Use precomposition internally; compare explicitly with scalar restriction by identity.

attribute [irreducible] moduleSquareSets

-- A compatible square of set inverse images lifts to a square of module inverse images.

attribute [irreducible] moduleSquare

-- The original existential binders h and k are retained verbatim.
end CategoryTheory
