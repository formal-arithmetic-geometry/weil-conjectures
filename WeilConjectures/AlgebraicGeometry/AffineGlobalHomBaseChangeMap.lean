/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
public import WeilConjectures.AlgebraicGeometry.GlobalHomOriginalCounitNormalization
import WeilConjectures.AlgebraicGeometry.OriginalCounitAdjunctionTransport
import WeilConjectures.AlgebraicGeometry.NormalizedInternalHomPullbackComparison
import WeilConjectures.AlgebraicGeometry.AffineSectionsPushforwardNormalization

/-!
 # The affine global derived Hom base-change comparison
Source: Stacks Project, perfect.tex, Tag 0AA7 (blueprint:
def-pc-affine-global-hom-base-change-map).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
noncomputable section
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]

-- Keep the concrete scalar-derived resolution machinery out of unrelated proof search.
attribute [local irreducible] affineDerivedExtension affineDerivedExtensionAdjunction

attribute [local irreducible] canonicalPullbackAdjunction
  schemeHomOriginalPullbackAdjunction schemeHomPullbackCounitIso

end AlgebraicGeometry
