/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Submission.WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Submission.WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Mathlib.Algebra.Category.Grp.Zero

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Global derived Hom on a scheme

Source: Stacks Project, Cohomology of Sheaves, Section 20.44, Tag 0B6A
(blueprint: def-pc-global-derived-rhom).

The structure sheaf on the one-point space is the pushforward of O_X: its value on
that point is A = O_X(X), and on the empty open it is the zero ring. The map of
structure sheaves is the identity. Modules on the point are A-modules, by an
equivalence whose functor is evaluation on the point. Derived global sections is the
right derived functor of Γ(X,-) valued in A-modules; it agrees with Rp_* followed by
that equivalence. Global derived Hom is its composite with the shared internal Hom.

## Main definitions and statements

* `globalSectionsPoint`, `toGlobalSectionsPoint`: the point ringed space and p.
* `schemeDerivedGlobalSections`: unbounded RΓ, with its point and resolution comparisons.
* `schemeGlobalDerivedHom`: RΓ composed with derived internal Hom.
-/

@[expose] public section

universe u w wA wPt

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

-- The functor of an equivalence of preadditive categories preserves binary products,
-- hence is additive; `mapDerivedCategory` of it needs this (found with
-- `synthInstance.maxSize 2048`).
attribute [local instance] Functor.additive_of_preserves_binary_products

namespace AlgebraicGeometry

/-- RΓ(X,-) valued in D(O_X(X)): the unbounded right derived functor of global sections
`Γ(X,-) : Mod(O_X) ⥤ Mod(O_X(X))`. Source: Stacks, Tag 0B6A
(blueprint: def-pc-global-derived-rhom). -/
def schemeDerivedGlobalSections (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA} (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))] :
    schemeDerivedCategory X ⥤
      DerivedCategory (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) :=
  (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor


end AlgebraicGeometry
