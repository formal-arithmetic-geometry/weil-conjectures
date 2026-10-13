/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-! # A fixed module resolution computes Ext from the structure sheaf

Source: Stacks Project, Cohomology, Tags 01DZ and 0B6A.
(blueprint: lem-sc-module-resolution-homology-ext).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}}

local instance moduleResolution_enoughInjectives :
    EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
  (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
local instance moduleResolution_hasExt : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
  hasExt_of_enoughInjectives.{u, u, u + 1} (SheafOfModules.{u} X.ringCatSheaf)

/-- A single fixed injective module resolution computes Ext from the structure sheaf.
Source: Stacks Project, Cohomology, Tag 01DZ (cohomology of modules) and Tag 0B6A
(cohomology as Ext from the structure sheaf).
(blueprint: lem-sc-module-resolution-homology-ext).

Proof: An O-linear map from the structure sheaf is determined by the image of 1
on the whole space. Conversely a global section defines such a map by multiplying
its restrictions by local functions. These maps are inverse and additive, and
commute with the differentials of I. Thus cocycles in the sections complex identify
with cocycle maps from the structure sheaf into I. Under this identification,
boundaries identify with null-homotopic cocycle maps: in positive degree they are
maps factoring through the preceding differential, and in degree zero both boundary
subgroups are zero. Taking quotients gives an additive equivalence with cohomology
classes from the degree-zero structure sheaf to I. Compose with the inverse of
I.extAddEquivCohomologyClass. The class of a cocycle map is I.extMk of that map,
which proves the displayed formula. It also uniquely determines the equivalence
because every homology class has a cycle representative. The argument includes
zero modules and the empty scheme, where both groups are zero. No comparison
between different resolutions is asserted here. -/
theorem moduleResolutionHomologyExtEquiv (F : SheafOfModules.{u} X.ringCatSheaf)
    (I : InjectiveResolution F) (n : ℕ) :
    ∃ e : (RingedSpace.globalSectionsComplex I).homology n ≃+
        Abelian.Ext.{u} (SheafOfModules.unit X.ringCatSheaf) F n,
      ∀ (a : (RingedSpace.globalSectionsComplex I).cycles n)
        (φ : SheafOfModules.unit X.ringCatSheaf ⟶ I.cocomplex.X n)
        (hφ : φ ≫ I.cocomplex.d n (n + 1) = 0),
        φ.val.app (op ⊤) (1 : Γ(X, ⊤)) =
          (RingedSpace.globalSectionsComplex I).iCycles n a →
        e ((RingedSpace.globalSectionsComplex I).homologyπ n a) =
          I.extMk φ (n + 1) rfl hφ := by sorry

end
end AlgebraicGeometry.Scheme.Modules
