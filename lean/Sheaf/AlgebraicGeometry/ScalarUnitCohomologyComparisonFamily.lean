/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic

/-! # The explicit module-to-abelian comparison for unit coefficients

Source: Stacks Project, Tag 03FD.
(blueprint: new-sc-scalar-unit-comparison-family).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme
open Modules

/-- Forget a module Ext class and precompose with the constant-integer class of the
unit section. The source is the underlying additive group of restricted-scalar cohomology;
thus this construction is independent of the structure morphism to the field.
Source: Stacks Project, Tag 03FD, and the constant-sheaf adjunction.
(blueprint: new-sc-scalar-unit-comparison-family). -/
noncomputable def scalarUnitAbelianComparison (X : Scheme.{u}) :
    ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj
      (SheafOfModules.unit X.ringCatSheaf)) →+ Sheaf.H (structureSheafAb X) 1 := by
  let : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hasExt_of_enoughInjectives _
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  have : PreservesFiniteColimits T :=
    SheafOfModules.preservesFiniteColimits_toSheaf X.ringCatSheaf
  let s : Sheaf.H (T.obj (SheafOfModules.unit X.ringCatSheaf)) 0 :=
    (Sheaf.H.equiv₀ _ isTerminalTop).symm (1 : Γ(X, ⊤))
  exact (s.precomp _ (zero_add 1)).comp
    ((T.mapExtAddHom _ _ 1).comp
      (moduleExtEquiv (SheafOfModules.unit X.ringCatSheaf) 1).toAddMonoidHom)

/-- The explicit comparison is bijective; no assertion about pullbacks is made here.
Source: Stacks Project, Tag 03FD, lemma-cohomology-modules-abelian-agree.
(blueprint: new-sc-scalar-unit-comparison-family).

Proof: Resolve the unit module by injective module sheaves. Forgetting to abelian sheaves
is exact and the forgotten injectives are acyclic for sections by Tag 03FD. Consequently
both derived sections groups are computed by the same underlying additive sections complex.
The module Ext comparison evaluates a morphism from the unit at its section 1, as specified
by exists_moduleExtEquiv. After forgetting modules, precomposition with the integer-unit
class does exactly the same evaluation: the constant-sheaf adjunction sends that class to 1.
Thus scalarUnitAbelianComparison is the common-resolution comparison on degree-one homology,
which is an isomorphism. This also handles the empty scheme, whose sections complex is zero;
no nonemptiness or finiteness assumption is used. -/
theorem scalar_unit_abelian_comparison_bijective (X : Scheme.{u}) :
    Function.Bijective (scalarUnitAbelianComparison X) := by
  sorry

end AlgebraicGeometry.Scheme
