/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective
import Mathlib.CategoryTheory.Abelian.Projective.Basic

/-! # Exact terminal scalar sections without auxiliary coefficient interfaces

Source: Stacks 03CW and 0946; latest blueprint, exact geometric-point sections.
(blueprint: lem-weil-point-proetale-sections-exact).

Hom from the regular module is actual module sections. Its scalar action is restriction
along the strong monoidal pullback of the condensed global sections Lambda(*).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeCondensedPoint

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Modules over the canonical pulled-back condensed coefficient ring.
Source: latest blueprint, module sections (blueprint: lem-weil-point-proetale-sections-exact). -/
abbrev Modules (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)

/-- Canonical action of condensed global scalars on the regular point module.
Source: latest blueprint, scalar restriction (blueprint: lem-weil-point-proetale-sections-exact). -/
def scalarAction (k : Type u) [Field k] :
    MonObj.Γ Λ →+* End (𝟙_ (Modules Λ (Spec (.of k)))) :=
  letI : (upperStarFromPoint (Spec (.of k))).Additive :=
    haveI : PreservesColimits (upperStarFromPoint (Spec (.of k))) :=
      (pointUpperStarLowerStarAdjunction.comp
        (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1}
          (toSpecZ (Spec (.of k))))).leftAdjoint_preservesColimits
    haveI : PreservesBinaryBiproducts (upperStarFromPoint (Spec (.of k))) :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    Functor.additive_of_preservesBinaryBiproducts _
  Mod.regularEndRingHom.comp (MonObj.Γ.mapFunctor (upperStarFromPoint (Spec (.of k))))

/-- The opposite regular action used by the covariant Hom-from-unit functor.
Source: latest blueprint, scalar restriction (blueprint: lem-weil-point-proetale-sections-exact). -/
def scalarsOp (k : Type u) [Field k] :
    MonObj.Γ Λ →+* (End (𝟙_ (Modules Λ (Spec (.of k)))))ᵐᵒᵖ :=
  (scalarAction Λ k).toOpposite fun x y ↦ by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]

/-- Terminal module sections with their canonical Lambda(*) action.
Source: latest blueprint, Gamma(s,-) (blueprint: lem-weil-point-proetale-sections-exact). -/
def sections (k : Type u) [Field k] :
    Modules Λ (Spec (.of k)) ⥤ ModuleCat.{u + 1} (MonObj.Γ Λ) :=
  preadditiveCoyonedaObj (𝟙_ (Modules Λ (Spec (.of k)))) ⋙
    ModuleCat.restrictScalars (scalarsOp Λ k)

end WeilConjectures.NativeCondensedPoint
