/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.InjectiveModuleCechAugmentationPositive
import WeilConjectures.AlgebraicGeometry.InjectiveModuleCechAugmentationZero

/-! # The augmented Čech complex of an injective module

## References

* Stacks Project, Cohomology of Sheaves, Tags 01EP and 01EQ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- For an open cover, restriction of global sections into the Čech complex of a
single injective module is a quasi-isomorphism. The supplied map's degree-zero
component is precisely the canonical restriction map, including the scalar
identification at the whole space. (Stacks, Tags 01EP, 01EQ.) -/
theorem injectiveModuleCechAugmentation_quasiIso {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (J : X.Modules) [Injective J]
    (ht : (X.ringCatSheaf.obj.map (isTerminalTop.op.to (op ⊤))).hom =
      RingHom.id Γ(X, ⊤))
    (b : (CochainComplex.single₀ (ModuleCat.{u} Γ(X, ⊤))).obj
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj J) ⟶
      (CategoryTheory.cechComplexFunctor U).obj J.presheafModuleCat)
    (hb : b.f 0 =
      (ModuleCat.restrictScalarsId'App
        (X.ringCatSheaf.obj.map (isTerminalTop.op.to (op ⊤))).hom ht
        (J.val.obj (op ⊤))).inv ≫
      Pi.lift fun y : Fin 1 → ι =>
        J.presheafModuleCat.map (homOfLE (le_top (a := ∏ᶜ fun l => U (y l)))).op) :
    QuasiIso b := by
  rw [quasiIso_iff]
  intro n
  by_cases hn : n = 0
  · subst n
    exact injectiveModuleCechAugmentation_quasiIsoAt_zero U hU J ht b hb
  · apply injectiveModuleCechAugmentation_quasiIsoAt_positive U hU J ht b hb n
    omega

end AlgebraicGeometry.Scheme.Modules
