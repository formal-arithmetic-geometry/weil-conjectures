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
import WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque
import WeilConjectures.Topology.Sheaves.CechFlasque
import WeilConjectures.Topology.Sheaves.CechComparison
public import Mathlib.Algebra.Category.Grp.Zero

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Positive-degree part of the augmented Čech quasi-isomorphism. (Stacks, Tag 01EP.) -/
theorem injectiveModuleCechAugmentation_quasiIsoAt_positive {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (_hU : iSup U = ⊤) (J : X.Modules) [Injective J]
    (ht : (X.ringCatSheaf.obj.map (isTerminalTop.op.to (op ⊤))).hom =
      RingHom.id Γ(X, ⊤))
    (b : (CochainComplex.single₀ (ModuleCat.{u} Γ(X, ⊤))).obj
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj J) ⟶
      (CategoryTheory.cechComplexFunctor U).obj J.presheafModuleCat)
    (_hb : b.f 0 =
      (ModuleCat.restrictScalarsId'App
        (X.ringCatSheaf.obj.map (isTerminalTop.op.to (op ⊤))).hom ht
        (J.val.obj (op ⊤))).inv ≫
      Pi.lift fun y : Fin 1 → ι =>
        J.presheafModuleCat.map (homOfLE (le_top (a := ∏ᶜ fun l => U (y l)))).op)
    (n : ℕ) (hn : 0 < n) : QuasiIsoAt b n := by
  apply (quasiIsoAt_iff_isIso_homologyMap _ _).2
  have hs := HomologicalComplex.isZero_single_obj_homology
    (ComplexShape.up ℕ) 0
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj J) n (Nat.ne_of_gt hn)
  let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj J
  have : TopCat.Presheaf.IsFlasque F.obj := isFlasque_of_injective J
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have he := TopCat.Sheaf.exactAt_cechComplex_of_isFlasque U q F
  have hz := he.isZero_homology
  have hz' : IsZero ((forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).obj
      (((CategoryTheory.cechComplexFunctor U).obj J.presheafModuleCat).homology
        (q + 1))) :=
    hz.of_iso (TopCat.Presheaf.cechComplexFunctorHomologyIso U J.presheafModuleCat
      (q + 1))
  have htgt : IsZero
      (((CategoryTheory.cechComplexFunctor U).obj J.presheafModuleCat).homology
        (q + 1)) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact (AddCommGrpCat.isZero_iff_subsingleton.mp hz')
  exact hs.isIso htgt _

end AlgebraicGeometry.Scheme.Modules
