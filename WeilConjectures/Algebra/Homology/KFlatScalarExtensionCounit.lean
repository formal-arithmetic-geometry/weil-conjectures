/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.BifunctorShift
import all WeilConjectures.Algebra.Homology.KFlatScalarExtensionDerivedIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Universal scalar extension counit on a K-flat complex

## References

* Stacks Project, Tags 06Y6, 064L and 06Y4
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
open CategoryTheory.Limits MonoidalCategory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

/-- The universal derived scalar extension counit is invertible on K-flat complexes. -/
theorem scalarExtensionCounit_isIso_of_kFlat
    {R B : Type u} [CommRing R] [CommRing B] (f : R →+* B)
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : ∀ L : CochainComplex (ModuleCat.{u} R) ℤ, L.Acyclic →
      (CochainComplex.mapBifunctor L P (MonoidalCategory.curriedTensor _)).Acyclic)
    (LF : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      (extendScalars f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))) :
    IsIso (ε.app ((HomotopyCategory.quotient _ _).obj P))  := by
  classical
  have (N : ModuleCat.{u} R) : PreservesColimitsOfShape ℤ
      ((curriedTensor (ModuleCat.{u} R)).flip.obj N) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (tensorRight N))
  have : HasExactColimitsOfShape ℤ (ModuleCat.{u} R) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} R)
      (AsSmall.equiv (C := ℤ)).symm
  have : (extendScalars f).PreservesKFlatQuasiIso :=
    ⟨fun hK hL a ↦ CochainComplex.scalarExtension_quasiIso_of_kFlat f a
      (show QuasiIso a from inferInstance) hK hL⟩
  exact ((extendScalars f).isLeftDerivedFunctor_iff_isIso_app_of_kFlat ε).1 hLF P
    (CochainComplex.kFlat_of_acyclic_tensor P hP)

end ModuleCat
