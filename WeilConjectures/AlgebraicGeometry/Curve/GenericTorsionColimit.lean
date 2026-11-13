/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.Curve.GenericTorsionFiniteStalk
import WeilConjectures.AlgebraicGeometry.Curve.GenericTorsionCohomologyColimit

/-! # Finite-stalk approximation for a generic torsion sheaf
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- A generic torsion sheaf on a qcqs integral scheme is a filtered colimit of finite-stalk
sheaves, and applying generic direct image and cohomology preserves this presentation. -/
theorem exists_generic_torsion_finite_stalk_cohomology_colimit
    (X : Scheme.{u}) [IsIntegral X] [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hM : M.IsTorsion) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (F : I ⥤ Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
      (ι : F ⟶ (Functor.const I).obj M),
      (∀ i, (F.obj i).IsTorsion) ∧
      (∀ i, Finite (((pointSmallEtale
        (Spec.map (CommRingCat.ofHom
          (algebraMap X.functionField (AlgebraicClosure X.functionField))))).sheafFiber
            (A := AddCommGrpCat.{u + 1})).obj (F.obj i))) ∧
      Nonempty (IsColimit (Cocone.mk M ι)) ∧
      ∀ q : ℕ, Nonempty (IsColimit
        (((Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField) ⋙
          Sheaf.functorH X.smallEtaleTopology q).mapCocone (Cocone.mk M ι))) := by
  obtain ⟨I, hI, hfiltered, F, ι, htor, hfin, hcolim⟩ :=
    exists_generic_torsion_finite_stalk_colimit X M hM
  let _ := hI
  let _ := hfiltered
  refine ⟨I, hI, hfiltered, F, ι, htor, hfin, hcolim, ?_⟩
  exact generic_torsion_cohomology_colimit X M hcolim


end AlgebraicGeometry.Scheme
