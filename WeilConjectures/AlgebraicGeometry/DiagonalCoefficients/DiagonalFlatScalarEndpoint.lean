/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientEndpoints
import WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all WeilConjectures.CategoryTheory.FlatScalarUnit

/-! # The normalized derived scalar endpoint of a flat internal module

Source: Stacks Project, Tag 06YY, K-flat computation of derived scalar extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] Functor.leftDerivedFunctor
  Mod.derivedExtendMapDerivedCategoryAdjunction

/-- A flat internal module has a unique scalar-endpoint isomorphism with the
prescribed ordinary unit as its derived adjoint.

Source: Stacks Project, Tag 06YY. -/
theorem diagonal_flat_scalar_endpoint_iso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u}) (M : Modules Λ X)
    (hM : ObjectProperty.flat M) :
    ∃! i : (derivedScalars a X).obj
        ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M) ≅
        (DerivedCategory.singleFunctor (Modules Λ' X) 0).obj
          ((Mod.extendScalars (coefficientMap a X)).obj M),
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).homEquiv _ _
          i.hom =
        (DerivedCategory.singleFunctor (Modules Λ X) 0).map
            (Mod.extendUnit (coefficientMap a X) M) ≫
          ((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).inv.app
            ((Mod.extendScalars (coefficientMap a X)).obj M) := by
  let E : Modules Λ X ⥤ Modules Λ' X := Mod.extendScalars (coefficientMap a X)
  let U : Modules Λ' X ⥤ Modules Λ X := Mod.comap (coefficientMap a X)
  let adj := Mod.extendRestrictAdjunction (coefficientMap a X)
  let ad := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)
  let P := (HomologicalComplex.single (Modules Λ X) (.up ℤ) 0).obj M
  let t := (ad.homEquiv _ _).symm
    ((DerivedCategory.singleFunctor (Modules Λ X) 0).map (adj.unit.app M) ≫
      (U.mapDerivedCategorySingleFunctor 0).inv.app (E.obj M))
  have ht : t = (ad.homEquiv _ _).symm
      (DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom.app M) := by
    rw [← Adjunction.homEquiv_naturality_right_symm]
    apply congrArg (ad.homEquiv _ _).symm
    simpa only [Category.assoc] using
      (SheafExactDegreeZero.derived_single_unit_square E U adj M).symm
  have hP := (CochainComplex.kFlat_single_obj_iff_flat M 0).mpr hM
  have hraw := Adjunction.isIso_cochainTranspose_of_kFlat E U adj ad P hP
  have : IsIso t := by rw [ht]; infer_instance
  refine ⟨asIso t, (ad.homEquiv _ _).apply_symm_apply _, ?_⟩
  intro j hj
  apply Iso.ext
  apply (ad.homEquiv _ _).injective
  exact hj.trans ((ad.homEquiv _ _).apply_symm_apply _).symm

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
