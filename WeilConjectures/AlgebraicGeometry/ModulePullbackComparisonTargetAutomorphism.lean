/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement
import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat

/-! # Changing the derived-to-ordinary comparison on a single module

Source: Stacks Project, Tags 06YJ and 08HY; the degree-zero truncation argument
in Step 4 of `lem-pc-affine-alternating-cech-base-change-factorization`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

private theorem rightExact_homology_zero_isIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    {K L : CochainComplex A ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0]
    (s : K ⟶ L) [QuasiIso s] :
    IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map s) 0) := by
  have hK : (K.sc 0).g = 0 := by
    change K.d 0 ((ComplexShape.up ℤ).next 0) = 0
    rw [CochainComplex.next]
    exact (K.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt _ _
  have hL : (L.sc 0).g = 0 := by
    change L.d 0 ((ComplexShape.up ℤ).next 0) = 0
    rw [CochainComplex.next]
    exact (L.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt _ _
  have : F.PreservesLeftHomologyOf (K.sc 0) := F.preservesLeftHomology_of_zero_g _ hK
  have : F.PreservesLeftHomologyOf (L.sc 0) := F.preservesLeftHomology_of_zero_g _ hL
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) 0).map s) F
  have : IsIso (F.map (HomologicalComplex.homologyMap s 0)) := inferInstance
  have hcomp : IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map s) 0 ≫
        ((L.sc 0).mapHomologyIso F).hom) := by
    erw [hn]
    change IsIso (((K.sc 0).mapHomologyIso F).hom ≫
      F.map (HomologicalComplex.homologyMap s 0))
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((L.sc 0).mapHomologyIso F).hom

end AlgebraicGeometry
