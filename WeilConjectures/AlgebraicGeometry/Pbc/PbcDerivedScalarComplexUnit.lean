/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalPullComputation
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Derived scalar extension and restriction on complexes

The unit of the derived scalar extension–restriction adjunction is computed on every cochain
complex by the ordinary unit, read through the universal counit. The derived restriction
compositors are computed on complexes by the ordinary ones.

## Main statements

* `AlgebraicGeometry.Scheme.pbcDerivedScalarAdjunction_unit_app_Q`: the derived unit on the
  localization of a complex.
* `AlgebraicGeometry.Scheme.pbcDerivedRestrictComp_hom_app_Q`: the derived restriction compositor
  on the localization of a complex.

## Implementation details

The normalization of `pbcDerivedScalarAdjunction` only records the unit on K-flat complexes. A
K-flat resolution and the naturality of the unit, of the counit and of the localization
comparisons extend it to every complex.

## References

* Stacks Project, Tags 06YY and 03DA
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The derived unit of scalar extension along `φ`, on the localization of any complex, is the
ordinary unit read through the universal counit. -/
theorem pbcDerivedScalarAdjunction_unit_app_Q {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (P : CochainComplex (pbcModules X R) ℤ) :
    (pbcDerivedScalarAdjunction φ).unit.app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedRestrict φ).map (pbcComplexCounit φ P) ≫
        (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
          (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app P) := by
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  obtain ⟨P', s, hP', -, hs, -⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
  have : IsIso (DerivedCategory.Q.map s) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).2 hs
  rw [← cancel_epi (DerivedCategory.Q.map s)]
  have h1 := (pbcDerivedScalarAdjunction φ).unit.naturality (DerivedCategory.Q.map s)
  have h2 := pbcComplexCounit_naturality φ s
  have h3 := (pbcRestrict φ).mapDerivedCategoryFactors.hom.naturality
    (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).map s)
  have h4 := (pbcDerivedScalarAdjunction_exists φ).exists.choose_spec P' hP'
  have h5 := (NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).naturality s
  dsimp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at h1 h3 h5
  have h2' := congrArg (pbcDerivedRestrict φ).map h2
  simp only [Functor.map_comp] at h2'
  rw [reassoc_of% h1]
  erw [reassoc_of% h2']
  erw [h3]
  rw [← Category.assoc, ← Category.assoc]
  erw [Category.assoc _ _ ((pbcRestrict φ).mapDerivedCategoryFactors.hom.app _), h4]
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  congr 1
  exact h5.symm

/-- The derived compositor of scalar restrictions, on the localization of a complex, is the
ordinary compositor read through the localization comparisons. -/
theorem pbcDerivedRestrictComp_hom_app_Q {R S B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ) (N : CochainComplex (pbcModules X B) ℤ) :
    (pbcDerivedRestrictComp φ ψ χ h).hom.app (DerivedCategory.Q.obj N) ≫
        (pbcRestrict χ).mapDerivedCategoryFactors.hom.app N =
      (pbcDerivedRestrict φ).map ((pbcRestrict ψ).mapDerivedCategoryFactors.hom.app N) ≫
        (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
          (((pbcRestrict ψ).mapHomologicalComplex (.up ℤ)).obj N) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (pbcRestrictComp φ ψ χ h).hom (.up ℤ)).app N) := by
  have hi := Functor.mapDerivedCategoryCompIso_hom_app_factors (pbcRestrict ψ) (pbcRestrict φ) N
  simp only [pbcDerivedRestrictComp, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_fac, ← hi, Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [Category.assoc]
  rfl

end AlgebraicGeometry.Scheme
