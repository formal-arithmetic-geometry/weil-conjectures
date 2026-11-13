/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.MixedRepForward.MixedRepresentationGeneral
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.MixedRepForward.ForwardTransportGeneral
import WeilConjectures.CategoryTheory.FiniteOpenMixedTensorRepresentativeCounit

/-!
# Counit and cochain representative equations for the published mixed open tensor comparison

The statement is given for an arbitrary coefficient category; the finite coefficient
case `Mod_A` is obtained by instantiation.

## References

* Stacks Project, Tag 07A4
-/

@[expose] public section
set_option autoImplicit false

universe u' u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open AlgebraicGeometry Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [ProEtale.UpperStarPreservesFlat A]
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- For an open immersion `j : U ⟶ X` and a coefficient category `A`, the left-derived
counit of `j^*` on pro-étale `A`-valued sheaves is compatible with the comparison `κ`, and the
left-derived tensor comparison `φ` is compatible with the counit and the tensorators of the
cochain localizations. No boundedness, flatness or K-flatness is assumed on `P, Q`.
(Stacks, Tag 07A4) -/
theorem finiteOpenMixedTensorRepresentative
    (P Q : CochainComplex (Sheaf (Scheme.ProEt.topology X) A) ℤ) :
    L((j)^*[A]).map
        ((DerivedCategory.quotientCompQhIso (Sheaf (Scheme.ProEt.topology X) A)).inv.app P) ≫
      (j)^*[A].leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map
        (((j)^*[A].mapHomotopyCategoryFactors (.up ℤ)).inv.app P) ≫
      (DerivedCategory.quotientCompQhIso (Sheaf (Scheme.ProEt.topology U) A)).hom.app
        (((j)^*[A].mapHomologicalComplex (.up ℤ)).obj P) =
      (j)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app
        ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj P) ≫
        (j)^*[A].mapDerivedCategoryFactors.hom.app P ∧
    ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorNatIso
      A j).hom.app
      ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj P)).app
      ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj Q) ≫
      ((j)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app
        ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj P) ≫
        (j)^*[A].mapDerivedCategoryFactors.hom.app P ⊗ₘ
       (j)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app
        ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj Q) ≫
        (j)^*[A].mapDerivedCategoryFactors.hom.app Q) ≫
      (Functor.LaxMonoidal.μ (DerivedCategory.Q
        (C := Sheaf (Scheme.ProEt.topology U) A))
        (((j)^*[A].mapHomologicalComplex (.up ℤ)).obj P)
        (((j)^*[A].mapHomologicalComplex (.up ℤ)).obj Q)) =
      L((j)^*[A]).map
        (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)) P Q) ≫
      ((j)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app
        ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj
          (HomologicalComplex.mapBifunctor P Q
            (curriedTensor (Sheaf (Scheme.ProEt.topology X) A)) (.up ℤ))) ≫
        (j)^*[A].mapDerivedCategoryFactors.hom.app
          (HomologicalComplex.mapBifunctor P Q
            (curriedTensor (Sheaf (Scheme.ProEt.topology X) A)) (.up ℤ))) ≫
      (DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology U) A)).map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
          (j)^*[A]).app P).app Q) ∧
    (((j)^*[A].leftDerivedFunctorIsoMapDerivedCategory.inv.app
        ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj P)) ⊗ₘ 𝟙 _) ≫
      ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorNatIso
        A j).inv.app
        ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj P)).app
        ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj Q) ≫
      (j)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app
        (((-⊗ᴸ-(X)[A]).obj
          ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj P)).obj
          ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj Q)) ≫
      (j)^*[A].mapDerivedCategory.map
        (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)) P Q) ≫
      (j)^*[A].mapDerivedCategoryFactors.hom.app
        (HomologicalComplex.mapBifunctor P Q
          (curriedTensor (Sheaf (Scheme.ProEt.topology X) A)) (.up ℤ)) =
      ((j)^*[A].mapDerivedCategoryFactors.hom.app P ⊗ₘ
        ((j)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app
          ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj Q) ≫
          (j)^*[A].mapDerivedCategoryFactors.hom.app Q)) ≫
      (Functor.LaxMonoidal.μ (DerivedCategory.Q
        (C := Sheaf (Scheme.ProEt.topology U) A))
        (((j)^*[A].mapHomologicalComplex (.up ℤ)).obj P)
        (((j)^*[A].mapHomologicalComplex (.up ℤ)).obj Q)) ≫
      inv ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology U) A)).map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
          (j)^*[A]).app P).app Q)) := by
  refine ⟨?_, MixedRepForward.forward_transport_general A j P Q,
    MixedRepForward.mixed_inverse_transport_general A j P Q⟩
  have h := CategoryTheory.Functor.leftDerivedFactors_eq_counit ((j)^*[A]) P
  rw [h]
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
    CategoryTheory.Functor.mapHomotopyCategoryFactors]
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
  simp only [cast_eq]

end AlgebraicGeometry.ProEtale
