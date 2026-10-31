/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorReductionData
import WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars

/-! # K-flat invertibility of the actual scalar adjunction representative -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w uA vA uB vB wA wB
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] Functor.leftAdjoint Adjunction.ofIsRightAdjoint
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit

private theorem cochainAdjunction_unit
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (E : A ⥤ B) (U : B ⥤ A) [E.Additive] [U.Additive] (adj : E ⊣ U)
    (C : CochainComplex A ℤ) :
    (adj.mapHomologicalComplex (.up ℤ)).unit.app C =
      (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app C ≫
        (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app C ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app C := by
  ext i : 1
  simp only [Functor.id_obj, Functor.comp_obj, Adjunction.mapHomologicalComplex_unit_app_f,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplexIdIso_inv_app_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Iso.refl_inv, NatTrans.id_app]
  exact ((Category.id_comp (adj.unit.app (C.X i) ≫ 𝟙 ((E ⋙ U).obj (C.X i)))).trans
    (Category.comp_id (adj.unit.app (C.X i)))).symm

private theorem normalizedTranspose_isIso
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
    [Abelian.HasFunctorialFlatResolution A] [HasExactColimitsOfShape ℤ A]
    [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (E : A ⥤ B) (U : B ⥤ A) [E.Additive] [U.Additive] [E.PreservesKFlatQuasiIso]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (adj : E ⊣ U) {L : _root_.DerivedCategory A ⥤ _root_.DerivedCategory B}
    (ad : L ⊣ U.mapDerivedCategory) (X : CochainComplex A ℤ)
    (hX : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat X) :
    IsIso ((ad.homEquiv _ _).symm
      (_root_.DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app X ≫
            (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app X ≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app X) ≫
        U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj X))) := by
  have hi := Adjunction.isIso_cochainTranspose_of_kFlat E U adj ad X hX
  rw [cochainAdjunction_unit E U adj X] at hi
  exact hi

/-- The actual fixed-adjoint scalar representative is invertible on K-flat complexes.
Source: thm-pur-finite-reduction-of-purity, proof Step 2; Stacks 07A4 and 0FPT.
(blueprint: lem-pur-finite-scalar-representative-invertible).
Proof: scalar extension preserves K-flat quasi-isomorphisms. Scalar restriction is
exact, preserving finite limits by the scalar adjunction and finite colimits by
the restriction/coextension adjunction. Its derived-adjunction transpose on a
K-flat complex is therefore invertible. The mapped ordinary unit and the cochain
adjunction unit agree in every degree; substitute this identity into the proved
exact-right-derived-adjoint comparison. -/
theorem finiteScalarRepresentative_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (C : CochainComplex (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ)
    (hC : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C) :
    IsIso (ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative φ T C) := by
  let _ := φ.toAlgebra
  let E := ProEtale.sheafExtendScalars φ T
  let U := Sheaf.restrictScalars (ProEt.topology T) φ
  have : E.PreservesKFlatQuasiIso :=
    ProEtale.preservesKFlatQuasiIso_sheafExtendScalars A B T
  have : PreservesFiniteLimits U := by
    let _ := (ProEtale.sheafExtendScalarsAdjunction φ T).rightAdjoint_preservesLimits
    infer_instance
  have : PreservesFiniteColimits U := by
    let _ := (Sheaf.restrictCoextendScalarsAdj (ProEt.topology T) φ).leftAdjoint_preservesColimits
    infer_instance
  let adj := ProEtale.sheafExtendScalarsAdjunction φ T
  have : HasExactColimitsOfShape ℤ
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) :=
    HasExactColimitsOfShape.of_domain_equivalence _ (AsSmall.equiv (C := ℤ)).symm
  exact normalizedTranspose_isIso E U adj
    (Adjunction.ofIsRightAdjoint
      (ProEtale.SupportedEtaleTensorOrigin.proFixedRestriction φ T)) C hC

end WeilConjectures.PurityFiniteSetting
