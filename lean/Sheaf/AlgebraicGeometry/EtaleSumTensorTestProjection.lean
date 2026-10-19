/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H6
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSumTensorTestComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.EtaleConstantModuleTensor
import Sheaf.Paper.EtaleSumTensorTotalization
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # Acyclic tensor tests for étale sum extension

Source: Stacks Project, More on Étale Cohomology, Tag 0GKF, and the unbounded
totalization expansion of lem-pur-etale-sum-tensor-totalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private def tensorTestRingEquivalence (T : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] :
    EtaleSumTensorTestModule T A ≌ SheafOfModules.{u + 1} (etaleConstantModuleRing T A) := by
  let : (CategoryTheory.Equivalence.refl (C := T.Etale)).functor.IsContinuous
      T.smallEtaleTopology T.smallEtaleTopology := by
    change (𝟭 T.Etale).IsContinuous T.smallEtaleTopology T.smallEtaleTopology
    infer_instance
  let : (CategoryTheory.Equivalence.refl (C := T.Etale)).inverse.IsContinuous
      T.smallEtaleTopology T.smallEtaleTopology := by
    change (𝟭 T.Etale).IsContinuous T.smallEtaleTopology T.smallEtaleTopology
    infer_instance
  let eT := SheafOfModules.pushforwardPushforwardEquivalence.{u + 1}
    (CategoryTheory.Equivalence.refl (C := T.Etale))
    (constantModuleHomRingIso T.smallEtaleTopology A).hom
    (constantModuleHomRingIso T.smallEtaleTopology A).inv (by
      ext W : 2
      dsimp [CategoryTheory.Equivalence.refl, CategoryTheory.Equivalence.counit]
      rw [CategoryTheory.Functor.map_id]
      change 𝟙 _ = ((constantModuleHomRingIso T.smallEtaleTopology A).inv ≫
        (constantModuleHomRingIso T.smallEtaleTopology A).hom).hom.app W
      rw [Iso.inv_hom_id]
      rfl) (by
      ext W : 2
      dsimp [CategoryTheory.Equivalence.refl, CategoryTheory.Equivalence.unit]
      rw [CategoryTheory.Functor.map_id]
      change ((constantModuleHomRingIso T.smallEtaleTopology A).hom ≫
        (constantModuleHomRingIso T.smallEtaleTopology A).inv).hom.app W = 𝟙 _
      rw [Iso.hom_inv_id]
      rfl)
  exact eT

private def tensorTestRestriction (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  (tensorTestRingEquivalence T A).functor ⋙ etaleConstantModuleRestrictionFunctor T A

private def tensorTestRealizationCounit (T : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] :
    tensorTestRestriction T A ⋙ etaleSumTensorTestRealization T A ≅ 𝟭 _ :=
  Functor.isoWhiskerLeft (tensorTestRingEquivalence T A).functor
    (Functor.isoWhiskerRight (etaleConstantModuleCounitIso T A)
      (tensorTestRingEquivalence T A).inverse) ≪≫
    (tensorTestRingEquivalence T A).unitIso.symm

private def tensorTestRestrictionCounit (T : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] :
    etaleSumTensorTestRealization T A ⋙ tensorTestRestriction T A ≅ 𝟭 _ :=
  Functor.isoWhiskerLeft (etaleConstantModuleFunctor T A)
    (Functor.isoWhiskerRight (tensorTestRingEquivalence T A).counitIso
      (etaleConstantModuleRestrictionFunctor T A)) ≪≫
    (etaleConstantModuleUnitIso T A).symm

private instance tensorTestRestriction_isEquivalence (T : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] :
    (tensorTestRestriction T A).IsEquivalence :=
  Functor.IsEquivalence.mk' (etaleSumTensorTestRealization T A)
    (tensorTestRealizationCounit T A).symm (tensorTestRestrictionCounit T A)

private def tensorComparisonCurried {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (E : C ⥤ D)
    (e : E.prod E ⋙ tensor D ≅ tensor C ⋙ E) :
    (Functor.postcompose₂.obj E).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ D).obj E).obj E).obj (curriedTensor D) := by
  refine NatIso.ofComponents (fun M ↦ NatIso.ofComponents
    (fun N ↦ (e.app (M, N)).symm) ?_) ?_
  · intro N N' g
    simpa using e.inv.naturality (X := (M, N)) (Y := (M, N')) (𝟙 M, g)
  · intro M M' f
    ext N
    simpa using e.inv.naturality (X := (M, N)) (Y := (M', N)) (f, 𝟙 N)

private theorem tensorTestTotalRealization (T : Scheme.{u}) (A : Type (u + 1))
    [CommRing A]
    (P Q : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    Nonempty (etaleSumTensorTestTotal T A
      ((etaleSumTensorTestRealizationComplex T A).obj P)
      ((etaleSumTensorTestRealizationComplex T A).obj Q) ≅
      (etaleSumTensorTestRealizationComplex T A).obj
        (CochainComplex.mapBifunctor P Q (curriedTensor _))) := by
  let R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  obtain ⟨e⟩ := etaleConstantModule_tensor_comparison T A
  let E := etaleSumTensorTestRealization T A
  let := etaleSumTensorTestRealization_isEquivalence T A
  let := Functor.additive_of_preserves_binary_products E
  let τ := (tensorComparisonCurried E e).hom
  let : IsIso τ := by dsimp only [τ]; infer_instance
  let c := HomologicalComplex.mapBifunctorComparison τ (.up ℤ) P Q
  exact ⟨(asIso c).symm⟩

/-- The projection comparison for arbitrary tensor tests, before imposing K-flatness.
Source: Stacks Project, More on Étale Cohomology, Tag 0GKF, with the unbounded
sum totalization expansion of lem-pur-etale-sum-tensor-totalization
(blueprint: lem-pur-etale-sum-tensor-test-projection).

Proof: restrict B to constant scalars by the inverse of the canonical realization,
apply the exact inverse image f^*, and realize again, to obtain Q. Equivalences are
exact and f^* is exact, so acyclicity of B implies acyclicity of Q. The constant-scalar
realization commutes with sheafified tensor: on pure tensors its comparison is the
identity; locally every coefficient section is a constant scalar, so balancing over
the constant ring sheaf imposes precisely the sheafified A-balancing relations.
The inverse has the same pure-tensor formula. These comparisons are natural, and
commute with coproducts because realization is an equivalence. Apply the projection
isomorphism in every bidegree (p,q). Sum the components over p+q=n, using preservation
of coproducts by f_!. The two differential summands commute with the components by
naturality, and the sign (-1)^p is preserved by additivity. The signed symmetry
x tensor y ↦ (-1)^(pq) y tensor x puts B, and then Q, first on both sides. Inserting
the realization unit and counit identifies the second factor with the original P.
The inverses of these maps commute with differentials by the same equations and
are inverse on each coproduct summand. Thus they define the asserted complex
isomorphism for every P, without a K-flatness or boundedness assumption. Empty
coproducts and zero coefficients obey the same universal properties. -/
theorem etaleSum_tensor_test_comparison {U X : Scheme.{u}} (f : U ⟶ X)
    [hf : Etale f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (A : Type (u + 1)) [CommRing A]
    (B : CochainComplex (EtaleSumTensorTestModule X A) ℤ) :
    ∀ P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      Nonempty (etaleSumTensorTestTotal X A B
        ((etaleSumTensorTestRealizationComplex X A).obj
          ((etaleSumTensorTestSheafComplexExtension f hf A).obj P)) ≅
        (etaleSumTensorTestComplexExtension f hf A).obj
          (etaleSumTensorTestTotal U A
            ((etaleSumTensorTestInverseImageComplex f A).obj B)
            ((etaleSumTensorTestRealizationComplex U A).obj P)))  := by
  intro P
  let Eₓ := etaleSumTensorTestRealization X A
  let Eᵤ := etaleSumTensorTestRealization U A
  let Dₓ := tensorTestRestriction X A
  let Dᵤ := tensorTestRestriction U A
  let := etaleSumTensorTestRealization_isEquivalence X A
  let := etaleSumTensorTestRealization_isEquivalence U A
  let L := Etale.etaleLowerShriek (ModuleCat.{u + 1} A) f hf
  let R := Etale.upperStar (ModuleCat.{u + 1} A) f
  let := (Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) f hf).isLeftAdjoint
  let Eₓc := Eₓ.mapHomologicalComplex (.up ℤ)
  let Eᵤc := Eᵤ.mapHomologicalComplex (.up ℤ)
  let Dₓc := Dₓ.mapHomologicalComplex (.up ℤ)
  let Dᵤc := Dᵤ.mapHomologicalComplex (.up ℤ)
  let Lc := L.mapHomologicalComplex (.up ℤ)
  let Rc := R.mapHomologicalComplex (.up ℤ)
  let K := Dₓc.obj B
  let V := Rc.obj K
  let eB : Eₓc.obj K ≅ B :=
    (NatIso.mapHomologicalComplex (tensorTestRealizationCounit X A) (.up ℤ)).app B ≪≫
      (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app B
  let 𝓡 := (constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A)
  let := SheafOfModules.isMonoidal_W_independentCoefficients 𝓡
  let := SheafOfModules.monoidalCategory 𝓡
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients 𝓡
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients 𝓡
  let e₁ := (((curriedTensor (EtaleSumTensorTestModule X A)).map₂CochainComplex).flip.obj
    (Eₓc.obj (Lc.obj P))).mapIso eB.symm
  obtain ⟨e₂⟩ := tensorTestTotalRealization X A K (Lc.obj P)
  obtain ⟨Ψ, _, _⟩ := etale_sum_tensor_totalization A f hf
  let e₃ := Eₓc.mapIso (CochainComplex.Monoidal.braiding K (Lc.obj P))
  let e₄ := Eₓc.mapIso (Ψ P K)
  let e₅ := (Lc ⋙ Eₓc).mapIso (CochainComplex.Monoidal.braiding P V)
  obtain ⟨eᵤ⟩ := tensorTestTotalRealization U A V P
  let Z := CochainComplex.mapBifunctor V P (curriedTensor _)
  let eZ : Dᵤc.obj (Eᵤc.obj Z) ≅ Z :=
    (NatIso.mapHomologicalComplex (tensorTestRestrictionCounit U A) (.up ℤ)).app Z ≪≫
      (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app Z
  let e₆ := (Lc ⋙ Eₓc).mapIso ((Dᵤc.mapIso eᵤ ≪≫ eZ).symm)
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅ ≪≫ e₆⟩

end AlgebraicGeometry.Scheme
