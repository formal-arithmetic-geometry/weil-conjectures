/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.Paper.IntegralReductionTensor
public import Sheaf.Paper.IntegralResiduePullSquare
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic

/-! # The canonical restricted residue tensor presentation

Source: Bhatt--Scholze, Lemma 6.5.9(3), and derived scalar extension.
(blueprint: new-integral-residue-tensor-presentation)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

instance genericTensorLeft_preservesKFlatQuasiIso (B : C) :
    (tensorLeft B).PreservesKFlatQuasiIso := by
  refine Functor.PreservesKFlatQuasiIso.mk' _ ?_
  intro K hK hKa
  exact (CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa B).of_iso
    ((NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight B) _).app K).symm

@[irreducible] noncomputable def homotopyTensorSingleIso (B : C) :
    tensorLeft ((HomotopyCategory.quotient C (.up ℤ)).obj
      ((HomologicalComplex.single C (.up ℤ) 0).obj B)) ≅
        (tensorLeft B).mapHomotopyCategory (.up ℤ) := by
  let q := HomotopyCategory.quotient C (.up ℤ)
  let P := (HomologicalComplex.single C (.up ℤ) 0).obj B
  let e : tensorLeft P ≅ (tensorLeft B).mapHomologicalComplex (.up ℤ) :=
    CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor C) B
  let pre : q ⋙ tensorLeft (q.obj P) ≅
      q ⋙ (tensorLeft B).mapHomotopyCategory (.up ℤ) :=
    (Functor.Monoidal.commTensorLeft q P).symm ≪≫
      Functor.isoWhiskerRight e q ≪≫ (tensorLeft B).mapHomotopyCategoryFactors (.up ℤ)
  exact (Functor.FullyFaithful.ofFullyFaithful
    ((Functor.whiskeringLeft _ _ _).obj q)).preimageIso pre

@[irreducible] noncomputable def derivedTensorSingleIso (B : C) :
    (tensorLeft B).leftDerivedFunctor ≅
      tensorLeft ((DerivedCategory.singleFunctor C 0).obj B) := by
  let P := (HomotopyCategory.quotient C (.up ℤ)).obj
    ((HomologicalComplex.single C (.up ℤ) 0).obj B)
  let eB : (DerivedCategory.singleFunctor C 0).obj B ≅ DerivedCategory.Qh.obj P :=
    (DerivedCategory.singleFunctorIsoCompQ C 0).app B ≪≫
      (DerivedCategory.quotientCompQhIso C).symm.app _
  exact Functor.leftDerivedNatIso (tensorLeft B).leftDerivedFunctor
      (tensorLeft (DerivedCategory.Qh.obj P)) (tensorLeft B).leftDerivedFunctorCounit
      (DerivedCategory.tensorLeftQhObjCounit P) (HomotopyCategory.quasiIso C (.up ℤ))
      (Functor.isoWhiskerRight (homotopyTensorSingleIso B).symm DerivedCategory.Qh) ≪≫
    (curriedTensor (DerivedCategory C)).mapIso eB.symm

@[irreducible] noncomputable def derivedTensorPresentationIso (B : C)
    (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [H.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))] :
    H ≅ tensorRight ((DerivedCategory.singleFunctor C 0).obj B) := by
  let : BraidedCategory (DerivedCategory C) := DerivedMonoidal.braidedCategory
    (DerivedCategory.Qh (C := C)) (HomotopyCategory.quasiIso C (.up ℤ))
  exact Functor.leftDerivedUnique (tensorLeft B).leftDerivedFunctor H ε
      (tensorLeft B).leftDerivedFunctorCounit (HomotopyCategory.quasiIso C (.up ℤ)) ≪≫
    derivedTensorSingleIso B ≪≫ BraidedCategory.tensorLeftIsoTensorRight _

end CategoryTheory

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]

/-- Restricted derived scalar extension is right tensor with the degree-zero
restricted regular module, using the canonical balanced tensor counit. -/
@[irreducible] noncomputable def residueDerivedTensorIso :
    (extendScalars φ).leftDerivedFunctor ⋙ (comap φ).mapDerivedCategory ≅
      MonoidalCategory.tensorRight ((DerivedCategory.singleFunctor (Mod C R) 0).obj
        ((comap φ).obj (regular S))) := by
  letI := Mod.tensorPresentationDerivedCounit_isLeftDerivedFunctor φ
  exact CategoryTheory.derivedTensorPresentationIso _ _ (Mod.tensorPresentationDerivedCounit φ)

end CategoryTheory.Mod

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The canonical tensor presentation of restricted derived coefficient reduction.
The data are obtained from the canonical balanced-tensor left-derived presentation
of integral reduction, followed by derived symmetry; no duplicate tensor-linearity
lemma is introduced here.
-/
@[irreducible] noncomputable def residueExchangeTensorIso (T : Scheme.{u}) :
    residueExchangeReduction ℓ E T ⋙ residueExchangeRestriction ℓ E T ≅
      tensorRight (residueExchangeCoefficient ℓ E T) := by
  unfold residueExchangeReduction integralReduction residueExchangeRestriction
  exact Mod.residueDerivedTensorIso (coefficientMap (integralReductionMap ℓ E) T)

end AlgebraicGeometry.ProEtale.CondensedRing
