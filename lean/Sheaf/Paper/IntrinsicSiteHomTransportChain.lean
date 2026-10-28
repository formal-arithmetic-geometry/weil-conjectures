/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
import all Sheaf.AlgebraicGeometry.IntrinsicRealizationTensorComplex
import all Sheaf.Algebra.Homology.KInjectiveHomComplexOfUniverses
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Chain-level intrinsic Hom transport

Source: Stacks Project, Tags 00YV, 08J7 and 0A95; coefficient-presentation
transport in Step 2 of lem-sf-tensor-exchange-ctf-domains.
(blueprint: lem-sf-intrinsic-site-hom-transport-chain)
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

private noncomputable def transportRightAdjoint
    {C D : Type*} [Category C] [Category D] (E : C ≌ D)
    {T H : C ⥤ C} {S K : D ⥤ D} (a : T ⊣ H) (b : S ⊣ K)
    (e : T ⋙ E.functor ≅ E.functor ⋙ S) :
    H ⋙ E.functor ≅ E.functor ⋙ K := by
  let d : E.inverse ⋙ T ≅ S ⋙ E.inverse :=
    ((Functor.associator E.inverse T E.functor) ≪≫ e.inverseCompIso).isoCompInverse
  exact conjugateIsoEquiv (E.symm.toAdjunction.comp a)
    (b.comp E.symm.toAdjunction) d.symm

-- Tensor compatibility alone suffices here; no monoidal coherence choices are needed.
private noncomputable def transportComplexHom
    {C D : Type*} [Category.{v} C] [Category.{w} D] [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
    [HasLimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    (e : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (L I : CochainComplex C ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.internalHomObj L I) ≅
      CochainComplex.internalHomObj ((F.mapHomologicalComplex (.up ℤ)).obj L)
        ((F.mapHomologicalComplex (.up ℤ)).obj I) := by
  let E := F.asEquivalence.mapHomologicalComplex (.up ℤ)
  let τ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D) :=
    { app := fun X ↦
        { app := fun Y ↦ e.hom.app (X, Y)
          naturality := by
            intro Y Y' g
            simpa using e.hom.naturality (X := (X, Y)) (Y := (X, Y')) (𝟙 X, g) }
      naturality := by
        intro X X' f
        ext Y
        simpa using e.hom.naturality (X := (X, Y)) (Y := (X', Y)) (f, 𝟙 Y) }
  have (X Y : C) : IsIso ((τ.app X).app Y) := (e.app (X, Y)).isIso_hom
  let t : tensorLeft L ⋙ E.functor ≅ E.functor ⋙ tensorLeft (E.functor.obj L) :=
    asIso ((HomologicalComplex.mapBifunctorComparisonNatTrans τ (.up ℤ)).app L)
  exact (transportRightAdjoint E (CochainComplex.tensorHomAdjunction L)
    (CochainComplex.tensorHomAdjunction (E.functor.obj L)) t).app I

namespace AlgebraicGeometry.ProEtale

private noncomputable def fixedHomRepresentative
    (X : Scheme.{u}) (A : Type u) [CommRing A]
    (L I : CochainComplex
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ)
    [I.IsKInjective] :
    (((derivedHom (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).obj
      (op (DerivedCategory.Q.obj L))).obj (DerivedCategory.Q.obj I)) ≅
      DerivedCategory.Q.obj (CochainComplex.internalHomObj L I) := by
  let C := Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
  letI : HasColimitsOfSize.{0, 0} C := fixedSheafCountableColimits A X
  letI (V W : GradedObject ℤ C) : V.HasTensor W :=
    fun _ ↦ @HasColimitsOfShape.has_colimit _ _ _ _
      (@HasColimitsOfSize.has_colimits_of_shape _ _
        (fixedSheafCountableColimits A X) _ _) _
  letI (V W Y Z : GradedObject ℤ C) : GradedObject.HasTensor₄ObjExt V W Y Z :=
    inferInstance
  letI (V W Y : GradedObject ℤ C) : GradedObject.HasGoodTensor₁₂Tensor V W Y :=
    inferInstance
  letI (V W Y : GradedObject ℤ C) : GradedObject.HasGoodTensorTensor₂₃ V W Y :=
    inferInstance
  letI : IsGrothendieckAbelian.{u + 1} C :=
    GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology _ X
  letI : HasColimitsOfShape ℤ C := inferInstance
  letI : HasExactColimitsOfShape ℤ C := hasExactColimitsOfShape_int C
  letI (M : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).obj M) := inferInstance
  letI (M : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj M) := inferInstance
  letI : Abelian.HasFunctorialFlatResolution C :=
    hasFunctorialFlatResolution_sheaf (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X
  letI (j : ℤ) : HasColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (.up ℤ) (.up ℤ) ⁻¹' {j})) C :=
    @HasColimitsOfSize.has_colimits_of_shape _ _ (fixedSheafCountableColimits A X) _ _
  let Λ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ C) := Classical.arbitrary _
  letI : (HomotopyCategory.quasiIso C (.up ℤ)).localizerMorphismKFlat
      |>.IsLeftDerivabilityStructure :=
    Λ.reduced.homotopyCategory_kFlat_isLeftDerivabilityStructure
      ObjectProperty.flat.essImage_ι_le
  let P := (HomotopyCategory.quotient C (.up ℤ)).obj L
  let e : DerivedCategory.Qh.obj P ≅ DerivedCategory.Q.obj L :=
    (DerivedCategory.quotientCompQhIso C).app L
  let a := (DerivedCategory.tensorHomAdjunctionQhObj P).ofNatIsoLeft
    ((tensoringLeft _).mapIso e)
  let d := Adjunction.rightAdjointUniq (derivedTensorHomAdjunction _ _) a
  have : IsIso ((DerivedCategory.internalHomQhObjUnit P).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj I)) := by
    infer_instance
  exact d.app (DerivedCategory.Q.obj I) ≪≫
    (DerivedCategory.internalHomQhObj P).mapIso
      ((DerivedCategory.quotientCompQhIso C).app I).symm ≪≫
    (asIso ((DerivedCategory.internalHomQhObjUnit P).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj I))).symm ≪≫
    DerivedCategory.Qh.mapIso ((HomotopyCategory.quotientCompInternalHomIso P).app I) ≪≫
    (DerivedCategory.quotientCompQhIso C).app (CochainComplex.internalHomObj L I)


/-- The realized fixed-coefficient derived Hom is represented by the intrinsic
Hom complex on the chosen K-injective representatives.

Source: Stacks Project, Tags 00YV, 08J7 and 0A95; coefficient-presentation
transport in Step 2 of lem-sf-tensor-exchange-ctf-domains.

Proof: apply the exact associated-module-sheaf realization termwise to the
fixed-coefficient Hom complex. The sheaf-Hom/tensor adjunction identifies each
term and its signed differential with the intrinsic constant-ring Hom complex;
exactness of the realization then carries the localized representative to the
localized intrinsic complex.
(blueprint: lem-sf-intrinsic-site-hom-transport-chain) -/
theorem intrinsicSiteHom_transport_chain (X : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (Lc Ic : CochainComplex
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ)
    [Ic.IsKInjective] :
    Nonempty
      ((finiteCoefficientIntrinsicRealization X A).mapDerivedCategory.obj
          (((derivedHom (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).obj
            (op (DerivedCategory.Q.obj Lc))).obj (DerivedCategory.Q.obj Ic)) ≅
        DerivedCategory.Q.obj
          (homComplex.{u + 1, u, u + 1, u + 1}
            (R := proEtaleConstantRing X A)
            (((finiteCoefficientIntrinsicRealization X A).mapHomologicalComplex
              (.up ℤ)).obj Lc)
            (((finiteCoefficientIntrinsicRealization X A).mapHomologicalComplex
              (.up ℤ)).obj Ic))) := by
  let C := Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
  let R := proEtaleConstantRing X A
  let D := proEtaleRingModules X R
  let F := finiteCoefficientIntrinsicRealization X A
  let : F.IsEquivalence := (finiteCoefficientIntrinsicRealization_exact X A).1
  let : MonoidalCategory D := SheafOfModules.monoidalCategory R
  let : SymmetricCategory D := SheafOfModules.symmetricCategory R
  let : MonoidalClosed D :=
    WeilConjectures.ZeroClassAux.moduleMonoidalClosed.{u + 1, u + 1, u} R
  let : HasLimitsOfSize.{0, 0} C := hasLimitsOfSizeShrink.{0, 0, u + 1, u + 1} C
  let : HasColimitsOfSize.{0, 0} C := fixedSheafCountableColimits A X
  let : HasLimitsOfSize.{0, 0} D := hasLimitsOfSizeShrink.{0, 0, u + 1, u + 1} D
  let : HasColimitsOfSize.{0, 0} D := hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} D
  obtain ⟨t⟩ := intrinsicTensorNatIso X A
  let c := transportComplexHom F t Lc Ic
  let h := WeilConjectures.ZeroClassAux.homComplexIsoInternalHomObj.{u + 1, u + 1, u}
    (R := R) ((F.mapHomologicalComplex (.up ℤ)).obj Lc)
      ((F.mapHomologicalComplex (.up ℤ)).obj Ic)
  exact ⟨F.mapDerivedCategory.mapIso (fixedHomRepresentative X A Lc Ic) ≪≫
    F.mapDerivedCategoryFactors.app (CochainComplex.internalHomObj Lc Ic) ≪≫
    DerivedCategory.Q.mapIso (c ≪≫ h.symm)⟩

end AlgebraicGeometry.ProEtale
