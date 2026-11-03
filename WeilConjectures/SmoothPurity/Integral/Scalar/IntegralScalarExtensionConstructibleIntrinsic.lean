/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension

import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import Mathlib.Algebra.Field.ULift
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
public import WeilConjectures.SmoothPurity.Integral.IntegralConstructibleLinear
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarFiniteLevelBounds
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTowerEffectivity
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison

/-!
# Integral scalar extension preserves intrinsic bounded constructibility

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace WeilConjectures

private theorem ordinaryScalarModelIso_transport
    (M : integralTowerModules l E Y) (U : Y.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
    (x : M.val.obj U) :
    ((ordinaryScalarModelIso l E L ι Y).hom.app M).val.app U
      ((eqToHom ((integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose M).symm).val.app U
        ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
            (integralCompletedScalarMap l E L ι Y) M).presheaf).app U
              (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
                ((integralCompletedScalarMap l E L ι Y).hom.app U).hom] x))) =
      completedScalarTensorSection l E L ι Y M U s x := by
  rw [ordinaryScalarModelIso_hom_app]
  exact tensorPresentation_transport Y _ _ (scalarMap_eq_completed l E L ι Y)
    M _ _ ((integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose M)
    ((completedScalarChangeData l E L ι Y).choose_spec.choose M) U s x

private theorem archived_initial_of_full_essSurj
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) [F.Full] [F.EssSurj] :
    F.Initial := by
  classical
  constructor
  intro Y
  let e := F.objObjPreimageIso Y
  let Z : CostructuredArrow F Y := CostructuredArrow.mk e.hom
  have lift (X : CostructuredArrow F Y) : Nonempty (X ⟶ Z) := by
    refine ⟨CostructuredArrow.homMk (F.preimage (X.hom ≫ e.inv)) ?_⟩
    simp [Z, e]
  let : Nonempty (CostructuredArrow F Y) := ⟨Z⟩
  apply zigzag_isConnected
  intro X X'
  exact (Zigzag.of_hom (lift X).some).trans (Zigzag.of_inv (lift X').some)

-- The induced functor on structured arrows is also full and essentially
-- surjective, so restricting the defining limit cone preserves its limit.

private noncomputable def archived_pointwise_precomp_full
    {A C D H : Type*} [Category A] [Category C] [Category D] [Category H]
    (P : A ⥤ C) [P.Full] [P.EssSurj] (Q : C ⥤ D) (F : C ⥤ H) (L : D ⥤ H)
    (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      ((Functor.associator P Q L).hom ≫ Functor.whiskerLeft P α)).IsPointwiseRightKanExtension := by
  intro Y
  let p := StructuredArrow.pre Y P Q
  let : p.Initial := archived_initial_of_full_essSurj p
  apply Limits.IsLimit.ofIsoLimit ((Functor.Initial.isLimitWhiskerEquiv p _).symm (h Y))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, p]
  simp
  rfl

-- Transport the defining limit cone through an equivalence of structured
-- arrow categories and the prescribed isomorphism of diagram functors.

private noncomputable def archived_pointwise_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {F F' : C ⥤ H} (L : D ⥤ H)
    (i : Q ≅ Q') (j : F ≅ F') (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      (Functor.whiskerRight i.inv L ≫ α ≫ j.hom)).IsPointwiseRightKanExtension := by
  intro Y
  let Φ : StructuredArrow Y Q' ≌ StructuredArrow Y Q := Comma.mapRightIso _ i.symm
  let k : Φ.functor ⋙ StructuredArrow.proj Y Q ⋙ F ≅
      StructuredArrow.proj Y Q' ⋙ F' :=
    NatIso.ofComponents (fun X ↦ j.app X.right) (by
      intro X X' f
      exact j.hom.naturality f.right)
  apply Limits.IsLimit.ofIsoLimit
    ((Limits.IsLimit.postcomposeHomEquiv k _).symm ((h Y).whiskerEquivalence Φ))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, Φ, k]
  simp [Category.assoc]
  rfl

private theorem archived_homotopyCounit_naturality
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] (LF : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    {P Q : CochainComplex A ℤ} (f : P ⟶ Q) :
    LF.map (DerivedCategory.Q.map f) ≫
        ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj Q) =
      ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  exact ε.naturality ((HomotopyCategory.quotient A (.up ℤ)).map f)

private def archived_homotopyCounitOnComplex
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] (LF : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ LF ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app P := ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P)
  naturality _ _ f := archived_homotopyCounit_naturality F LF ε f

private noncomputable def archived_homotopyCounitOnComplex_pointwise
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] (LF : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [(F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (.up ℤ))]
    [LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ))] :
    (Functor.RightExtension.mk LF
      (archived_homotopyCounitOnComplex F LF ε)).IsPointwiseRightKanExtension := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  let H := F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let α := (Functor.associator q DerivedCategory.Qh LF).hom ≫ Functor.whiskerLeft q ε
  have hα := archived_pointwise_precomp_full q DerivedCategory.Qh H LF ε
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor LF ε
      (HomotopyCategory.quasiIso A (.up ℤ)))
  let i := DerivedCategory.quotientCompQhIso A
  let j : q ⋙ H ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let β : DerivedCategory.Q ⋙ LF ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight i.inv LF ≫ α ≫ j.hom
  have hb : β = archived_homotopyCounitOnComplex F LF ε := by
    ext P
    dsimp [β, i, α, j, archived_homotopyCounitOnComplex]
    simp only [Category.id_comp, Category.assoc]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    erw [Category.id_comp, Category.comp_id, Category.comp_id]
    exact Category.id_comp _
  rw [← hb]
  exact archived_pointwise_change_iso LF i j α hα

private noncomputable def archived_modelOfHomotopyData
    {C : Type a} [Category.{b} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S)
    [HasDerivedCategory (ringedSiteModules.{u}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory (ringedSiteModules.{u}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
    (F : ringedSiteModules.{u} (SheafOfModules.derivedChangeRingIndependentCoefficients J R) ⥤
      ringedSiteModules.{u} (SheafOfModules.derivedChangeRingIndependentCoefficients J S))
    [F.Additive]
    (hobj : ∀ M, F.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (hobj N).symm)
    (hpres : ∀ {P Q : CochainComplex
      (ringedSiteModules.{u} (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ}
      (f : P ⟶ Q), CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        CochainComplex.IsKFlatIndependentCoefficients (R := R) Q → QuasiIso f →
          QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f))
    (LF : DerivedCategory
      (ringedSiteModules.{u} (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ⥤
      DerivedCategory
        (ringedSiteModules.{u} (SheafOfModules.derivedChangeRingIndependentCoefficients J S)))
    (ε : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hpw : (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso _ (.up ℤ)))
    (huniv : LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)))
    (htri : ∃ (_ : LF.CommShift ℤ), LF.IsTriangulated)
    (hcomp : ∀ P : CochainComplex
      (ringedSiteModules.{u} (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) :
    SheafOfModules.DerivedChangeOfRingsCochainModel φ := by
  letI := hpw
  letI := huniv
  have hβ := archived_homotopyCounitOnComplex_pointwise F LF ε
  refine
    { E := F
      obj_eq := hobj
      map_eq := hmap
      preserves := hpres
      T := LF
      pointwise := ?_
      ε := archived_homotopyCounitOnComplex F LF ε
      universal := ⟨hβ.isRightKanExtension⟩
      triangulated := htri
      computes := hcomp }
  intro X
  exact (Functor.hasPointwiseLeftDerivedFunctorAt_iff
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ)) X).2
    ((hβ (DerivedCategory.Q.obj X)).hasPointwiseRightKanExtensionAt)

private noncomputable def archived_modelOfChosenHomotopyData
    {C : Type a} [Category.{b} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S)
    [HasDerivedCategory (ringedSiteModules.{u}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory (ringedSiteModules.{u}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
    := by
  let h := SheafOfModules.derivedChangeOfRingsIndependentCoefficients φ
  exact @archived_modelOfHomotopyData C inferInstance inferInstance J inferInstance
    inferInstance inferInstance R S φ inferInstance inferInstance
    h.choose h.choose_spec.choose_spec.choose_spec.choose
    h.choose_spec.choose h.choose_spec.choose_spec.choose
    h.choose_spec.choose_spec.choose_spec.choose_spec.1
    h.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose
    h.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose
    h.choose_spec.choose_spec.choose_spec.choose_spec.2.1
    h.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose_spec.1
    h.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose_spec.2.1
    h.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose_spec.2.2

private noncomputable def archivedCompletedScalarCochainModel :=
  @archived_modelOfChosenHomotopyData
    Y.ProEt inferInstance (essentiallySmallSelf.{u} _)
    (AlgebraicGeometry.Scheme.ProEt.topology Y) inferInstance
    (integralCoefficientAbLocallyBijective.{u, u} Y)
    (integralCoefficientAbSheafify.{u, u} Y)
    (completedIntegralCommRingSheafUnrestricted l E Y)
    (completedIntegralCommRingSheafUnrestricted l L Y)
    (completedCoefficientMap l E L ι Y)
    (integralTowerHasDerivedCategory l E Y) (integralTowerHasDerivedCategory l L Y)

private theorem archivedCompletedScalarCochainModel_counit
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (archivedCompletedScalarCochainModel l E L ι Y).ε.app P =
      completedScalarCounit l E L ι Y P := by
  rfl

private theorem integralScalarCompletionChain_model_spec :
    let e := NatIso.mapHomologicalComplex (ordinaryScalarModelIso l E L ι Y) (.up ℤ);
    let b := e.hom ≫ completedScalarChainComparison l E L ι Y;
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (n : ℕ)
        (U : Y.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
        (x : (P.X i).val.obj U),
        (((b.app P ≫ CochainComplex.mappingCocone.fst
          (integralScalarRoosBoundary l E L ι Y P) ≫
          Pi.π (fun n ↦ (integralScalarLevel l E L ι Y n).obj P) n).f i).val.app U)
            ((eqToHom ((integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose
              (P.X i)).symm).val.app U
              ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
                (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
                  (integralCompletedScalarMap l E L ι Y) (P.X i)).presheaf).app U
                (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
                  ((integralCompletedScalarMap l E L ι Y).hom.app U).hom] x))) =
          integralScalarTensorSection l E L ι Y n (P.X i) U
            ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app U s) x) ∧
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i j : ℤ)
        (h : i + -1 = j),
        (b.app P).f i ≫ (CochainComplex.mappingCocone.snd
          (integralScalarRoosBoundary l E L ι Y P)).v i j h = 0) := by
  let e := NatIso.mapHomologicalComplex (ordinaryScalarModelIso l E L ι Y) (.up ℤ)
  let b := e.hom ≫ completedScalarChainComparison l E L ι Y
  change _ ∧ _
  constructor
  · intro P i n U s x
    dsimp only [NatTrans.comp_app, HomologicalComplex.comp_f,
      NatTrans.mapHomologicalComplex_app_f]
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
    change (((completedScalarChainComparison l E L ι Y).app P).f i ≫
      (CochainComplex.mappingCocone.fst
        (completedScalarRoosEndomorphism l E L ι Y P)).f i ≫
      (Pi.π (fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n)) n).f i
      ).val.app U
        (((ordinaryScalarModelIso l E L ι Y).hom.app (P.X i)).val.app U
          ((eqToHom ((integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose
            (P.X i)).symm).val.app U
            ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
              (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
                (integralCompletedScalarMap l E L ι Y) (P.X i)).presheaf).app U
                  (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
                    ((integralCompletedScalarMap l E L ι Y).hom.app U).hom] x)))) = _
    exact (congrArg (fun z ↦
      (((completedScalarChainComparison l E L ι Y).app P).f i ≫
        (CochainComplex.mappingCocone.fst
          (completedScalarRoosEndomorphism l E L ι Y P)).f i ≫
        (Pi.π (fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n)) n).f i
        ).val.app U z) (ordinaryScalarModelIso_transport l E L ι Y (P.X i) U s x)).trans
      (by
        simpa only [completedScalarChainComparison] using
          (completedScalarChainComparison_existsUnique l E L ι Y).exists.choose_spec.1
            P i n U s x)
  · intro P i j hij
    have hj : j = i - 1 := by omega
    subst j
    change (e.hom.app P).f i ≫
      (((completedScalarChainComparison l E L ι Y).app P).f i ≫
        (CochainComplex.mappingCocone.snd
          (completedScalarRoosEndomorphism l E L ι Y P)).v i (i - 1) (by omega)) = 0
    have h : ((completedScalarChainComparison l E L ι Y).app P).f i ≫
        (CochainComplex.mappingCocone.snd
          (completedScalarRoosEndomorphism l E L ι Y P)).v i (i - 1) (by omega) = 0 := by
      simpa only [completedScalarChainComparison] using
        (completedScalarChainComparison_existsUnique l E L ι Y).exists.choose_spec.2 P i
    dsimp only [completedOrdinaryScalarComplex] at h ⊢
    exact (congrArg ((e.hom.app P).f i ≫ ·) h).trans
      (Preadditive.leftComp _ ((e.hom.app P).f i)).map_zero

-- Public statement elaboration needs the fixed coefficient-universe instance.
-- The generic instance imported by the condensed route leaves a smallness level open.

/-- The unique scalar-completion transformation with the specified counit square,
isomorphic on every derived-complete input.
Source: Bhatt--Scholze, Proposition 3.5.1 and Lemma 6.8.2(1)
(blueprint: lem-weil-normalized-scalar-completion).
Proof: identify the two ordinary sheafified scalar models by their completed coefficient
maps and lift this isomorphism to complexes. The universal left-derived comparison gives
a natural isomorphism of their derived functors and preserves the counits. Compose with
the existing normalized completed-scalar comparison. Its counit equation and the strict
chain transport identify the resulting square with the required quotient-completion
normalization, including the zero shifted coordinate. Intrinsic derived completeness
agrees with the legacy augmented-tower predicate; choose an auxiliary finite field in a
prime characteristic different from l to apply the finite-free comparison, which makes
this specified component invertible. Finally, good complexes localize to the derived
category. The normalization forces equality on every good representative by cancellation
of its representative comparison, and localization forces equality on all objects. -/
private theorem archivedIntegralScalarCompletion (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! χ : integralOrdinaryDerivedScalar l E L ι W ⟶ integralScalarExtension l E L ι W,
      (∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
        χ.app (DerivedCategory.Q.obj P.obj) ≫
            (integralScalarExtensionComparison l E L ι W).hom.app P =
          (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.obj ≫
            DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι W).app P.obj)) ∧
      (∀ K, IsSfDerivedComplete l E W K → IsIso (χ.app K)) := by
  let G := integralOrdinaryScalar l E L ι W
  let q := HomologicalComplex.quasiIso (integralTowerModules l E W) (.up ℤ)
  let D := archivedCompletedScalarCochainModel l E L ι W
  let T := completedDerivedScalarExtension.{u, u} l E L ι W
  let t := NatIso.mapHomologicalComplex (ordinaryScalarModelIso l E L ι W) (.up ℤ)
  let ε : DerivedCategory.Q ⋙ T ⟶
      completedOrdinaryScalarComplex l E L ι W ⋙ DerivedCategory.Q := D.ε
  let : T.IsLeftDerivedFunctor ε q := D.universal
  let : G.mapDerivedCategory.IsLeftDerivedFunctor G.mapDerivedCategoryFactors.hom q :=
    Functor.isLeftDerivedFunctor_of_inverts q _ G.mapDerivedCategoryFactors
  let e : integralOrdinaryDerivedScalar l E L ι W ≅ T :=
    Functor.leftDerivedNatIso G.mapDerivedCategory T G.mapDerivedCategoryFactors.hom
      ε q (Functor.isoWhiskerRight t DerivedCategory.Q)
  have he (P : CochainComplex (integralTowerModules l E W) ℤ) :
      e.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit.{u, u} l E L ι W P =
        G.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map (t.hom.app P) := by
    have h : e.hom.app (DerivedCategory.Q.obj P) ≫ ε.app P =
        G.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map (t.hom.app P) :=
      Functor.leftDerivedNatTrans_app G.mapDerivedCategory T
        G.mapDerivedCategoryFactors.hom ε q
        (Functor.isoWhiskerRight t DerivedCategory.Q).hom P
    have hε : ε.app P = completedScalarCounit.{u, u} l E L ι W P :=
      archivedCompletedScalarCochainModel_counit l E L ι W P
    exact (congrArg (e.hom.app (DerivedCategory.Q.obj P) ≫ ·) hε).symm.trans h
  let c : T ⟶ integralScalarExtension l E L ι W := by
    unfold integralScalarExtension
    exact completedScalarComparison.{u, u} l E L ι W
  let r (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
      (integralScalarExtension l E L ι W).obj (DerivedCategory.Q.obj P.obj) ⟶
        DerivedCategory.Q.obj ((integralScalarComplexFunctor l E L ι W).obj P.obj) :=
    (integralScalarExtensionComparison l E L ι W).hom.app P
  have hc (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
      c.app (DerivedCategory.Q.obj P.obj) ≫ r P =
        completedScalarCounit.{u, u} l E L ι W P.obj ≫
          DerivedCategory.Q.map ((completedScalarChainComparison.{u, u} l E L ι W).app P.obj) := by
    with_unfolding_all
      exact (completedScalarComparison_existsUnique.{u, u} l E L ι W).exists.choose_spec P
  let χ : integralOrdinaryDerivedScalar l E L ι W ⟶ integralScalarExtension l E L ι W :=
    e.hom ≫ c
  have hχ : ∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
      χ.app (DerivedCategory.Q.obj P.obj) ≫
          (integralScalarExtensionComparison l E L ι W).hom.app P =
        G.mapDerivedCategoryFactors.hom.app P.obj ≫
          DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι W).app P.obj) := by
    intro P
    change (e.hom.app _ ≫ c.app _) ≫ r P = _
    calc
      _ = e.hom.app _ ≫ (c.app _ ≫ r P) :=
        Category.assoc _ _ _
      _ = e.hom.app _ ≫ (completedScalarCounit.{u, u} l E L ι W P.obj ≫
          DerivedCategory.Q.map ((completedScalarChainComparison.{u, u} l E L ι W).app P.obj)) :=
        congrArg (e.hom.app (DerivedCategory.Q.obj P.obj) ≫ ·) (hc P)
      _ = (e.hom.app _ ≫ completedScalarCounit.{u, u} l E L ι W P.obj) ≫
          DerivedCategory.Q.map ((completedScalarChainComparison.{u, u} l E L ι W).app P.obj) :=
        (Category.assoc _ _ _).symm
      _ = (G.mapDerivedCategoryFactors.hom.app P.obj ≫
          DerivedCategory.Q.map (t.hom.app P.obj)) ≫
          DerivedCategory.Q.map ((completedScalarChainComparison.{u, u} l E L ι W).app P.obj) :=
        congrArg (· ≫ DerivedCategory.Q.map
          ((completedScalarChainComparison.{u, u} l E L ι W).app P.obj)) (he P.obj)
      _ = G.mapDerivedCategoryFactors.hom.app P.obj ≫ DerivedCategory.Q.map
          (t.hom.app P.obj ≫ (completedScalarChainComparison.{u, u} l E L ι W).app P.obj) :=
        (Category.assoc _ _ _).trans (congrArg
          (G.mapDerivedCategoryFactors.hom.app P.obj ≫ ·)
          (DerivedCategory.Q.map_comp _ _).symm)
      _ = _ := congrArg (fun z ↦ G.mapDerivedCategoryFactors.hom.app P.obj ≫
        DerivedCategory.Q.map z)
          (NatTrans.congr_app (integralScalarCompletionChain_model l E L ι W) P.obj).symm
  refine ⟨χ, ⟨hχ, ?_⟩, ?_⟩
  · intro K hK
    obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
    let : Fact p.Prime := ⟨hp⟩
    let Δ : FiniteFieldDatum.{0} :=
      { p := p
        a := 1
        q := p
        prime := hp
        exponent_pos := le_refl 1
        cardinality_eq := (pow_one p).symm
        k₀ := ZMod p
        card_base := by simp [Nat.card_eq_fintype_card]
        k := AlgebraicClosure (ZMod p) }
    have hl : l ≠ Δ.p := by change l ≠ p; omega
    have hlegacy : IsDerivedCompleteUnrestricted l E W K :=
      ⟨Δ, hl, (sfDerivedComplete_iff_legacy l E W Δ hl K).mp hK⟩
    let : IsIso (c.app K) := by
      with_unfolding_all
        exact (finiteFreeCompletedScalarComparison.{u, u} l E L ι W).2.1 K hlegacy |>.1
    change IsIso (e.hom.app K ≫ c.app K)
    infer_instance
  · intro χ' hχ'
    apply NatTrans.ext
    funext K
    let X := (DerivedCategory.Q (C := integralTowerModules l E W)).objPreimage K
    let eX := (DerivedCategory.Q (C := integralTowerModules l E W)).objObjPreimageIso K
    obtain ⟨V, f, hV, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E W) X
    have hgood : integralOperationsGoodComplex l E W V := by
      refine ⟨hV, fun i ↦ ?_⟩
      exact (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso
          (completedIntegralCommRingSheafUnrestricted l E W) (V.X i)).symm (hf i)
    let P : (integralOperationsGoodComplex l E W).FullSubcategory := ⟨V, hgood⟩
    let : QuasiIso f := hq
    let eP : DerivedCategory.Q.obj P.obj ≅ K := asIso (DerivedCategory.Q.map f) ≪≫ eX
    apply (cancel_epi ((integralOrdinaryDerivedScalar l E L ι W).map eP.hom)).mp
    rw [χ'.naturality, χ.naturality]
    congr 1
    apply (cancel_mono ((integralScalarExtensionComparison l E L ι W).hom.app P)).mp
    exact (hχ'.1 P).trans (hχ P).symm

private noncomputable def scalarExtensionDatum (p : ℕ) (hp : p.Prime) :
    FiniteFieldDatum.{u} := by
  letI : Fact p.Prime := ⟨hp⟩
  exact {
    p := p
    a := 1
    q := p
    prime := hp
    exponent_pos := le_refl 1
    cardinality_eq := (pow_one p).symm
    k₀ := ULift.{u} (ZMod p)
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ULift.{u} (ZMod p)) }

private theorem constructible_iff_legacy
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (Y : AlgebraicGeometry.Scheme.{u})
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E Y)) :
    sfIntegralConstructible l E Y K ↔
      boundedConstructibleDerivedCompleteIntegral D l hl E Y K := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types false in
    constructor
    · rintro ⟨hK, a, b, hab, h⟩
      refine ⟨(sfDerivedComplete_iff_legacy l E Y D hl K).mp hK, a, b, hab, ?_⟩
      intro n
      exact ⟨(h n).1, fun i hi ↦ (h n).2 hi⟩
    · rintro ⟨hK, a, b, hab, h⟩
      refine ⟨(sfDerivedComplete_iff_legacy l E Y D hl K).mpr hK, a, b, hab, ?_⟩
      intro n
      exact ⟨(h n).1, fun i hi ↦ (h n).2 i hi⟩

/-- Completed integral scalar extension preserves the intrinsic bounded constructible
predicate over arbitrary schemes.
Source: blueprint order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
Proof: the K-flat augmented-tower definition of completeness is equivalent to the intrinsic
one, by the canonical tensor counits, normalized units, and pure-tensor transitions.
Finite-level constructibility and the common cohomological interval are the same in the
two predicates. Choose an auxiliary finite-field datum of prime characteristic larger
than l, transfer the input to the legacy predicate, apply the published completed
scalar-extension preservation theorem, and transfer its output back. The auxiliary
datum imposes no condition on the scheme and disappears from the conclusion.
-/
theorem sfIntegralScalarExtension_constructible
    (p l : ℕ) [Fact l.Prime] (_hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (Y : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E Y))
    (hK : sfIntegralConstructible l E Y K) :
    sfIntegralConstructible l L Y
      ((integralScalarExtension l E L ι Y).obj K) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types false in
    obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (l + 1)
    let D := scalarExtensionDatum.{u} q hprime
    have hlD : l ≠ D.p := by
      change l ≠ q
      omega
    have hlegacy := (constructible_iff_legacy l E Y D hlD K).mp hK
    exact (constructible_iff_legacy l L Y D hlD _).mpr
      (integralScalarExtension_constructible D l hlD E L ι Y ⟨K, hlegacy⟩)

/-- The completed scalar extension restricted to intrinsic bounded constructible
objects. Its object map is the ambient extension and its morphism map is inherited.
Source: blueprint order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
-/
noncomputable def sfConstructibleIntegralScalarExtension
    (p l : ℕ) [Fact l.Prime] (_hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (Y : AlgebraicGeometry.Scheme.{u}) :
    sfIntegralConstructibleCategory l E Y ⥤
      sfIntegralConstructibleCategory l L Y :=
  (sfIntegralConstructible l L Y).lift
    ((sfIntegralConstructible l E Y).ι ⋙ integralScalarExtension l E L ι Y)
    (fun X ↦ sfIntegralScalarExtension_constructible p l _hl E L ι Y X.obj X.property)

/-- The restricted functor is linear for the integral coefficient action.
Source: blueprint order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
Proof: the ambient completed extension is linear on morphisms; the full-subcategory
restriction preserves the same equality.
-/
theorem sfConstructibleIntegralScalarExtension_smul
    (p l : ℕ) [Fact l.Prime] (_hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (Y : AlgebraicGeometry.Scheme.{u})
    (K K' : sfIntegralConstructibleCategory l E Y)
    (f : K ⟶ K') (a : Padic.coefficientExtensionIntegers l E) :
    (integralScalarExtension l E L ι Y).map
        ((integralScalarDerivedAction l E Y a).app K.obj ≫ f.hom) =
      (integralScalarDerivedAction l L Y
          (integralScalarIntegerInclusion l E L ι a)).app
          ((sfConstructibleIntegralScalarExtension p l _hl E L ι Y).obj K).obj ≫
        ((sfConstructibleIntegralScalarExtension p l _hl E L ι Y).map f).hom := by
  exact (integralScalarExtensionWellDefined l E L ι Y).2.choose_spec.choose_spec.2.2.2.2
    a K.obj K'.obj f.hom

end WeilConjectures
