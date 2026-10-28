/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefficientDerivedSystemEvaluationData
import all Sheaf.CategoryTheory.CoefficientSequenceGlobalSections
import all Sheaf.CategoryTheory.CoefficientSequenceSectionsLimit
import Sheaf.CategoryTheory.CoefficientRestrictionSectionsAcyclic
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import all Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! Proved implementation helpers for normalized coefficient sections.
Source: Stacks 079P, 0941 and 0D6E.
The ordinary transport, recorded derived pairs, and their normalized comparisons
are shared by the scalar and total-limit construction.
(blueprint: lem-coef-sections-core-limit-transport)
-/

@[expose] public section
set_option autoImplicit false
set_option linter.privateModule false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures



section GenericSections

universe c v r
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasLimitsOfShape Cᵒᵖ AddCommGrpCat.{max c v r}]
  (A : Sheaf J CommRingCat.{max c v r})

private noncomputable def ordinarySectionsEquiv
    (M : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) :
    (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A) ⟶ M) ≃+
      (SheafOfModules.sequenceCoefficientSections A).obj M := by
  let e : (limit M.val.presheaf : AddCommGrpCat.{max c v r}) ≃ M.sections :=
    Types.isLimitEquivSections
      (isLimitOfPreserves (forget AddCommGrpCat) (limit.isLimit M.val.presheaf))
  refine { toEquiv := M.unitHomEquiv.trans e.symm, map_add' := ?_ }
  intro f g
  apply Concrete.limit_ext
  intro U
  have he (h : SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A) ⟶ M) :
      (limit.π M.val.presheaf U) (e.symm (M.unitHomEquiv h)) =
        h.val.app U (1 : A.obj.obj U) := by
    convert! Types.isLimitEquivSections_symm_apply
      (isLimitOfPreserves (forget AddCommGrpCat) (limit.isLimit M.val.presheaf))
      (M.unitHomEquiv h) U using 1
  change (limit.π M.val.presheaf U) (e.symm (M.unitHomEquiv (f + g))) =
    (limit.π M.val.presheaf U) (e.symm (M.unitHomEquiv f) + e.symm (M.unitHomEquiv g))
  rw [(limit.π M.val.presheaf U).hom.map_add, he, he, he]
  rfl

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasLimitsOfShape Cᵒᵖ AddCommGrpCat.{max c v r}] in
private theorem ordinarySectionsEquiv_π
    (M : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A))
    (f : SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A) ⟶ M)
    (U : Cᵒᵖ) :
    (limit.π M.val.presheaf U) (ordinarySectionsEquiv.{c, v, r} J A M f) =
      f.val.app U (1 : A.obj.obj U) := by
  convert! Types.isLimitEquivSections_symm_apply
    (isLimitOfPreserves (forget AddCommGrpCat) (limit.isLimit M.val.presheaf))
    (M.unitHomEquiv f) U using 1

private noncomputable def ordinarySectionsIso :
    coefficientOrdinarySections.{r, c, v} J A ≅
      SheafOfModules.sequenceCoefficientSections A := by
  refine NatIso.ofComponents (fun M ↦ (ordinarySectionsEquiv.{c, v, r} J A M).toAddCommGrpIso) ?_
  intro M N f
  ext x
  apply Concrete.limit_ext
  intro U
  change (limit.π N.val.presheaf U) (ordinarySectionsEquiv.{c, v, r} J A N (x ≫ f)) =
    (limit.π N.val.presheaf U) ((SheafOfModules.sequenceCoefficientSections A).map f
      (ordinarySectionsEquiv.{c, v, r} J A M x))
  rw [ordinarySectionsEquiv_π.{c, v, r}]
  change f.val.app U (x.val.app U (1 : A.obj.obj U)) = _
  have h := congrArg (fun z : (SheafOfModules.sequenceCoefficientSections A).obj M ⟶
        N.val.presheaf.obj U ↦ z (ordinarySectionsEquiv.{c, v, r} J A M x))
    (limMap_π ((PresheafOfModules.toPresheaf _).map f.val) U).symm
  simp only [AddCommGrpCat.comp_apply] at h
  change f.val.app U ((limit.π M.val.presheaf U)
    (ordinarySectionsEquiv.{c, v, r} J A M x)) = _ at h
  rw [ordinarySectionsEquiv_π] at h
  exact h


end GenericSections

section GenericScalarSections

universe c v r w
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasLimitsOfShape Cᵒᵖ AddCommGrpCat.{max c v r}]
  {A B : Sheaf J CommRingCat.{max c v r}} (f : A ⟶ B)

private noncomputable def ordinaryRestrictionIso :
    SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map f) ⋙
        coefficientOrdinarySections.{r, c, v} J A ≅
      coefficientOrdinarySections.{r, c, v} J B :=
  Functor.isoWhiskerLeft _ (ordinarySectionsIso.{c, v, r} J A) ≪≫
    (Iso.refl (SheafOfModules.sequenceCoefficientSections B)) ≪≫
      (ordinarySectionsIso.{c, v, r} J B).symm

omit [HasLimitsOfShape Cᵒᵖ AddCommGrpCat.{max c v r}] in
private theorem ordinaryRestrictionIso_one
    (M : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj B))
    (h : SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A) ⟶
        (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map f)).obj M)
    (U : Cᵒᵖ) :
    (((ordinaryRestrictionIso.{c, v, r} J f).hom.app M) h).val.app U
        (1 : B.obj.obj U) = h.val.app U (1 : A.obj.obj U) := by
  have he : (ordinarySectionsIso.{c, v, r} J B).hom.app M
      (((ordinaryRestrictionIso.{c, v, r} J f).hom.app M) h) =
    (ordinarySectionsIso.{c, v, r} J A).hom.app
      ((SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map f)).obj M) h := by
    change (ordinarySectionsIso.{c, v, r} J B).hom.app M
      ((ordinarySectionsIso.{c, v, r} J B).inv.app M
        ((ordinarySectionsIso.{c, v, r} J A).hom.app _ h)) = _
    exact (ordinarySectionsIso.{c, v, r} J B).app M |>.addCommGroupIsoToAddEquiv.apply_symm_apply _
  have hx := congrArg (fun z ↦ (limit.π M.val.presheaf U) z) he
  change (limit.π M.val.presheaf U) (ordinarySectionsEquiv.{c, v, r} J B M
      (((ordinaryRestrictionIso.{c, v, r} J f).hom.app M) h)) =
    (limit.π M.val.presheaf U) (ordinarySectionsEquiv.{c, v, r} J A
      ((SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map f)).obj M)
      h) at hx
  rw [ordinarySectionsEquiv_π] at hx
  exact hx.trans (ordinarySectionsEquiv_π.{c, v, r} J A _ h U)

omit [HasLimitsOfShape Cᵒᵖ AddCommGrpCat.{max c v r}] in
private theorem ordinaryRestrictionIso_formula
    (M : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj B))
    (h : SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A) ⟶
        (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map f)).obj M)
    (U : Cᵒᵖ) (b : B.obj.obj U) :
    (((ordinaryRestrictionIso.{c, v, r} J f).hom.app M) h).val.app U b =
      b • (@id (M.val.obj U) (h.val.app U (1 : A.obj.obj U))) := by
  let g := (((ordinaryRestrictionIso.{c, v, r} J f).hom.app M) h).val.app U
  calc
    g b = g (b • (1 : B.obj.obj U)) := by rw [smul_eq_mul, mul_one]
    _ = b • g (1 : B.obj.obj U) := g.hom.map_smul _ _
    _ = _ := congrArg (fun z ↦ b • z) (ordinaryRestrictionIso_one.{c, v, r} J f M h U)



variable [EssentiallySmall.{max c v r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]

private theorem ordinaryRestrictionSections_quasiIso
    (I : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj B)) ℤ)
    (K : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) ℤ)
    (j : ((SheafOfModules.restrictScalars
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map f)).mapHomologicalComplex
      (.up ℤ)).obj I ⟶ K)
    [I.IsKInjective] [K.IsKInjective] [QuasiIso j] :
    QuasiIso (((coefficientOrdinarySections.{r, c, v} J A).mapHomologicalComplex
      (.up ℤ)).map j) := by
  let : HasDerivedCategory AddCommGrpCat.{max c v r} := HasDerivedCategory.standard _
  have : QuasiIso (((SheafOfModules.sequenceCoefficientSections A).mapHomologicalComplex
      (.up ℤ)).map j) := SheafOfModules.coefficientRestrictionSections_quasiIso f I K j
  have hi : IsIso ((SheafOfModules.sequenceCoefficientSections A).mapHomologicalComplex
      (.up ℤ) ⋙ DerivedCategory.Q |>.map j) := by
    change IsIso (DerivedCategory.Q.map
      (((SheafOfModules.sequenceCoefficientSections A).mapHomologicalComplex
        (.up ℤ)).map j))
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _
      (((SheafOfModules.sequenceCoefficientSections A).mapHomologicalComplex
        (.up ℤ)).map j)).mpr inferInstance
  have hj : IsIso (((coefficientOrdinarySections.{r, c, v} J A).mapHomologicalComplex
      (.up ℤ) ⋙ DerivedCategory.Q).map j) :=
    (NatIso.isIso_map_iff (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (ordinarySectionsIso.{c, v, r} J A) (.up ℤ))
        DerivedCategory.Q) j).mpr hi
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hj

end GenericScalarSections

section GenericDerived

universe a av b bv da db
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{da} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{db} B]
  [Abelian.HasKInjectiveResolutions A]

private noncomputable def standardSectionsPair (F : A ⥤ B) [F.Additive] :
    SheafOfModules.SequenceSectionsDerivedPair F := by
  let η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    { app := F.rightDerivedFunctorUnitQ
      naturality := fun _ _ f ↦ F.rightDerivedFunctorUnitQ_naturality f }
  have hi (I : CochainComplex A ℤ) (hI : I.IsKInjective) : IsIso (η.app I) := by
    let := hI
    change IsIso (F.rightDerivedFunctorUnitQ I)
    rw [F.rightDerivedFunctorUnitQ_eq]
    infer_instance
  refine ⟨F.rightDerivedFunctor, η, ?_, hi⟩
  apply (SheafOfModules.sectionsDerives F).isRightDerivedFunctor_of_isIso
  intro I
  exact hi I.obj I.property

end GenericDerived

section GenericRestrictionDerived

universe a av b bv da db r
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{da} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{db} B]
  [HasDerivedCategory AddCommGrpCat.{r}]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
  (R : B ⥤ A) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (F : A ⥤ AddCommGrpCat.{r}) [F.Additive]
  (G : B ⥤ AddCommGrpCat.{r}) [G.Additive] (e : R ⋙ F ≅ G)

omit [Abelian.HasKInjectiveResolutions A] in
private theorem restrictionDerivedIso
    (P : SheafOfModules.SequenceSectionsDerivedPair F)
    (S : SheafOfModules.SequenceSectionsDerivedPair G)
    (hc : ∀ (I : CochainComplex B ℤ), I.IsKInjective →
      IsIso (P.unit.app ((R.mapHomologicalComplex (.up ℤ)).obj I))) :
    ∃ s : R.mapDerivedCategory ⋙ P.functor ≅ S.functor,
      ∀ I : CochainComplex B ℤ,
        P.unit.app ((R.mapHomologicalComplex (.up ℤ)).obj I) ≫
            P.functor.map (R.mapDerivedCategoryFactors.inv.app I) ≫
              s.hom.app (DerivedCategory.Q.obj I) =
          DerivedCategory.Q.map
            (coefficientComplexCompositeSourceTransformation R F e.hom I) ≫ S.unit.app I := by
  let L := SheafOfModules.sectionsExactComposite R F P hc
  have := L.universal
  have := S.universal
  let τ := Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)) DerivedCategory.Q
  let s : L.functor ≅ S.functor := Functor.rightDerivedNatIso _ _ L.unit S.unit
    (HomologicalComplex.quasiIso B (.up ℤ)) τ
  refine ⟨s, ?_⟩
  intro I
  have h := Functor.rightDerivedNatTrans_app _ _ L.unit S.unit
    (HomologicalComplex.quasiIso B (.up ℤ)) τ.hom I
  change (P.unit.app ((R.mapHomologicalComplex (.up ℤ)).obj I) ≫
      P.functor.map (R.mapDerivedCategoryFactors.inv.app I)) ≫ s.hom.app _ =
    τ.hom.app I ≫ S.unit.app I at h
  simpa only [τ, NatIso.mapHomologicalComplex, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, coefficientComplexCompositeSourceTransformation,
    Category.assoc] using h

end GenericRestrictionDerived

section GenericSectionsLimit

universe a av da dta r sep
variable {A : Type a} [Category.{av} A] [Abelian A]
  [HasDerivedCategory.{da} A] [HasDerivedCategory.{dta} (ℕᵒᵖ ⥤ A)]
  [IsGrothendieckAbelian.{sep} A] [HasLimitsOfShape ℕᵒᵖ A]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive]
  [(lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤ AddCommGrpCat.{r}).Additive]
  (F : A ⥤ AddCommGrpCat.{r}) [F.Additive] [PreservesLimitsOfShape ℕᵒᵖ F]

/-- Derived sections commute with total tower limit for the recorded right-derived functors.
Source: Stacks 079P, 0941 and 0D6E.
Proof: the exact constant left adjoint makes inverse limit preserve K-injectives.
The tower-image acyclicity theorem handles the opposite composite. Both composite
units define right derivations, so their ordinary limit-preservation isomorphism
induces the required natural isomorphism by uniqueness of right derivation.
(blueprint: lem-coef-sections-core-limit-transport) -/
private theorem sectionsLimitComparison :
    Nonempty ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor ⋙ F.rightDerivedFunctor ≅
      ((Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{r}).obj F).rightDerivedFunctor ⋙
        (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤ AddCommGrpCat.{r}).rightDerivedFunctor) := by
  let : IsGrothendieckAbelian.{sep} (ℕᵒᵖ ⥤ A) := SheafOfModules.sectionsTowerGrothendieck
  let : IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) :=
    SheafOfModules.sectionsTowerGrothendieck
  let LA := (lim : (ℕᵒᵖ ⥤ A) ⥤ A)
  let LB := (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤ AddCommGrpCat.{r})
  let T := (Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{r}).obj F
  let : LA.Additive := Functor.additive_of_preserves_binary_products _
  let : LB.Additive := Functor.additive_of_preserves_binary_products _
  let : LA.PreservesKInjectiveComplexes :=
    Adjunction.preservesKInjectiveComplexes constLimAdj
  let P := standardSectionsPair F
  let Q := standardSectionsPair T
  let L := standardSectionsPair LA
  let M := standardSectionsPair LB
  let α := SheafOfModules.sectionsCompositeUnit LA F L P
  let β := SheafOfModules.sectionsCompositeUnit T LB Q M
  have ha := SheafOfModules.sectionsCompositeDerived LA F L P (fun I hI ↦ by
    have := hI
    exact P.computes _ inferInstance)
  have hb := SheafOfModules.sectionsCompositeDerived T LB Q M
    (SheafOfModules.sectionsTowerImageAcyclic F M)
  let τ := Functor.isoWhiskerRight (NatIso.mapHomologicalComplex
    (preservesLimitNatIso F (J := ℕᵒᵖ)) (.up ℤ)) DerivedCategory.Q
  have : (L.functor ⋙ P.functor).IsRightDerivedFunctor α
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) := ha
  have : (Q.functor ⋙ M.functor).IsRightDerivedFunctor β
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) := hb
  let κ : L.functor ⋙ P.functor ≅ Q.functor ⋙ M.functor :=
    Functor.rightDerivedNatIso _ _ α β
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) τ
  exact ⟨κ⟩

end GenericSectionsLimit

section SiteDerivedPair

universe c v r d
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (A : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{d} (SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A))]

open SheafOfModules in
private noncomputable def siteSectionsPair :
    SheafOfModules.SequenceSectionsDerivedPair (coefficientOrdinarySections.{r, c, v} J A) := by
  let : IsGrothendieckAbelian.{max c v r} (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J A).1
  let F := coefficientOrdinarySections.{r, c, v} J A
  let P := standardSectionsPair F
  refine { functor := coefficientGlobalSections.{r, c, v} J A
           unit := { app := coefficientSiteSectionsComparison.{r, c, v} J A
                     naturality := ?_ }
           universal := ?_
           computes := ?_ }
  · intro I K f
    exact F.rightDerivedFunctorUnitQ_naturality f
  · exact P.universal
  · intro I hI
    exact P.computes I hI

end SiteDerivedPair

end WeilConjectures
