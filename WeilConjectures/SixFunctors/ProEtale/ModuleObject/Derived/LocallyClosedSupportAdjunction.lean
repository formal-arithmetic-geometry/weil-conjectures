/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import all WeilConjectures.AlgebraicGeometry.SixFunctors.BrownHypothesesSmall
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicLocalizingExceptionalBounded
import WeilConjectures.CategoryTheory.SixFunctors.CohomologicalSolutionSetRepresentability
import WeilConjectures.CategoryTheory.SixFunctors.SetGeneratedDerivedSolutionSet
import WeilConjectures.CategoryTheory.SmoothPurity.CountableCoproductsIdempotentComplete
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.FullSubcategory

/-! # Locally closed restriction and its Brown right adjoint -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open CategoryTheory.Pretriangulated.Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem support_cohomological_representable (X : Scheme.{u})
    [CompactSpace X] [IsLocallyNoetherian X]
    (htri : (localizingClosureProEtale Λ X).IsTriangulated)
    (hiso : (localizingClosureProEtale Λ X).IsClosedUnderIsomorphisms)
    (hcop : ∀ I : Type (u + 1),
      (localizingClosureProEtale Λ X).IsClosedUnderColimitsOfShape (Discrete I)) :
    letI := htri
    letI := hiso
    letI := hcop
    ∀ (H : (localizingClosureProEtale Λ X).FullSubcategoryᵒᵖ ⥤
        AddCommGrpCat.{u + 1}) [H.IsHomological],
      (∀ I : Type (u + 1), PreservesLimitsOfShape (Discrete I) H) →
        (H ⋙ forget AddCommGrpCat).IsRepresentable := by
  let := htri
  let := hiso
  let := hcop
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let P := constantModelBoundedConstructible Λ X ⊓
    (fun K : DerivedCategory A ↦ _root_.DerivedCategory.finiteTorAmplitude A K)
  have : ObjectProperty.EssentiallySmall.{u + 1} P := by
    have := small_bounded_constant_models Λ X
    exact ObjectProperty.EssentiallySmall.of_le (fun _ h ↦ h.1)
  obtain ⟨hambient, _, _, _, _, _, _, _⟩ := localizingClosure_exists Λ X P
  let := hambient
  let : HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory :=
    fun I ↦ hasColimitsOfShape_of_closedUnderColimits (Discrete I) _
  let : IsIdempotentComplete (localizingClosureProEtale Λ X).FullSubcategory :=
    CategoryTheory.isIdempotentComplete_of_countableCoproducts _
  intro H instH hH
  apply cohomological_isRepresentable_of_solutionSet H hH
  refine setGeneratedDerived_cohomological_solutionSet P
    (localizingClosureProEtale Λ X) (fun K hK Q _ hQ ↦ hQ K hK) ?_ H hH
  intro Q hPQ hi ht hc
  have hQ : IsLocalizingSubcategoryOfSize.{u + 1} Q := by
    refine ⟨ht, hi, ?_⟩
    intro I F hF hmem
    let := hc I
    let := hF
    exact Q.prop_colimit F (fun i ↦ hmem i.as)
  have hQbig : IsLocalizingSubcategory Q :=
    CategoryTheory.Functor.localizing_large Q hQ
  intro K hK
  exact hK Q hQbig hPQ

private theorem support_restricted_leftAdjoint
    {X Y : Scheme.{u}} [CompactSpace X] [IsLocallyNoetherian X]
    (F : (localizingClosureProEtale Λ X).FullSubcategory ⥤
      (localizingClosureProEtale Λ Y).FullSubcategory)
    [(localizingClosureProEtale Λ X).IsTriangulated]
    [(localizingClosureProEtale Λ Y).IsTriangulated]
    [(localizingClosureProEtale Λ X).IsClosedUnderIsomorphisms]
    [(localizingClosureProEtale Λ Y).IsClosedUnderIsomorphisms]
    [∀ I : Type (u + 1),
      (localizingClosureProEtale Λ X).IsClosedUnderColimitsOfShape (Discrete I)]
    [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) F) :
    F.IsLeftAdjoint := by
  apply Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top
  funext K
  apply propext
  refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
  let H := F.op ⋙ preadditiveYoneda.obj K
  let := Pretriangulated.Opposite.instHasShiftOppositeInt
    (localizingClosureProEtale Λ X).FullSubcategory
  let := Pretriangulated.Opposite.instHasShiftOppositeInt
    (localizingClosureProEtale Λ Y).FullSubcategory
  let := Pretriangulated.Opposite.instOpposite
    (C := (localizingClosureProEtale Λ X).FullSubcategory)
  let := Pretriangulated.Opposite.instOpposite
    (C := (localizingClosureProEtale Λ Y).FullSubcategory)
  let := Pretriangulated.Opposite.commShiftFunctorOpInt F
  let := Pretriangulated.Opposite.functor_isTriangulated_op F
  have : H.IsHomological := by
    change (F.op ⋙ preadditiveYoneda.obj K).IsHomological
    infer_instance
  have hH : ∀ I : Type (u + 1), PreservesLimitsOfShape (Discrete I) H := by
    intro I
    let := hF I
    let : PreservesColimitsOfShape (Discrete I)ᵒᵖ F :=
      preservesColimitsOfShape_of_equiv (Discrete.opposite I).symm F
    let : PreservesLimitsOfShape (Discrete I) F.op :=
      preservesLimitsOfShape_op (Discrete I) F
    have : PreservesLimitsOfShape (Discrete I)
        (preadditiveYoneda.obj K ⋙ forget AddCommGrpCat) :=
      inferInstanceAs (PreservesLimitsOfShape (Discrete I) (yoneda.obj K))
    have : PreservesLimitsOfShape (Discrete I) (preadditiveYoneda.obj K) :=
      preservesLimitsOfShape_of_reflects_of_preserves _ (forget AddCommGrpCat)
    change PreservesLimitsOfShape (Discrete I) (F.op ⋙ preadditiveYoneda.obj K)
    infer_instance
  exact support_cohomological_representable Λ X inferInstance inferInstance
    (fun I ↦ inferInstance) H hH

/--
The restricted locally closed exceptional functor preserves the localizing closure and has a
right adjoint.  This is the Brown representability step: extension by zero is handled by the
open immersion localization theorem, the closed direct image by compactification localization,
and the solution-set argument is applied to the resulting set-generated triangulated hull.
Source: internal-Hom stability proof, Steps 8--9.
(blueprint: lem-sfb-locally-closed-support-adjunction).
-/
theorem locallyClosed_support_adjunction
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (S Z : Scheme.{u}) (a : S ⟶ X) (j : S ⟶ Z) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i] (ha : a = j ≫ i) :
    let F := (openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
      (lowerStar Λ i).rightDerivedFunctor
    ∃ (h : ∀ M, localizingClosureProEtale Λ S M →
        localizingClosureProEtale Λ X (F.obj M))
      (G : (localizingClosureProEtale Λ X).FullSubcategory ⥤
        (localizingClosureProEtale Λ S).FullSubcategory),
      Nonempty ((localizingClosureProEtale Λ X).lift
        ((localizingClosureProEtale Λ S).ι ⋙ F) (fun M ↦ h M.obj M.property) ⊣ G) := by
  classical
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : Z.Over (Spec (.of k)) := ⟨i ≫ (X ↘ Spec (.of k))⟩
  let : S.Over (Spec (.of k)) := ⟨j ≫ (Z ↘ Spec (.of k))⟩
  let : i.IsOver (Spec (.of k)) := ⟨rfl⟩
  let : j.IsOver (Spec (.of k)) := ⟨rfl⟩
  let : LocallyOfFiniteType (Z ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (i ≫ (X ↘ Spec (.of k)))
    infer_instance
  let : QuasiCompact (Z ↘ Spec (.of k)) := by
    change QuasiCompact (i ≫ (X ↘ Spec (.of k)))
    infer_instance
  let : IsSeparated (Z ↘ Spec (.of k)) := by
    change IsSeparated (i ≫ (X ↘ Spec (.of k)))
    infer_instance
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of k))
  let : LocallyOfFiniteType (S ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (j ≫ (Z ↘ Spec (.of k)))
    infer_instance
  let : QuasiCompact (S ↘ Spec (.of k)) := by
    change QuasiCompact (j ≫ (Z ↘ Spec (.of k)))
    infer_instance
  let : IsSeparated (S ↘ Spec (.of k)) := by
    change IsSeparated (j ≫ (Z ↘ Spec (.of k)))
    infer_instance
  let : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of k))
  let : LocallyOfFiniteType a := by rw [ha]; infer_instance
  let : QuasiCompact a := by rw [ha]; infer_instance
  let : IsSeparated a := by rw [ha]; infer_instance
  let : a.IsOver (Spec (.of k)) := ⟨by
    change a ≫ (X ↘ Spec (.of k)) = j ≫ i ≫ (X ↘ Spec (.of k))
    rw [ha, Category.assoc]⟩
  let : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of k))
  let c₀ : Compactification a :=
    { Z := Z, g := i, i := j, comm := ha,
      isProper := inferInstance, isOpenImmersion := inferInstance }
  let c : Compactification.BoundaryCompactification a := ⟨⟨c₀, inferInstance⟩⟩
  obtain ⟨h, htri, hsums, _⟩ := compactification_localizing Λ ℓ k a c hΛ
  let F₀ := rightDerivedLowerShriekOfCompactification Λ c₀
  let PS := constantModelBoundedConstructible Λ S ⊓
    fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K
  let PX := constantModelBoundedConstructible Λ X ⊓
    fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K
  obtain ⟨hambientS, _, _, hlocalS, _, _, _, _⟩ := localizingClosure_exists Λ S PS
  obtain ⟨hambientX, _, _, hlocalX, _, _, _, _⟩ := localizingClosure_exists Λ X PX
  let := hambientS
  let := hambientX
  let : (localizingClosureProEtale Λ S).IsTriangulated := hlocalS.1
  let : (localizingClosureProEtale Λ X).IsTriangulated := hlocalX.1
  let : (localizingClosureProEtale Λ S).IsClosedUnderIsomorphisms := hlocalS.2.1
  let : (localizingClosureProEtale Λ X).IsClosedUnderIsomorphisms := hlocalX.2.1
  have hclosed (T : Scheme.{u}) (hT : IsLocalizingSubcategory
      (localizingClosureProEtale Λ T)) (I : Type (u + 2)) :
      (localizingClosureProEtale Λ T).IsClosedUnderColimitsOfShape (Discrete I) := by
    let := hT.2.1
    apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
    rintro _ ⟨K, hK⟩
    exact hT.2.2 K inferInstance (fun i ↦ hK (Discrete.mk i))
  have hsmall (T : Scheme.{u}) (hT : IsLocalizingSubcategory
      (localizingClosureProEtale Λ T)) (I : Type (u + 1)) :
      (localizingClosureProEtale Λ T).IsClosedUnderColimitsOfShape (Discrete I) := by
    let := hclosed T hT (ULift.{u + 2} I)
    exact ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence Equiv.ulift)
  let : ∀ I : Type (u + 1),
      (localizingClosureProEtale Λ S).IsClosedUnderColimitsOfShape (Discrete I) :=
    hsmall S hlocalS
  let : ∀ I : Type (u + 1),
      (localizingClosureProEtale Λ X).IsClosedUnderColimitsOfShape (Discrete I) :=
    hsmall X hlocalX
  let LF := (localizingClosureProEtale Λ X).lift
    ((localizingClosureProEtale Λ S).ι ⋙ F₀) (fun M ↦ h M.obj M.property)
  have hFsums : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) LF := by
    intro I
    let : HasColimitsOfShape (Discrete I) (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))) :=
      hambientS I
    let : PreservesColimitsOfShape (Discrete I) (localizingClosureProEtale Λ S).ι :=
      inferInstance
    let eI := Discrete.equivalence (Equiv.ulift : ULift.{u + 2} I ≃ I)
    have hcomp : PreservesColimitsOfShape (Discrete I)
        ((localizingClosureProEtale Λ S).ι ⋙ F₀) := by
      constructor
      intro K
      have hpres : PreservesColimit (K ⋙ (localizingClosureProEtale Λ S).ι) F₀ := by
        let H := K ⋙ (localizingClosureProEtale Λ S).ι
        let := hsums (ULift.{u + 2} I) (eI.functor ⋙ H)
          (fun i ↦ (K.obj (eI.functor.obj (Discrete.mk i))).property)
        exact Functor.Final.preservesColimit_of_comp eI.functor
      let := hpres
      let : PreservesColimit K (localizingClosureProEtale Λ S).ι :=
        PreservesColimitsOfShape.preservesColimit
      exact comp_preservesColimit (localizingClosureProEtale Λ S).ι F₀
    have : PreservesColimitsOfShape (Discrete I)
        (LF ⋙ (localizingClosureProEtale Λ X).ι) := by
      let := hcomp
      exact preservesColimitsOfShape_of_natIso
        ((localizingClosureProEtale Λ X).liftCompιIso _ _).symm
    exact preservesColimitsOfShape_of_reflects_of_preserves LF
      (localizingClosureProEtale Λ X).ι
  let : LF.IsTriangulated := by
    dsimp [LF, F₀, rightDerivedLowerShriekOfCompactification]
    infer_instance
  let : LF.IsLeftAdjoint := support_restricted_leftAdjoint Λ LF hFsums
  exact ⟨h, LF.rightAdjoint, ⟨Adjunction.ofIsLeftAdjoint LF⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
