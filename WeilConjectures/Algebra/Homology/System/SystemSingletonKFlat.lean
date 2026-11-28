/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemSingletonScalarBasic
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.System.SystemSequenceKFlatCriterion

/-! # K-flatness on the ringed sequence site of singleton extension

## Implementation details

Flat-term K-flatness on the ringed sequence site is detected levelwise
(`systemSequence_kFlat_of_evaluations`). At a level `m ≤ n` the singleton extension is the
scalar extension along the transition, which is a ringed-topos pullback; above `n` it is zero.

## References

* Stacks Project, Tags 06YN, 0D6D, 0G7E
* Zheng, Construction 4.1
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- The identity presentation of a ring sheaf as an algebraic inverse image. -/
private def singletonIdentityPullback (R : Sheaf J CommRingCat.{w}) :
    AlgebraicInverseImage (𝟭 (Sheaf J (Type w))) R R where
  ringUnderlying := Iso.refl _
  ringAdd := fun _ _ _ _ h ↦ h
  ringMul := fun _ _ _ _ h ↦ h
  ringZero := fun _ _ h ↦ h
  ringOne := fun _ _ h ↦ h
  modules := 𝟭 _
  moduleUnderlying := Iso.refl _
  moduleAdd := fun _ _ _ _ _ h ↦ h
  moduleZero := fun _ _ _ h ↦ h
  moduleSMul := fun _ _ _ _ _ h ↦ h

private local instance addCommGrpSmallestColimits : HasColimitsOfSize.{0, 0} AddCommGrpCat.{w} :=
  hasColimitsOfSizeShrink.{0, 0, w, w} _

private local instance moduleCoproducts (R : Sheaf J CommRingCat.{w}) (I : Type) :
    HasColimitsOfShape (Discrete I) (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :=
  have : HasColimitsOfShape (Discrete I) (PresheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _

/-- A functor with zero values preserves finite limits. -/
private theorem preservesFiniteLimits_of_isZero {A A' : Type*} [Category A] [Category A']
    (G : A ⥤ A') (hG : ∀ X, IsZero (G.obj X)) : PreservesFiniteLimits G where
  preservesFiniteLimits _ _ _ := ⟨fun {_} ↦ ⟨fun {c} _ ↦ ⟨
    { lift := fun s ↦ (hG c.pt).from_ s.pt
      fac := fun _ _ ↦ (hG _).eq_of_tgt _ _
      uniq := fun _ _ _ ↦ (hG _).eq_of_tgt _ _ }⟩⟩⟩

/-- A functor with zero values preserves finite colimits. -/
private theorem preservesFiniteColimits_of_isZero {A A' : Type*} [Category A] [Category A']
    (G : A ⥤ A') (hG : ∀ X, IsZero (G.obj X)) : PreservesFiniteColimits G where
  preservesFiniteColimits _ _ _ := ⟨fun {_} ↦ ⟨fun {c} _ ↦ ⟨
    { desc := fun s ↦ (hG c.pt).to_ s.pt
      fac := fun _ _ ↦ (hG _).eq_of_src _ _
      uniq := fun _ _ _ ↦ (hG _).eq_of_src _ _ }⟩⟩⟩

/-- A termwise zero complex is flat-term K-flat. -/
private theorem kFlat_of_isZero (R : Sheaf J CommRingCat.{w})
    (Q : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
    (hQ : ∀ i, IsZero (Q.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R) Q ∧
      ∀ i : ℤ, IsFlatOnSite (R := R) (Q.X i) := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  have hT (M N : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (hN : IsZero N) :
      IsZero (((MonoidalCategory.curriedTensor _).obj M).obj N) :=
    Functor.map_isZero _ hN
  refine ⟨fun F _ k ↦ ShortComplex.exact_of_isZero_X₂ _ ?_, fun i ↦ ?_⟩
  · change IsZero ((HomologicalComplex.mapBifunctor F Q
      (MonoidalCategory.curriedTensor _) (.up ℤ)).X k)
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    exact (hT _ _ (hQ q)).eq_of_src _ _
  · have hM : exactFunctor _ _ (MonoidalCategory.tensorRight (Q.X i)) :=
      (exactFunctor_iff _).2 ⟨preservesFiniteLimits_of_isZero _ fun M ↦ hT M _ (hQ i),
        preservesFiniteColimits_of_isZero _ fun M ↦ hT M _ (hQ i)⟩
    exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (Q.X i)).symm hM

variable (S : SystemScalarAssignment (J := J)) (T : SystemTensorCoherence S)
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- Below the selected level, the evaluated singleton is the tensor along the transition. -/
private def singletonSequenceOrdinaryBelow (n : ℕ) {m : ℕ} (h : m ≤ n) :
    singletonSequenceOrdinary S T B n ⋙ systemSequenceEvaluation B m ≅ systemTensor S B h :=
  Functor.isoWhiskerLeft (systemSingleFunctor S T B n)
      (Functor.isoWhiskerRight (strictSystemSequenceEquivalence B).unitIso.symm
        (systemEvaluation B m) ≪≫ Functor.leftUnitor _) ≪≫
    systemSingleBelow S T B n h

/-- Ordinary singleton extension preserves flat-term K-flat complexes on the whole
ringed sequence site. -/
theorem singletonSequenceOrdinary_kFlat (n : ℕ)
    (P : CochainComplex (systemLevel B n) ℤ) (hP : systemLevelKFlat B n P) :
    CochainComplex.IsKFlatIndependentCoefficients (R := systemSequenceRing B)
      (((singletonSequenceOrdinary S T B n).mapHomologicalComplex (.up ℤ)).obj P) ∧
    (∀ i : ℤ, IsFlatOnSite (R := systemSequenceRing B)
      ((singletonSequenceOrdinary S T B n).obj (P.X i))) := by
  refine systemSequence_kFlat_of_evaluations B _ fun m ↦ ?_
  by_cases hm : m ≤ n
  · let A := S (B.map (homOfLE hm).op)
    have ht := isKFlat_ringedToposPullback (𝟭 _) (𝟭 _) Adjunction.id
      (singletonIdentityPullback (B.obj (op n))) (B.map (homOfLE hm).op) A.model.E
      A.model.obj_eq A.model.map_eq P hP.1 hP.2
    let ec := (Functor.mapHomologicalComplexCompIso
      (singletonSequenceOrdinaryBelow S T B n hm) (.up ℤ)).app P
    exact ⟨kFlat_iso_independent (B.obj (op m)) ec.symm ht.1,
      fun i ↦ flatOnSite_of_iso (B.obj (op m))
        ((HomologicalComplex.eval _ (.up ℤ) i).mapIso ec.symm) (ht.2 i)⟩
  · refine kFlat_of_isZero (B.obj (op m)) _ fun i ↦ ?_
    exact (systemSingleLevelAbove S B n (P.X i) (Nat.lt_of_not_ge hm)).of_iso
      ((systemEvaluation B m).mapIso ((strictSystemSequenceEquivalence B).unitIso.symm.app
        ((systemSingleFunctor S T B n).obj (P.X i))))

end SheafOfModules
