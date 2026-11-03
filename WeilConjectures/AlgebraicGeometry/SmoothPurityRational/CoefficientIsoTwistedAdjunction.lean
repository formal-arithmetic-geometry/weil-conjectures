/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.ShriekCoefficientIsomorphism
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude

/-! # Transport of twisted pullback along a coefficient isomorphism

Source: integral-adjunction-bijection, coefficient presentations in the Purity paragraph.
(blueprint: lem-sp-rational-coefficient-iso-twisted-adjunction)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SmoothPurityRational

variable {A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj A] [MonObj B] [IsCommMonObj A] [IsCommMonObj B]

private instance coefficientConstructibleReplete
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u}) :
    (constantModelBoundedConstructible R T).IsClosedUnderIsomorphisms :=
  (constantModelConstructibleFiniteTor_wellDefined R T).2.1

/-- The literal uncompleted pullback, tensor by the specified single, and shift.
Source: integral smooth purity source
(blueprint: lem-sp-rational-coefficient-iso-twisted-adjunction).
-/
def coefficientTwistedSource {X Y : Scheme.{u}} (A :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    (f : X ⟶ Y) (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj A X)) (n : ℤ) :=
  (CondensedRing.upperStar A f).mapDerivedCategory ⋙
    tensorRight ((DerivedCategory.singleFunctor _ 0).obj L) ⋙ shiftFunctor _ n

set_option maxHeartbeats 4000000 in
-- The comparison shares large derived tensor and exact functor instances.
/-- Scalar transport takes this source to the source with the transported line.
Source: integral-adjunction-bijection, Purity, fixed coefficient presentation
(blueprint: lem-sp-rational-coefficient-iso-twisted-adjunction).
Proof: extension along a ring isomorphism is its exact inverse scalar restriction.
Its counit carries the prescribed line comparison to the new line. Derive its
single comparison, then use the monoidal derived extension, canonical pullback
comparison and shift comparison. Each constituent is a natural isomorphism. -/
def coefficientTwistedSourceIso (e : Mon.mk A ≅ Mon.mk B)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A X))
    (L' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (hL : L ≅ (Mod.comap (coefficientMap e.hom.hom X)).obj L') (n : ℤ) :
    coefficientTwistedSource A f L n ⋙ shriekCoefficientTransport e X ≅
      shriekCoefficientTransport e Y ⋙ coefficientTwistedSource B f L' n := by
  have : IsIso e.hom.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.hom))
  have hi (T : Scheme.{u}) :
      (asIso (coefficientMap e.hom.hom T)).inv = coefficientMap e.inv.hom T := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [← coefficientMap_comp]
    change coefficientMap ((Mon.forget _).map (e.hom ≫ e.inv)) T = _
    rw [Iso.hom_inv_id]
    exact coefficientMap_id T
  let FX := Mod.extendScalars (coefficientMap e.hom.hom X)
  let FY := Mod.extendScalars (coefficientMap e.hom.hom Y)
  have hx (T : Scheme.{u}) :
      (Mod.extendScalars (coefficientMap e.hom.hom T)).IsEquivalence := by
    have : (Mod.comap (asIso (coefficientMap e.hom.hom T)).inv).IsEquivalence :=
      (inferInstance : (Mod.comapEquivalenceOfIsIso
        (coefficientMap e.hom.hom T)).inverse.IsEquivalence)
    exact Functor.isEquivalence_of_iso (Mod.extendScalarsIsoComapInv _).symm
  have : FX.IsEquivalence := hx X
  have : FY.IsEquivalence := hx Y
  let LX := FX.leftDerivedFunctor
  let LY := FY.leftDerivedFunctor
  letI : LX.CommShift ℤ :=
    Functor.CommShift.ofIso FX.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  let UX := (CondensedRing.upperStar A f).mapDerivedCategory
  let UY := (CondensedRing.upperStar B f).mapDerivedCategory
  let T := (DerivedCategory.singleFunctor _ 0).obj L
  let T' := (DerivedCategory.singleFunctor _ 0).obj L'
  let ux : LX ≅ shriekCoefficientTransport e X :=
    FX.leftDerivedFunctorIsoMapDerivedCategory ≪≫
      Functor.mapDerivedCategoryNatIso
        (Mod.extendScalarsIsoComapInv _ ≪≫ Mod.comapCongr (hi X))
  let uy : LY ≅ shriekCoefficientTransport e Y :=
    FY.leftDerivedFunctorIsoMapDerivedCategory ≪≫
      Functor.mapDerivedCategoryNatIso
        (Mod.extendScalarsIsoComapInv _ ≪≫ Mod.comapCongr (hi Y))
  have : (Mod.comap (coefficientMap e.hom.hom X)).IsEquivalence :=
    (inferInstance : (Mod.comapEquivalenceOfIsIso
      (coefficientMap e.hom.hom X)).functor.IsEquivalence)
  let line : FX.obj L ≅ L' := FX.mapIso hL ≪≫
    asIso ((Mod.extendRestrictAdjunction (coefficientMap e.hom.hom X)).counit.app L')
  let lineD : LX.obj T ≅ T' :=
    FX.leftDerivedFunctorIsoMapDerivedCategory.app T ≪≫
      (FX.mapDerivedCategorySingleFunctor 0).app L ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso line
  have : FX.Monoidal := Mod.extendScalarsMonoidal _
  have : FX.PreservesFlat := Mod.preservesFlat_extendScalars _
  have : LX.Monoidal := FX.leftDerivedFunctorMonoidal
  let et : tensorRight T ⋙ LX ≅ LX ⋙ tensorRight T' :=
    (Functor.Monoidal.commTensorRight LX T).symm ≪≫
      Functor.isoWhiskerLeft LX ((curriedTensor _).flip.mapIso lineD)
  let ep : UX ⋙ LX ≅ LY ⋙ UY :=
    Functor.isoWhiskerRight
      (CondensedRing.upperStar A f).leftDerivedFunctorIsoMapDerivedCategory.symm LX ≪≫
      CondensedRing.derivedPullIso e.hom.hom f ≪≫
        Functor.isoWhiskerLeft LY
          (CondensedRing.upperStar B f).leftDerivedFunctorIsoMapDerivedCategory
  let a : coefficientTwistedSource A f L n ⋙ LX ≅
      LY ⋙ coefficientTwistedSource B f L' n :=
    Functor.isoWhiskerRight (Functor.associator UX (tensorRight T) (shiftFunctor _ n)) LX ≪≫
      Functor.associator UX _ LX ≪≫
      Functor.isoWhiskerLeft UX
        (Functor.associator (tensorRight T) _ LX ≪≫
          Functor.isoWhiskerLeft (tensorRight T) (LX.commShiftIso n) ≪≫
          (Functor.associator (tensorRight T) LX _).symm ≪≫
          Functor.isoWhiskerRight et _) ≪≫
      (Functor.associator UX (LX ⋙ tensorRight T') _).symm ≪≫
      Functor.isoWhiskerRight
        ((Functor.associator UX LX _).symm ≪≫ Functor.isoWhiskerRight ep _ ≪≫
          Functor.associator LY UY _) _ ≪≫
      Functor.associator LY _ _
  exact Functor.isoWhiskerLeft _ ux.symm ≪≫ a ≪≫ Functor.isoWhiskerRight uy _

private def coefficientRoundTrip (e : Mon.mk A ≅ Mon.mk B) (T : Scheme.{u}) :
    shriekCoefficientTransport e T ⋙ shriekCoefficientTransport e.symm T ≅ 𝟭 _ := by
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((Mod.comapComp _ _).symm ≪≫ Mod.comapCongr (by
        change (upperStarFromPoint T).map e.hom.hom ≫
          (upperStarFromPoint T).map e.inv.hom = 𝟙 _
        rw [← Functor.map_comp]
        change (upperStarFromPoint T).map ((Mon.forget _).map (e.hom ≫ e.inv)) = _
        simp only [Iso.hom_inv_id]
        exact (upperStarFromPoint T).map_id A) ≪≫ Mod.comapId _) ≪≫
    Functor.mapDerivedCategoryIdIso _

private theorem boundedCoefficientIso (e : Mon.mk A ≅ Mon.mk B)
    (T : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj A T))) (hK : constantModelBoundedConstructible A T K) :
    constantModelBoundedConstructible B T ((shriekCoefficientTransport e T).obj K) := by
  let φ := (upperStarFromPoint T).map e.inv.hom
  have : IsIso e.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  have : IsIso φ := inferInstanceAs (IsIso ((upperStarFromPoint T).map e.inv.hom))
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) φ
  refine ⟨F.bounded_mapDerivedCategory_obj hK.1, ?_⟩
  intro n
  exact constructible_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K)
    (constructible_comap (Λ := A) (Λ' := B) e.inv.hom T _ (hK.2 n))

private def coefficientBoundedEquivalence (e : Mon.mk A ≅ Mon.mk B)
    (T : Scheme.{u}) :
    ConstantModelBoundedConstructible A T ≌ ConstantModelBoundedConstructible B T := by
  have := (shriekCoefficientIso_transport e T).1
  have hb (K) : constantModelBoundedConstructible A T K ↔
      constantModelBoundedConstructible B T ((shriekCoefficientTransport e T).obj K) := by
    constructor
    · exact boundedCoefficientIso e T K
    · intro hK
      exact ObjectProperty.prop_of_iso _ ((coefficientRoundTrip e T).app K)
        (boundedCoefficientIso e.symm T _ hK)
  exact (shriekCoefficientTransport e T).asEquivalence.congrFullSubcategory
    (by funext K; exact propext (hb K).symm)

/-- An integral twisted adjunction survives a change of coefficient presentation.
Source: integral-adjunction-bijection, fixed coefficient presentations
(blueprint: lem-sp-rational-coefficient-iso-twisted-adjunction).
Proof: exact restriction along the inverse ring isomorphism gives equivalences
on Dbc. The compact-support comparison and the preceding twisted-source comparison
commute with these equivalences. Essential surjectivity proves preservation by
the new functors. Restrict the comparisons and conjugate the given adjunction
through the two equivalences. Its right functor is the specified twisted pullback.
-/
theorem coefficientIsoTwistedAdjunction (e : Mon.mk A ≅ Mon.mk B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification.BoundaryCompactification f)
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A X))
    (L' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (hL : L ≅ (Mod.comap (coefficientMap e.hom.hom X)).obj L') (n : ℤ)
    (hF : ∀ M : ConstantModelBoundedConstructible A X,
      constantModelBoundedConstructible A Y
        ((CondensedRing.rightDerivedLowerShriekOfCompactification A c.obj.obj).obj M.obj))
    (hJ : ∀ K : ConstantModelBoundedConstructible A Y,
      constantModelBoundedConstructible A X ((coefficientTwistedSource A f L n).obj K.obj))
    (adj : (constantModelBoundedConstructible A Y).lift
        ((constantModelBoundedConstructible A X).ι ⋙
          CondensedRing.rightDerivedLowerShriekOfCompactification A c.obj.obj) hF ⊣
      (constantModelBoundedConstructible A X).lift
        ((constantModelBoundedConstructible A Y).ι ⋙ coefficientTwistedSource A f L n) hJ) :
    ∃ (hF' : ∀ M : ConstantModelBoundedConstructible B X,
      constantModelBoundedConstructible B Y
        ((CondensedRing.rightDerivedLowerShriekOfCompactification B c.obj.obj).obj M.obj))
      (hJ' : ∀ K : ConstantModelBoundedConstructible B Y,
        constantModelBoundedConstructible B X
          ((coefficientTwistedSource B f L' n).obj K.obj)),
      Nonempty ((constantModelBoundedConstructible B Y).lift
        ((constantModelBoundedConstructible B X).ι ⋙
          CondensedRing.rightDerivedLowerShriekOfCompactification B c.obj.obj) hF' ⊣
        (constantModelBoundedConstructible B X).lift
          ((constantModelBoundedConstructible B Y).ι ⋙ coefficientTwistedSource B f L' n) hJ') := by
  let EX := coefficientBoundedEquivalence e X
  let EY := coefficientBoundedEquivalence e Y
  let F := (constantModelBoundedConstructible A Y).lift
    ((constantModelBoundedConstructible A X).ι ⋙
      CondensedRing.rightDerivedLowerShriekOfCompactification A c.obj.obj) hF
  let J := (constantModelBoundedConstructible A X).lift
    ((constantModelBoundedConstructible A Y).ι ⋙ coefficientTwistedSource A f L n) hJ
  let b := shriekCoefficientCompactificationIso e c
  let a := coefficientTwistedSourceIso e f L L' hL n
  have hF' (M : ConstantModelBoundedConstructible B X) :
      constantModelBoundedConstructible B Y
        ((CondensedRing.rightDerivedLowerShriekOfCompactification B c.obj.obj).obj M.obj) := by
    let M0 := EX.inverse.obj M
    let i := (constantModelBoundedConstructible B X).ι.mapIso (EX.counitIso.app M)
    exact ObjectProperty.prop_of_iso _
      (b.app M0.obj ≪≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification B c.obj.obj).mapIso i)
      (EY.functor.obj (F.obj M0)).property
  have hJ' (K : ConstantModelBoundedConstructible B Y) :
      constantModelBoundedConstructible B X
        ((coefficientTwistedSource B f L' n).obj K.obj) := by
    let K0 := EY.inverse.obj K
    let i := (constantModelBoundedConstructible B Y).ι.mapIso (EY.counitIso.app K)
    exact ObjectProperty.prop_of_iso _
      (a.app K0.obj ≪≫ (coefficientTwistedSource B f L' n).mapIso i)
      (EX.functor.obj (J.obj K0)).property
  let F' := (constantModelBoundedConstructible B Y).lift
    ((constantModelBoundedConstructible B X).ι ⋙
      CondensedRing.rightDerivedLowerShriekOfCompactification B c.obj.obj) hF'
  let J' := (constantModelBoundedConstructible B X).lift
    ((constantModelBoundedConstructible B Y).ι ⋙ coefficientTwistedSource B f L' n) hJ'
  let bi : F ⋙ EY.functor ≅ EX.functor ⋙ F' :=
    NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ (b.app M.obj))
      (fun v ↦ by apply ObjectProperty.hom_ext; exact b.hom.naturality v.hom)
  let ai : J ⋙ EX.functor ≅ EY.functor ⋙ J' :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ (a.app K.obj))
      (fun v ↦ by apply ObjectProperty.hom_ext; exact a.hom.naturality v.hom)
  let ad : (EX.inverse ⋙ F) ⋙ EY.functor ⊣ (EY.inverse ⋙ J) ⋙ EX.functor :=
    (EX.symm.toAdjunction.comp adj).comp EY.toAdjunction
  let el : (EX.inverse ⋙ F) ⋙ EY.functor ≅ F' :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft EX.inverse bi ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight EX.counitIso F' ≪≫ Functor.leftUnitor F'
  let er : (EY.inverse ⋙ J) ⋙ EX.functor ≅ J' :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft EY.inverse ai ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight EY.counitIso J' ≪≫ Functor.leftUnitor J'
  exact ⟨hF', hJ', ⟨(ad.ofNatIsoLeft el).ofNatIsoRight er⟩⟩

end AlgebraicGeometry.ProEtale.SmoothPurityRational
