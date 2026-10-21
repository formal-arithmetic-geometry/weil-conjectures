/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.Paper.AdmissibleLattices
public import Sheaf.Paper.SbcCompletedOperations
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.CategoryTheory.ScalarLocalization
import Sheaf.Paper.AdicSmoothBaseChange
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Mathlib.GroupTheory.PGroup
import all Sheaf.Paper.PbcFinitePullbackConstructibility
import Sheaf.Paper.ProEtaleLisseFiniteModelsFromLisse
import Sheaf.AlgebraicGeometry.FiniteCoefficientRealizationDirectImage

/-! # Smooth base change with finite-extension rational coefficients
Source: blueprint, sec-smooth-base-change/sk-rem-rest, order 1445
(blueprint: sbc-thm-e-coefficient-smooth-base-change).
The exchange lives in the raw rationalization of the ambient complete category.
Constructible landing is represented through the fully faithful integral inclusion
and the specified lattice presentation. It makes no integral constructibility claim
about an arbitrary representative merely rationally isomorphic to a constructible one.

## Main statements

- `sbcRationalExchange`: the localized canonical integral mate.
- `sbcTransportedExchange`: transport along a specified presentation.
- `eCoefficientSmoothBaseChange`: invertibility, independence and constructible landing.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct

/-- Right derivation transports a square with an equivalent source and an exact target. -/
@[irreducible] private def deriveRightSquare
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory C'] [HasDerivedCategory D']
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions C']
    (F : C ⥤ D) (G : C' ⥤ D') (E : C ⥤ C') (H : D ⥤ D')
    [F.Additive] [G.Additive] [E.Additive] [H.Additive] [E.IsEquivalence]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (i : F ⋙ H ≅ E ⋙ G) :
    F.rightDerivedFunctor ⋙ H.mapDerivedCategory ≅
      E.mapDerivedCategory ⋙ G.rightDerivedFunctor :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F H).symm ≪≫
    Functor.rightDerivedFunctorNatIso i ≪≫ Functor.rightDerivedFunctorCompIso E G ≪≫
      Functor.isoWhiskerRight E.rightDerivedFunctorIsoMapDerivedCategory G.rightDerivedFunctor

@[irreducible] private def cancelTwoEquivalences
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    (L : C ⥤ D) (R : D ⥤ C) (L' : E ⥤ F) (R' : F ⥤ E) (G : C ⥤ E)
    (i : L ⋙ R ≅ 𝟭 C) (j : L' ⋙ R' ≅ 𝟭 E) :
    L ⋙ R ⋙ G ⋙ L' ⋙ R' ≅ G :=
  Functor.isoWhiskerRight i (G ⋙ L' ⋙ R') ≪≫ Functor.leftUnitor _ ≪≫
    Functor.isoWhiskerLeft G j ≪≫ Functor.rightUnitor G

namespace AlgebraicGeometry.Scheme

/-- The two specified coefficient normalizations agree on constant sections. -/
private theorem sbcPresentationScalars (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    adicLisseConstantUnit W (ProEtale.PbcQuotient d n) ≫
      ((adicLisseForget W).map (pbcLevelConstantComparison W d n).hom).hom =
        pbcFunctionScalars W d n := by
  let P := ProEtale.PbcQuotient d n
  let c := AdicCoefficients.finiteRingComparison W P
  have hη := (AdicCoefficients.finiteRingComparison_exists W P).choose_spec.1.2
  have hc (U : W.ProEtᵒᵖ) (b : P) :=
    (pbcLevelConstantComparison_exists W d n).exists.choose_spec U b
  ext U b
  apply (ConcreteCategory.bijective_of_isIso (c.hom.hom.app U)).1
  change c.hom.hom.app U
      ((pbcLevelConstantComparison W d n).hom.hom.app U
        ((toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj
          (CommRingCat.of P))).app U b)) =
    c.hom.hom.app U (c.inv.hom.app U ((ProEtale.finiteCoefficientScalarMap W P).app U b))
  have hinv := congrArg (fun k : AdicCoefficients.finiteRingPresentation W P ⟶
      AdicCoefficients.finiteRingPresentation W P ↦
        k.hom.app U ((ProEtale.finiteCoefficientScalarMap W P).app U b)) c.inv_hom_id
  change c.hom.hom.app U (c.inv.hom.app U _) = _ at hinv
  rw [hinv]
  erw [hc]
  exact ConcreteCategory.congr_hom (congr_app hη U)
    ((AdicCoefficients.constants W P).app U b)

@[irreducible] private def sbcPresentationUnit (W : Scheme.{u}) (P : Type (u + 1)) [CommRing P]
    (R : Sheaf (ProEt.topology W) RingCat.{u + 1})
    (α : (Functor.const W.ProEtᵒᵖ).obj (RingCat.of P) ⟶ R.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology W) α]
    [Presheaf.IsLocallySurjective (ProEt.topology W) α] :
    pbcAssociatedModule W P R α ⋙
      ConstantScalarComparison.restriction (ProEt.topology W) P R α ≅ 𝟭 _ := by
  let B := scalarEmbedding W P
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} α
  let η := Functor.whiskerLeft B adj.unit
  have hi (F : Sheaf (ProEt.topology W) (ModuleCat.{u + 1} P)) : IsIso (η.app F) := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    change IsIso (toSheafify (ProEt.topology W) _)
    exact isIso_toSheafify (ProEt.topology W)
      ((sheafCompose (ProEt.topology W)
        (forget₂ (ModuleCat.{u + 1} P) AddCommGrpCat.{u + 1})).obj F).property
  have : IsIso η := NatIso.isIso_of_isIso_app η
  exact (Functor.fullyFaithfulCancelRight B (asIso η)).symm

/-- View a finite function-coefficient module as a fixed-coefficient sheaf. -/
private abbrev sbcFiniteView (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :=
  pbcRestrict (pbcLevelConstantComparison W d n).hom ⋙
    scalarRestriction W (ProEtale.PbcQuotient d n)

@[irreducible] private def sbcFiniteViewUnit (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    pbcFunctionRealization W d n ⋙ sbcFiniteView W d n ≅ 𝟭 _ := by
  let P := ProEtale.PbcQuotient d n
  let C := pbcAssociatedModule W P ((adicLisseForget W).obj (adicLisseConstantRing W P))
    (adicLisseConstantUnit W P)
  have h := pbcAssociatedRestriction_exists W P P
    ((adicLisseForget W).obj (adicLisseConstantRing W P))
    ((adicLisseForget W).obj ((pbcAdicRings W d).obj (op n)))
    (adicLisseConstantUnit W P) (pbcFunctionScalars W d n) (RingHom.id P)
    ((adicLisseForget W).map (pbcLevelConstantComparison W d n).hom)
    (by simpa using sbcPresentationScalars W d n)
  let i : C ≅ pbcFunctionRealization W d n ⋙
      pbcRestrict (pbcLevelConstantComparison W d n).hom := h.exists.choose
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight i.symm (scalarRestriction W P) ≪≫
      sbcPresentationUnit W P _ (adicLisseConstantUnit W P)

private instance sbcFiniteView_equivalence (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (sbcFiniteView W d n).IsEquivalence := by
  have : (pbcFunctionRealization W d n ⋙ sbcFiniteView W d n).IsEquivalence :=
    Functor.isEquivalence_of_iso (sbcFiniteViewUnit W d n).symm
  exact Functor.isEquivalence_of_comp_left (pbcFunctionRealization W d n)
    (sbcFiniteView W d n)

private instance sbcFiniteView_additive (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (sbcFiniteView W d n).Additive := by
  constructor
  intro M N a b
  ext U m
  rfl

-- Name exactness once, so derived comparisons do not repeatedly synthesize its proof.
private instance sbcFiniteView_limits (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    PreservesFiniteLimits (sbcFiniteView W d n) := inferInstance

private instance sbcFiniteView_colimits (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    PreservesFiniteColimits (sbcFiniteView W d n) := inferInstance

@[irreducible] private def sbcViewPullOrdinary {V W : Scheme.{u}} (q : W ⟶ V)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    proEtaleRingModulePullback q ((pbcAdicRings V d).obj (op n))
        ((pbcAdicRings W d).obj (op n)) (asIso (completedFiniteCoefficientMap q d n)) ⋙
      sbcFiniteView W d n ≅
    sbcFiniteView V d n ⋙ ProEtale.upperStar
      (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) q := by
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (levelPullbackEncoding q d n).symm _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
        (pullbackEncoding q (ProEtale.PbcQuotient d n)) ≪≫
          (Functor.associator _ _ _).symm

@[irreducible] private def sbcViewPushOrdinary {V W : Scheme.{u}} (q : W ⟶ V)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    proEtaleRingModuleDirectImage q ((pbcAdicRings V d).obj (op n))
        ((pbcAdicRings W d).obj (op n)) (asIso (completedFiniteCoefficientMap q d n)) ⋙
      sbcFiniteView V d n ≅
    sbcFiniteView W d n ⋙ ProEtale.lowerStar
      (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) q := by
  let P := ProEtale.PbcQuotient d n
  have hc : (constantCoefficients q P).hom ≫ (pbcLevelConstantComparison W d n).hom =
      (proEtaleSheafInverseImage q CommRingCat.{u + 1}).map
        (pbcLevelConstantComparison V d n).hom ≫ completedFiniteCoefficientMap q d n := by
    simp only [constantCoefficients, asIso_hom, completedFiniteCoefficientMap,
      ← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
    have hid := (proEtaleSheafInverseImage q CommRingCat.{u + 1}).map_id
      (adicLisseConstantRing V P)
    erw [hid]
    rfl
  let c := proEtaleRingRestrictionDirectImage q _ _ _ _
    (pbcLevelConstantComparison V d n).hom (pbcLevelConstantComparison W d n).hom
    (constantCoefficients q P) (asIso (completedFiniteCoefficientMap q d n)) hc
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight c _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (directImageEncoding q P) ≪≫
        (Functor.associator _ _ _).symm

@[irreducible] private def sbcViewPull {V W : Scheme.{u}} (q : W ⟶ V)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    proEtaleRingDerivedPullback q ((pbcAdicRings V d).obj (op n))
        ((pbcAdicRings W d).obj (op n)) (asIso (completedFiniteCoefficientMap q d n)) ⋙
      (sbcFiniteView W d n).mapDerivedCategory ≅
    (sbcFiniteView V d n).mapDerivedCategory ⋙
      (ProEtale.upperStar (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) q).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (sbcViewPullOrdinary q d n) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

@[irreducible] private def sbcViewPush {V W : Scheme.{u}} (q : W ⟶ V)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    proEtaleRingDerivedDirectImage q ((pbcAdicRings V d).obj (op n))
        ((pbcAdicRings W d).obj (op n)) (asIso (completedFiniteCoefficientMap q d n)) ⋙
      (sbcFiniteView V d n).mapDerivedCategory ≅
    (sbcFiniteView W d n).mapDerivedCategory ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) q).rightDerivedFunctor :=
  deriveRightSquare _ _ _ _ (sbcViewPushOrdinary q d n)

@[irreducible] private def sbcViewInverse (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (pbcDerivedFunctionRealization W d n).asEquivalence.inverse ≅
      (sbcFiniteView W d n).mapDerivedCategory := by
  let E := (pbcDerivedFunctionRealization W d n).asEquivalence
  let G := (sbcFiniteView W d n).mapDerivedCategory
  let i : E.functor ⋙ G ≅ 𝟭 _ :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (sbcFiniteViewUnit W d n) ≪≫
        Functor.mapDerivedCategoryIdIso _
  exact (Functor.rightUnitor E.inverse).symm ≪≫
    Functor.isoWhiskerLeft E.inverse i.symm ≪≫ E.invFunIdAssoc G

@[irreducible] private def sbcRealizationUnit (W : Scheme.{u}) (P : Type (u + 1))
    [CommRing P] [Finite P] [TopologicalSpace P] [DiscreteTopology P] :
    (ProEtale.finiteCoefficientRealization W P).mapDerivedCategory ⋙
      (ProEtale.finiteCoefficientUnrealization W P).mapDerivedCategory ≅ 𝟭 _ :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (ProEtale.finiteCoefficientRealization W P).asEquivalence.unitIso.symm ≪≫
        Functor.mapDerivedCategoryIdIso _

/-- Cancel finite realization to identify the witness pushforward with derived lowerStar. -/
@[irreducible] private def sbcWitnessPushEncoding {V W : Scheme.{u}} (q : W ⟶ V)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    ProEtale.pbcWitnessDirectImage q d n ≅
      (ProEtale.lowerStar
        (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) q).rightDerivedFunctor := by
  let P := ProEtale.PbcQuotient d n
  let R := (ProEtale.lowerStar (ModuleCat.{u + 1} P) q).rightDerivedFunctor
  let i := deriveRightSquare _ _ _ _
    (ProEtale.finiteCoefficientRealization_directImage q P).some.symm
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight i.symm _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft R (sbcRealizationUnit V P) ≪≫ Functor.rightUnitor R

@[irreducible] private def sbcWitnessPullEncoding {V W : Scheme.{u}} (q : W ⟶ V)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    ProEtale.pbcWitnessPullback q d n ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) q).mapDerivedCategory := by
  let P := ProEtale.PbcQuotient d n
  let F := ProEtale.upperStar (ModuleCat.{u + 1} P) q
  let RV := ProEtale.finiteCoefficientRealization V P
  let UV := ProEtale.finiteCoefficientUnrealization V P
  let RW := ProEtale.finiteCoefficientRealization W P
  let UW := ProEtale.finiteCoefficientUnrealization W P
  let i : (ProEtale.finiteCoefficientPullback V P q).mapDerivedCategory ≅
      UV.mapDerivedCategory ⋙ F.mapDerivedCategory ⋙ RW.mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIso UV (F ⋙ RW) ≪≫
      Functor.isoWhiskerLeft UV.mapDerivedCategory (Functor.mapDerivedCategoryCompIso F RW)
  exact Functor.isoWhiskerRight (Functor.isoWhiskerLeft RV.mapDerivedCategory i)
      UW.mapDerivedCategory ≪≫ cancelTwoEquivalences _ _ _ _ _
        (sbcRealizationUnit V P) (sbcRealizationUnit W P)

@[irreducible] private def sbcFixedPush {V W : Scheme.{u}} (q : W ⟶ V)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    proEtaleRingDerivedDirectImage q ((pbcAdicRings V d).obj (op n))
        ((pbcAdicRings W d).obj (op n)) (asIso (completedFiniteCoefficientMap q d n)) ⋙
      (sbcFiniteView V d n).mapDerivedCategory ≅
    (sbcFiniteView W d n).mapDerivedCategory ⋙ ProEtale.pbcWitnessDirectImage q d n :=
  sbcViewPush q d n ≪≫ Functor.isoWhiskerLeft _ (sbcWitnessPushEncoding q d n).symm

@[irreducible] private def sbcFixedPull {V W : Scheme.{u}} (q : W ⟶ V)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    proEtaleRingDerivedPullback q ((pbcAdicRings V d).obj (op n))
        ((pbcAdicRings W d).obj (op n)) (asIso (completedFiniteCoefficientMap q d n)) ⋙
      (sbcFiniteView W d n).mapDerivedCategory ≅
    (sbcFiniteView V d n).mapDerivedCategory ⋙ ProEtale.pbcWitnessPullback q d n :=
  sbcViewPull q d n ≪≫ Functor.isoWhiskerLeft _ (sbcWitnessPullEncoding q d n).symm

/-- Transfer constructibility and the same vanishing interval through the coefficient view. -/
private theorem sbcFiniteWindow (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (J : DerivedCategory (pbcModules W ((pbcAdicRings W d).obj (op n))))
    (K : DerivedCategory (Sheaf (ProEt.topology W)
      (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n))))
    (j : (sbcFiniteView W d n).mapDerivedCategory.obj J ≅ K)
    {a b : ℤ} (hK : sbcIntrinsicConstructibleIn W (ProEtale.PbcQuotient d n) a b K)
    (i : ℤ) :
    IsConstructibleProEtaleCoefficientModuleSheaf W (ProEtale.PbcQuotient d n)
      ((pbcRestrict (pbcLevelConstantComparison W d n).hom).obj
        ((DerivedCategory.homologyFunctor _ i).obj J)) ∧
    ((i < a ∨ b < i) → IsZero
      ((pbcRestrict (pbcLevelConstantComparison W d n).hom).obj
        ((DerivedCategory.homologyFunctor _ i).obj J))) := by
  let c := ((sbcFiniteView W d n).mapDerivedCategoryHomologyFunctorIso i).app J ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso j
  constructor
  · apply (coefficientConstructible_iff W (ProEtale.PbcQuotient d n) _).mpr
    have hc : ProEtale.IsConstructible (ProEtale.PbcQuotient d n)
        ((DerivedCategory.homologyFunctor _ i).obj K) := by
      obtain ⟨S, _, _, h⟩ := (hK i).1
      exact ⟨S, fun j ↦ finite_models_of_fixed_lisse _ _ _ (h j)⟩
    exact ProEtale.isConstructible_of_iso c.symm hc
  · intro hi
    have hz := ((hK i).2 hi).of_iso c
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (scalarRestriction W (ProEtale.PbcQuotient d n)).map_injective
    exact hz.eq_of_src _ _

end AlgebraicGeometry.Scheme

namespace WeilConjectures
private theorem transportExchange {C D : Type*} [Category* C] [Category* D]
    (F G : C ⥤ D) (α : F ⟶ G) {A B : C} (i : A ≅ B) :
    F.map i.inv ≫ α.app A ≫ G.map i.hom = α.app B := by
  rw [← α.naturality i.hom, ← Functor.map_comp_assoc]
  simp

private theorem exchangeRepresentation {C D : Type*} [Category* C] [Category* D]
    (F G : C ⥤ D) (α : F ⟶ G) {I K : C} (i : I ≅ K)
    {A B : D} (a : A ≅ F.obj I) (b : B ≅ G.obj I) (β : A ⟶ B)
    (hβ : β ≫ b.hom = a.hom ≫ α.app I) :
    β ≫ (b ≪≫ G.mapIso i).hom = (a ≪≫ F.mapIso i).hom ≫ α.app K := by
  dsimp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hβ, Category.assoc, ← α.naturality i.hom, ← Category.assoc]

private theorem localizedFunctor_map {R : Type*} [CommRing R] (p : R)
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [Linear R C] [Linear R D] (F : C ⥤ D) [F.Additive] [F.Linear R]
    {A B : C} (m : A ⟶ B) :
    (ScalarLocalization.between R p F).map ((ScalarLocalization.localization R C p).map m) =
      (ScalarLocalization.localization R D p).map (F.map m) := by
  change (ScalarLocalization.betweenHom R p F _ _)
    ((1 : Localization.Away p) ⊗ₜ[R] m) = _
  simp only [ScalarLocalization.betweenHom, LinearMap.baseChange_tmul]
  rfl

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (sq : ChosenCartesianSquare h e f g)

/-- The scalar localization of the left integral composite, on all complete complexes.
Equivalently this is successive rational direct image and rational completed pullback:
both send a tensor r tensor a to r tensor P_f(D_g(a)).
Source: blueprint order 1445 (blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def sbcRationalLeft : PbcRationalComplete l E T ⥤ PbcRationalComplete l E X :=
  ScalarLocalization.between (PbcIntegralRing l E)
    (pbcUniformizer l E) (sbcPush l E g ⋙ sbcPull l E f)

/-- The scalar localization of the right integral composite, without constructibility
assumptions on its outputs. Source: blueprint order 1445
(blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def sbcRationalRight : PbcRationalComplete l E T ⥤ PbcRationalComplete l E X :=
  ScalarLocalization.between (PbcIntegralRing l E)
    (pbcUniformizer l E) (sbcPull l E e ⋙ sbcPush l E h)

/-- Rational exchange is exactly scalar localization of the specified integral mate.
Source: blueprint order 1445 (blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def sbcRationalExchange : sbcRationalLeft l E (f := f) (g := g) ⟶
    sbcRationalRight l E (e := e) (h := h) :=
  ScalarLocalization.betweenNat (PbcIntegralRing l E)
    (pbcUniformizer l E) (sbcExchange l E sq)

/-- Localize an ambient integral complete complex by the same raw construction.
Source: blueprint order 1445 (blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
abbrev sbcCompleteRationalize (W : Scheme.{u}) :=
  ScalarLocalization.localization (PbcIntegralRing l E)
    (PbcComplete l E W) (pbcUniformizer l E)

/-- Transport of the lattice exchange along the specified rational presentation.
Source: blueprint order 1445 (blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def sbcTransportedExchange [IsNoetherian T]
    (hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (hlT : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) {K : PbcRationalConstructible l E T}
    (L : IntegralLattice l E T hT hlT K) :
    (sbcRationalLeft l E (f := f) (g := g)).obj ((pbcRationalInclusion l E T).obj K) ⟶
      (sbcRationalRight l E (e := e) (h := h)).obj ((pbcRationalInclusion l E T).obj K) :=
  (sbcRationalLeft l E (f := f) (g := g)).map
      ((pbcRationalInclusion l E T).map L.rationalization.inv) ≫
    (sbcRationalExchange l E sq).app
      ((sbcCompleteRationalize l E T).obj ((pbcConstructibleInclusion l E T).obj L.integral)) ≫
    (sbcRationalRight l E (e := e) (h := h)).map
      ((pbcRationalInclusion l E T).map L.rationalization.hom)

/-- Constructible landing means a constructible rational isomorphism representing the
ambient exchange, with the endpoints identified using this lattice presentation.
The integral endpoint identifications precede rationalization, so an arbitrary rational
representative is never inferred to have a constructible integral model.
Source: blueprint order 1445 (blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def SbcConstructibleExchangeRepresentation [IsNoetherian T]
    (hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (hlT : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) {K : PbcRationalConstructible l E T}
    (L : IntegralLattice l E T hT hlT K) : Prop :=
  ∃ (J J' : PbcIntegralConstructible l E X)
    (a : (pbcConstructibleInclusion l E X).obj J ≅
      (sbcPull l E f).obj ((sbcPush l E g).obj
        ((pbcConstructibleInclusion l E T).obj L.integral)))
    (b : (pbcConstructibleInclusion l E X).obj J' ≅
      (sbcPush l E h).obj ((sbcPull l E e).obj
        ((pbcConstructibleInclusion l E T).obj L.integral)))
    (β : (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj J ≅
      (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj J'),
    (pbcRationalInclusion l E X).map β.hom ≫
        ((sbcCompleteRationalize l E X).mapIso b ≪≫
          (sbcRationalRight l E (e := e) (h := h)).mapIso
            ((pbcRationalInclusion l E T).mapIso L.rationalization)).hom =
      ((sbcCompleteRationalize l E X).mapIso a ≪≫
        (sbcRationalLeft l E (f := f) (g := g)).mapIso
          ((pbcRationalInclusion l E T).mapIso L.rationalization)).hom ≫
        (sbcRationalExchange l E sq).app ((pbcRationalInclusion l E T).obj K)

set_option linter.unusedSectionVars false in
/-- Pulling an invertible global integer back to every stalk preserves invertibility.
Source: blueprint order 1445, invertibility on every corner in proof step 1
(blueprint: sbc-thm-e-coefficient-smooth-base-change).
Proof: map the global section through q.appTop and the global-to-stalk germ. Ring maps
preserve units and natural-number casts. This also handles an empty source scheme. -/
theorem sbcPrimeUnitOnSource {U V : Scheme.{u}} (q : U ⟶ V)
    (_hl : IsUnit (l : Γ(V, ⊤))) : ∀ t : U, IsUnit (l : U.presheaf.stalk t) := by
  intro t
  simpa only [map_natCast] using
    (_hl.map q.appTop.hom).map (U.presheaf.germ ⊤ t trivial).hom

private theorem sbcTransportedExchange_eq [IsNoetherian T]
    (hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (hlT : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) {K : PbcRationalConstructible l E T}
    (L : IntegralLattice l E T hT hlT K) :
    sbcTransportedExchange l E sq hT hlT L =
      (sbcRationalExchange l E sq).app ((pbcRationalInclusion l E T).obj K) := by
  exact transportExchange _ _ _ ((pbcRationalInclusion l E T).mapIso L.rationalization)

private theorem sbcQuotientCardPow (n : ℕ) :
    ∃ d : ℕ, Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) = l ^ d := by
  have h := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hlmem : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E := by
    apply (h.2.1 _).mpr
    change Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1
    rw [← map_natCast (algebraMap ℚ_[l] E) l]
    change spectralNorm ℚ_[l] E (algebraMap ℚ_[l] E (l : ℚ_[l])) < 1
    rw [spectralNorm_extends]
    exact Padic.norm_natCast_lt_one_iff.mpr (dvd_refl l)
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hlspan : (l : PbcIntegralRing l E) ∈ (pbcIntegralDatum l E).ideal := by
    rw [← hgen] at hlmem
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hlmem
    exact Ideal.mem_span_singleton.mpr ⟨ULift.up a, congrArg ULift.up ha⟩
  have hz : (l : ProEtale.PbcQuotient (pbcIntegralDatum l E) n) ^ (n + 1) = 0 := by
    simpa only [map_pow, map_natCast] using
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hlspan (n + 1)))
  have hp : IsPGroup l (Multiplicative
      (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)) := by
    intro x
    refine ⟨n + 1, ?_⟩
    change (l ^ (n + 1)) • Multiplicative.toAdd x = 0
    rw [nsmul_eq_mul, Nat.cast_pow, hz, zero_mul]
  obtain ⟨d, hd⟩ := hp.exists_card_eq
  exact ⟨d, hd⟩

/-- Smooth base change for E coefficients, including lattice independence and
constructible landing with the specified endpoint identifications.
The integral and rational constructible categories and both lattice predicates are
the landed Q06 declarations. Their full inclusion into the complete category uses the
same completed coefficient ring and published intrinsic predicate. Completed pullback
is the strict tower construction with its maps. No additional universe equality is required.
Source: blueprint order 1445, sec-smooth-base-change/sk-rem-rest
(blueprint: sbc-thm-e-coefficient-smooth-base-change).

Proof: the ring of integers is a Noetherian DVR with finite residue field; its positive
quotients are finite and have two-term finite-free resolutions. Multiplication by a
positive uniformizer power is injective because the valuation ring is a domain, so
these resolutions give perfect quotients. The residue field has characteristic l:
l has absolute value less than one and lies in the maximal ideal. If its cardinality
is l^d, cancellation identifies each successive uniformizer-ideal quotient with that
residue field, giving cardinality l^(d(n+1)) at level n. Its order is invertible on S
by the hypothesis on l, and hence on every corner. This verifies the coefficient
hypotheses of sbc-thm-adic-smooth-base-change, using
lem-weil-l-adic-extension-integers-dvr and lem-weil-valued-dvr-finite-quotients.
The lattice's complete-category membership supplies the compatible etale origins,
and its finite-level admissibility supplies bounded constructible origins. Apply the
adic theorem to this lattice. Its finite-level smooth base change applies
to every bounded constructible étale origin of the lattice reduction. The completed
pullback-reduction and direct-image/derived-limit comparisons identify the completed
integral mate with the derived inverse limit of these finite exchange maps, hence
make it invertible on the lattice. The operations are additive and A-linear, so raw
scalar localization gives the displayed natural transformation and preserves its
inverse. Naturality, followed by cancellation of the two inverse presentation maps,
gives transported exchange = exchange at K; applying the same equality to every
other admissible presentation proves independence.

For square-constructible admissibility, the four finite systems share one window.
Their canonical quotient-linear comparisons are the actual reductions of the four
completed integral outputs. Normalized constructible local effectivity supplies the
uniform stratified local models and bounded étale origins for the two X endpoints.
Lift each quotient normalization to its étale origin using full faithfulness on D+;
the normalization cocycle and faithfulness give the witness cocycle. Thus both integral
endpoints are in the published bounded constructible complete subcategory. Its full
inclusion remains fully faithful after tensoring Hom groups. The localized exchange
and its inverse are consequently an isomorphism of the rational constructible
endpoints. Composing their endpoint identifications with the given presentation gives
the equality required by SbcConstructibleExchangeRepresentation. -/
theorem eCoefficientSmoothBaseChange
    [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
    [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    (_hX : ∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (_hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (_hl : IsUnit (l : Γ(S, ⊤)))
    (K : PbcRationalConstructible l E T)
    (L : IntegralLattice l E T _hT (sbcPrimeUnitOnSource l g _hl) K)
    (_hL : L.IsFiniteLevelEtaleAdmissible l E T _hT (sbcPrimeUnitOnSource l g _hl)) :
    IsIso ((sbcRationalExchange l E sq).app ((pbcRationalInclusion l E T).obj K)) ∧
    (sbcTransportedExchange l E sq _hT (sbcPrimeUnitOnSource l g _hl) L =
      (sbcRationalExchange l E sq).app ((pbcRationalInclusion l E T).obj K)) ∧
    (∀ L' : IntegralLattice l E T _hT (sbcPrimeUnitOnSource l g _hl) K,
      L'.IsFiniteLevelEtaleAdmissible l E T _hT (sbcPrimeUnitOnSource l g _hl) →
      sbcTransportedExchange l E sq _hT (sbcPrimeUnitOnSource l g _hl) L' =
        sbcTransportedExchange l E sq _hT (sbcPrimeUnitOnSource l g _hl) L) ∧
    (L.IsSquareConstructiblyAdmissible l E T _hT (sbcPrimeUnitOnSource l g _hl) sq →
      SbcConstructibleExchangeRepresentation l E sq _hT (sbcPrimeUnitOnSource l g _hl) L) := by
  have horder (n : ℕ) := sbcQuotientCardPow l E n
  have hunit (W : Scheme.{u}) (q : W ⟶ S) (n : ℕ) :
      IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(W, ⊤)) := by
    obtain ⟨d, hd⟩ := horder n
    rw [hd, Nat.cast_pow]
    have hu : IsUnit (l : Γ(W, ⊤)) := by
      simpa only [map_natCast] using _hl.map q.appTop.hom
    exact hu.pow d
  have horigin (n : ℕ) := _hL n
  have horigin' (n : ℕ) :
      ∃ M : Etale.BoundedConstructibleDerivedCategory
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) T,
        Nonempty ((pbcDerivedFunctionRealization T (pbcIntegralDatum l E) n).obj
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1}
              (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)) T).mapDerivedCategory.obj M.obj) ≅
          (sbcReduction l E T n).obj L.integral.obj) := by
    obtain ⟨M, ⟨i⟩⟩ := horigin n
    exact ⟨M, ⟨(pbcDerivedFunctionRealization T (pbcIntegralDatum l E) n).mapIso i ≪≫
      (pbcDerivedFunctionRealization T (pbcIntegralDatum l E) n).asEquivalence.counitIso.app
        ((sbcReduction l E T n).obj L.integral.obj)⟩⟩
  obtain ⟨hint, hlanding⟩ := adicSmoothBaseChange l E sq _hT _hl
    (fun n ↦ ⟨hunit S (𝟙 S) n,
      hunit X f n, hunit T g n, hunit Y (e ≫ g) n⟩) L.integral horigin'
  have hlocalized : IsIso ((sbcRationalExchange l E sq).app
      ((sbcCompleteRationalize l E T).obj
        ((pbcConstructibleInclusion l E T).obj L.integral))) := by
    change IsIso ((sbcCompleteRationalize l E X).map
      (sbcExchangeApp l E sq ((pbcConstructibleInclusion l E T).obj L.integral)))
    exact Functor.map_isIso _ _
  have htransport := sbcTransportedExchange_eq l E sq _hT
    (sbcPrimeUnitOnSource l g _hl) L
  have hrat : IsIso ((sbcRationalExchange l E sq).app
      ((pbcRationalInclusion l E T).obj K)) := by
    rw [← htransport]
    unfold sbcTransportedExchange
    infer_instance
  refine ⟨hrat, htransport, ?_, ?_⟩
  · intro L' _
    exact (sbcTransportedExchange_eq l E sq _hT (sbcPrimeUnitOnSource l g _hl) L').trans
      htransport.symm
  · intro hsq
    have hwindow := hsq.2
    obtain ⟨a₀, b₀, hab, hwindow⟩ := hwindow
    obtain ⟨hB, hD, hiso⟩ := hlanding _hX (by
      refine ⟨a₀, b₀, hab, ?_⟩
      intro n i
      let d := pbcIntegralDatum l E
      let M := (sbcReduction l E T n).obj L.integral.obj
      let r : (sbcFiniteView T d n).mapDerivedCategory.obj M ≅
          L.reduction l E T _hT (sbcPrimeUnitOnSource l g _hl) n :=
        ((sbcViewInverse T d n).app M).symm
      let r₁ := (sbcFixedPush g d n).app M ≪≫
        (ProEtale.pbcWitnessDirectImage g d n).mapIso r
      let r₂ := (sbcFixedPull f d n).app ((sbcFinitePush l E g n).obj M) ≪≫
        (ProEtale.pbcWitnessPullback f d n).mapIso r₁
      let r₃ := (sbcFixedPull e d n).app M ≪≫
        (ProEtale.pbcWitnessPullback e d n).mapIso r
      let r₄ := (sbcFixedPush h d n).app ((sbcFinitePull l E e n).obj M) ≪≫
        (ProEtale.pbcWitnessDirectImage h d n).mapIso r₃
      exact ⟨sbcFiniteWindow S d n _ _ r₁ (hwindow n).1 i,
        sbcFiniteWindow X d n _ _ r₂ (hwindow n).2.1 i,
        sbcFiniteWindow Y d n _ _ r₃ (hwindow n).2.2.1 i,
        sbcFiniteWindow X d n _ _ r₄ (hwindow n).2.2.2 i⟩)
    let J : PbcIntegralConstructible l E X := ⟨_, hB⟩
    let J' : PbcIntegralConstructible l E X := ⟨_, hD⟩
    let m : J ⟶ J' := ObjectProperty.homMk
      (sbcExchangeApp l E sq ((pbcConstructibleInclusion l E T).obj L.integral)).hom
    have hm : IsIso m := hiso
    let a : (pbcConstructibleInclusion l E X).obj J ≅
        (sbcPull l E f).obj ((sbcPush l E g).obj
          ((pbcConstructibleInclusion l E T).obj L.integral)) := Iso.refl _
    let b : (pbcConstructibleInclusion l E X).obj J' ≅
        (sbcPush l E h).obj ((sbcPull l E e).obj
          ((pbcConstructibleInclusion l E T).obj L.integral)) := Iso.refl _
    refine ⟨J, J', a, b,
      (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).mapIso
        (asIso m), ?_⟩
    apply exchangeRepresentation (sbcRationalLeft l E) (sbcRationalRight l E)
      (sbcRationalExchange l E sq) ((pbcRationalInclusion l E T).mapIso L.rationalization)
    have hmap := localizedFunctor_map (pbcUniformizer l E)
      (pbcConstructibleInclusion l E X) m
    change (pbcRationalInclusion l E X).map
        ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map m) ≫
        (sbcCompleteRationalize l E X).map b.hom =
      (sbcCompleteRationalize l E X).map a.hom ≫ _
    calc
      _ = (pbcRationalInclusion l E X).map
          ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map m) :=
        (sbcCompleteRationalize l E X).map_id _ ▸ Category.comp_id _
      _ = _ := hmap
      _ = _ := (sbcCompleteRationalize l E X).map_id _ ▸ (Category.id_comp _).symm

end WeilConjectures

end
