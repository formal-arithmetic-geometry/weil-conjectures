/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S6
-/
module

public import Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion
public import Sheaf.AlgebraicGeometry.IntegralConstantModelRealization
public import Sheaf.Paper.AdicStratifiedPerfectData
import Sheaf.Paper.SmallIntegralRoosComparison
import Sheaf.AlgebraicGeometry.IntegralModelsCompletionTransport
import Sheaf.SixFunctors.ProEtale.InternalCompletionStacksComparison
import WeilConjectures.CategoryTheory.Monoidal.KFlatEquivalence

/-! # Transport of the small integral completion augmentation

Source: Stacks Tags 099B, 0A0E, 0941, 099L and 099M; the integral-heart local-model proof,
clause (2), Completeness.
(blueprint: lem-sfb-small-integral-roos-completeness-transport)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.IntegralConstantModel.pointComparison
  AlgebraicGeometry.ProEtale.IntegralConstantModel.modulesFunctor
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local instance] smallIntegralSheafMonoidal smallIntegralSheafClosed
  smallIntegralModulesMonoidal

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesMonoidal AdicCompletion.modulesSymmetric AdicCompletion.modulesClosed
  AdicCompletion.modulesMonoidalPreadditive AdicCompletion.modulesDerived
  AdicCompletion.modulesProducts AdicCompletion.complexProducts

private instance siteEssentiallySmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _


private def toModelEquivalence (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}) :=
  CategoryTheory.Equivalence.mk
    (Scheme.proEtaleModuleToModel R) (Scheme.proEtaleModuleFromModel R)
    (NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ Iso.refl _))))
    (NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ Iso.refl _))))

private theorem sfbComplete_of_iso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    {K L : DerivedCategory (Scheme.proEtaleRingModules X (Scheme.adicLisseCompletedRing X I))}
    (e : K ≅ L) (hK : Scheme.IsSfbAdicComplete X I K) :
    Scheme.IsSfbAdicComplete X I L := by
  let R := Scheme.adicLisseCompletedRing X I
  let F := Scheme.proEtaleModuleToModel ((Scheme.adicLisseForget X).obj R)
  have : F.Additive := ⟨by intros; ext U x; rfl⟩
  have : F.IsEquivalence := (toModelEquivalence X _).isEquivalence_functor
  let := HasDerivedCategory.standard
    (ConstantCompletion.Mod ((Scheme.sfbModelRings X).obj R))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1}
      (((AsSmall.down : Scheme.proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
        RingCat.{u + 1} (Scheme.proEtaleModelTopology X) (Scheme.ProEt.topology X)).obj
        ((Scheme.adicLisseForget X).obj R)))
  let c (N : DerivedCategory (Scheme.proEtaleRingModules X R)) :
      (ConstantCompletion.Q ((Scheme.sfbModelRings X).obj R)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj (DerivedCategory.Q.objPreimage N)) ≅
        F.mapDerivedCategory.obj N :=
    (F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage N)).symm ≪≫
      F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso N)
  let d := c K ≪≫ F.mapDerivedCategory.mapIso e ≪≫ (c L).symm
  let O := (Scheme.sfbModelRings X).obj R
  let (U : Scheme.proEtaleSiteModel X) :=
    HasDerivedCategory.standard (ConstantCompletion.Mod (O.over U))
  intro U f hf
  let H := (Functor.curry.obj (derivedInternalHom _ (O.over U))).obj
    (Opposite.op ((DerivedCategory.singleFunctor _ 0).obj
      (ringedSectionLocalization (O.over U) (ringedSliceSection O U f))))
  exact (((ringedDerivedRestriction O U ⋙ H).mapIso d).isZero_iff).mp (hK U f hf)

private theorem ordinary_complete_of_sfb
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (F : Type u) [Field F] [Algebra (Padic ℓ) F] [FiniteDimensional (Padic ℓ) F]
    (e : Mon.mk (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E) ≅
      sfbCondensedIntegers ℓ F) (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (SmallAdicCompletion.Modules ℓ E X))
    (hK : Scheme.IsSfbAdicComplete X (IntegralConstantCompletion.ideal ℓ F)
      ((Mod.comap (coefficientMap e.inv.hom X) ⋙
        IntegralConstantModel.modulesFunctor ℓ F X).mapDerivedCategory.obj K)) :
    let G := Mod.comap (coefficientMap (IntegralConstantModel.pointComparison ℓ F).hom.hom X ≫
      coefficientMap e.inv.hom X)
    IsDerivedComplete ℓ F X (G.mapDerivedCategory.obj K) := by
  let S := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (sfbCondensedIntegers ℓ F).X X)
  let R : SmallAdicCompletion.Modules ℓ E X ⥤ S :=
    Mod.comap (coefficientMap e.inv.hom X)
  let a : AdicCompletion.ring ℓ F X ⟶
      condensedRingObj (sfbCondensedIntegers ℓ F).X X :=
    coefficientMap (IntegralConstantModel.pointComparison ℓ F).hom.hom X
  let b : condensedRingObj (sfbCondensedIntegers ℓ F).X X ⟶
      AdicCompletion.ring ℓ F X :=
    coefficientMap (IntegralConstantModel.pointComparison ℓ F).inv.hom X
  let A : S ⥤ AdicCompletion.Modules ℓ F X := Mod.comap a
  let B : AdicCompletion.Modules ℓ F X ⥤ S := Mod.comap b
  have : R.IsEquivalence := (Mod.comapEquivalenceOfIsIso _).isEquivalence_functor
  have : A.IsEquivalence := (Mod.comapEquivalenceOfIsIso _).isEquivalence_functor
  have : B.IsEquivalence := (Mod.comapEquivalenceOfIsIso _).isEquivalence_functor
  have hba : b ≫ a = 𝟙 _ := by
    dsimp only [a, b]
    rw [← coefficientMap_comp]
    have h := congrArg Mon.Hom.hom (IntegralConstantModel.pointComparison ℓ F).inv_hom_id
    simp only [Mon.comp_hom', Mon.id_hom'] at h
    rw [h, coefficientMap_id]
  let c : A ⋙ B ≅ 𝟭 _ :=
    (Mod.comapComp b a).symm ≪≫ Mod.comapCongr hba ≪≫ Mod.comapId _
  let d : A.mapDerivedCategory ⋙ B.mapDerivedCategory ≅ 𝟭 _ :=
    (Functor.mapDerivedCategoryCompIso A B).symm ≪≫
      Functor.mapDerivedCategoryNatIso c ≪≫ Functor.mapDerivedCategoryIdIso _
  let G : SmallAdicCompletion.Modules ℓ E X ⥤ AdicCompletion.Modules ℓ F X :=
    Mod.comap (a ≫ coefficientMap e.inv.hom X)
  let g : G ≅ R ⋙ A := Mod.comapComp a (coefficientMap e.inv.hom X)
  let L := G.mapDerivedCategory.obj K
  let r : B.mapDerivedCategory.obj L ≅ R.mapDerivedCategory.obj K :=
    B.mapDerivedCategory.mapIso
      ((Functor.mapDerivedCategoryNatIso g).app K ≪≫
        (Functor.mapDerivedCategoryCompIso R A).app K) ≪≫
      d.app (R.mapDerivedCategory.obj K)
  let M := IntegralConstantModel.modulesFunctor ℓ F X
  have hR : Scheme.IsSfbAdicComplete X (IntegralConstantCompletion.ideal ℓ F)
      (M.mapDerivedCategory.obj (R.mapDerivedCategory.obj K)) :=
    sfbComplete_of_iso X _ ((Functor.mapDerivedCategoryCompIso R M).app K) hK
  have hL : Scheme.IsSfbAdicComplete X (IntegralConstantCompletion.ideal ℓ F)
      (M.mapDerivedCategory.obj (B.mapDerivedCategory.obj L)) :=
    sfbComplete_of_iso X _ (M.mapDerivedCategory.mapIso r.symm) hR
  apply (internal_completion_stacks_comparison ℓ F X L).mpr
  exact (IntegralModelsStacks.completion_transport ℓ F X).1
    (B.mapDerivedCategory.obj L) |>.mp hL

/-- Local derived completeness in the normalized completed ring-sheaf presentation
implies invertibility of the explicit small-coefficient Roos augmentation.
There is no constructibility or cohomological bound hypothesis.

Source: Stacks Tags 099B, 0A0E, 0941, 099L, 099M; integral-heart-local-model, clause (2),
Completeness.
(blueprint: lem-sfb-small-integral-roos-completeness-transport)

Proof: evaluate e at the one-point profinite set to obtain an isomorphism of the
coefficient DVRs. Naturality at points identifies e on any continuous function with
postcomposition by this isomorphism. It carries the unique maximal ideal, and hence
every positive power of it, to the corresponding ideal. Thus e identifies the finite
quotients, their transition maps and their quotient units. Restriction of scalars along
e and the published section-action equivalence identify derived scalar extension by
these quotients. Pass to the equivalent small ringed site. The constant-completion
equivalence identifies the given local completeness predicate with invertibility of
the canonical quotient-tower completion unit. Take a flat-term K-flat representative
of K; exact coefficient equivalences preserve K-flatness and its derived reductions.
Exact countable products on the pro-etale site identify the derived inverse limit with
the product cone of one minus shift. The normalized unit comparisons identify the map
from the representative with SmallAdicCompletion.augmentation: its first coordinate
is the product of quotient units and its shifted-product coordinate is zero. The
canonical completion unit is invertible, so this augmentation is invertible after Q.
Together with the representative's localization isomorphism these are precisely the
three witnesses required by SmallAdicCompletion.IsDerivedComplete. This works for
unbounded complexes and for the empty scheme. -/
theorem smallIntegralRoosCompletenessTransport
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (F : Type u) [Field F] [Algebra (Padic ℓ) F] [FiniteDimensional (Padic ℓ) F]
    (e : Mon.mk (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E) ≅
      sfbCondensedIntegers ℓ F)
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (SmallAdicCompletion.Modules ℓ E X)) :
    Scheme.IsSfbAdicComplete X (IntegralConstantCompletion.ideal ℓ F)
      ((Mod.comap (coefficientMap e.inv.hom X) ⋙
        IntegralConstantModel.modulesFunctor ℓ F X).mapDerivedCategory.obj K) →
      SmallAdicCompletion.IsDerivedComplete ℓ E X K := by
  intro hK
  let G : SmallAdicCompletion.Modules ℓ E X ⥤ AdicCompletion.Modules ℓ F X :=
    Mod.comap (coefficientMap (IntegralConstantModel.pointComparison ℓ F).hom.hom X ≫
      coefficientMap e.inv.hom X)
  have : G.IsEquivalence := (Mod.comapEquivalenceOfIsIso _).isEquivalence_functor
  let Gc := G.mapHomologicalComplex (.up ℤ)
  obtain ⟨P, f, hf, _, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage K)
  have := hf
  let p : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have hGP := G.kFlat_mapHomologicalComplex_obj_of_isEquivalence hP
  let q : DerivedCategory.Q.obj (Gc.obj P) ≅ G.mapDerivedCategory.obj K :=
    (G.mapDerivedCategoryFactors.app P).symm ≪≫ G.mapDerivedCategory.mapIso p
  have hF := ordinary_complete_of_sfb ℓ E F e X K hK
  have haug : IsIso (DerivedCategory.Q.map
      (AdicCompletion.augmentation ℓ F X (Gc.obj P))) := by
    have h := (AdicCompletion.isDerivedComplete_iff ℓ F X _ _ hGP q).mp hF
    change IsIso (q.inv ≫ _) at h
    have := h
    exact IsIso.of_isIso_comp_left q.inv _
  obtain ⟨c, hc⟩ := smallIntegralRoosComparison ℓ E F e X P
  have : QuasiIso (AdicCompletion.augmentation ℓ F X (Gc.obj P)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp haug
  have : QuasiIso (Gc.map (SmallAdicCompletion.augmentation ℓ E X P) ≫ c.hom) := by
    rw [hc]
    infer_instance
  have hm : IsIso (DerivedCategory.Q.map
      (Gc.map (SmallAdicCompletion.augmentation ℓ E X P)) ≫
        DerivedCategory.Q.map c.hom) := by
    exact (DerivedCategory.Q.map_comp
      (Gc.map (SmallAdicCompletion.augmentation ℓ E X P)) c.hom) ▸
        (inferInstance : IsIso (DerivedCategory.Q.map
          (Gc.map (SmallAdicCompletion.augmentation ℓ E X P) ≫ c.hom)))
  have := hm
  have : IsIso (DerivedCategory.Q.map
      (Gc.map (SmallAdicCompletion.augmentation ℓ E X P))) :=
    IsIso.of_isIso_comp_right _ (DerivedCategory.Q.map c.hom)
  have : QuasiIso (Gc.map (SmallAdicCompletion.augmentation ℓ E X P)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp inferInstance
  have : QuasiIso (SmallAdicCompletion.augmentation ℓ E X P) :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ G).mp inferInstance
  exact ⟨P, hP, ⟨p⟩, inferInstance⟩

end AlgebraicGeometry.ProEtale
