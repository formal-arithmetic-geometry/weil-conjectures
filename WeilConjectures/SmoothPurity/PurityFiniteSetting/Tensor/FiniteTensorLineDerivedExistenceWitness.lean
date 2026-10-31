/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorReductionData
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorSemilinearReduction
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarRepresentativeIso
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLinePowerFlat
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicTensorComparison
import WeilConjectures.AlgebraicGeometry.Vector.VectorPurityScalarSingle
import WeilConjectures.CategoryTheory.Finite.FiniteRealizationMateAlgebra

/-! # Existence of the prescribed derived signed-line comparison

Source: finite reduction of purity, proof Step 2; Stacks Tags 03EK, 03EM and 06YY.
(blueprint: lem-route-exists-finite-tensor-line-derived-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

open Opposite SheafOfModules

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Adjunction.ofIsRightAdjoint
  Functor.mapDerivedCategory changeOfRingsOfUniverses scalarExtensionSection
  scalarExtensionUnitIso siteSheafTensorTmul siteSheafTensorRight finiteTensorFirstLine

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section

set_option allowUnsafeReducibility true in
attribute [local reducible] sheafCompose

private noncomputable def ordinaryHomEquiv (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (α : R ⟶ S)
    (L : proEtaleRingModules T R) (K : proEtaleRingModules T S) :
    (changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α L ⟶ K) ≃
      (L ⟶ (SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map α)).obj K) where
  toFun f := scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1} α L ≫
    (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map α)).map f
  invFun f := scalarExtensionLift.{u + 1, u, u + 1, u + 1} α L K f
  left_inv f := by
    apply scalarExtension_hom_ext.{u + 1, u, u + 1, u + 1} α L
    intro U s x
    simp only [scalarExtensionLift_tmul.{u + 1, u, u + 1, u + 1}, comp_val,
      PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
    change s • (show K.val.obj U from f.val.app U
      (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α L U 1 x)) =
      f.val.app U (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α L U s x)
    rw [← map_smul]
    congr 1
    simpa only [mul_one] using
      (scalarExtensionSection_smul.{u + 1, u, u + 1, u + 1} α L U s 1 x)
  right_inv f := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (scalarExtensionLift.{u + 1, u, u + 1, u + 1} α L K f).val.app U
      (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α L U 1 x) = f.val.app U x
    exact (scalarExtensionLift_tmul.{u + 1, u, u + 1, u + 1} α L K f U 1 x).trans
      (one_smul (S.obj.obj U) (show K.val.obj U from f.val.app U x))

private theorem ordinaryHomEquiv_naturality (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (α : R ⟶ S)
    (L : proEtaleRingModules T R) (K K' : proEtaleRingModules T S)
    (g : K ⟶ K') (f : changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α L ⟶ K) :
    ordinaryHomEquiv T α L K' (f ≫ g) = ordinaryHomEquiv T α L K f ≫
      (SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map α)).map g := by
  dsimp only [ordinaryHomEquiv, Equiv.coe_fn_mk]
  rw [Functor.map_comp, Category.assoc]

private noncomputable def ordinaryScalar (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (α : R ⟶ S) :
    proEtaleRingModules T R ⥤ proEtaleRingModules T S :=
  Adjunction.leftAdjointOfEquiv (ordinaryHomEquiv T α) (ordinaryHomEquiv_naturality T α)

private noncomputable def ordinaryAdjunction (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (α : R ⟶ S) :
    ordinaryScalar T α ⊣ SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map α) :=
  Adjunction.adjunctionOfEquivLeft (ordinaryHomEquiv T α) (ordinaryHomEquiv_naturality T α)

private theorem ordinaryAdjunction_unit (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (α : R ⟶ S)
    (L : proEtaleRingModules T R) :
    (ordinaryAdjunction T α).unit.app L =
      scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1} α L := by
  change scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1} α L ≫
    (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map α)).map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

end

private theorem realizationLine_isIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (EA : A ≌ C) (EB : B ≌ D)
    {S : C ⥤ D} {U : D ⥤ C} {T : A ⥤ B} {V : B ⥤ A}
    (a : S ⊣ U) (d : T ⊣ V) (k : U ⋙ EA.inverse ≅ EB.inverse ⋙ V)
    (L : A) (K : B) (b : T.obj L ≅ K) :
    IsIso ((a.homEquiv _ _).symm
      (EA.functor.map (d.unit.app L ≫ V.map b.hom) ≫
        (realizationRestrictionFromInverse EA EB k).inv.app K)) := by
  let z := ((EA.toAdjunction.comp a).ofNatIsoRight k).leftAdjointUniq
    (d.comp EB.toAdjunction)
  let w := realizationRestrictionFromInverse EA EB k
  have hz : a.homEquiv _ _ (z.hom.app L) =
      EA.functor.map (d.unit.app L) ≫ w.inv.app (T.obj L) := by
    have h := realizationScalar_unit EA EB a d k L
    have hh := congrArg (fun f : EA.functor.obj L ⟶ EA.functor.obj (V.obj (T.obj L)) ↦
      f ≫ w.inv.app (T.obj L)) h
    change (a.unit.app (EA.functor.obj L) ≫ U.map (z.hom.app L) ≫
      w.hom.app (T.obj L)) ≫ w.inv.app (T.obj L) = _ at hh
    simpa only [Adjunction.homEquiv_unit, Functor.comp_obj, Category.assoc,
      Iso.hom_inv_id_app, Category.comp_id] using hh
  have he : a.homEquiv _ _ (z.hom.app L ≫ EB.functor.map b.hom) =
      EA.functor.map (d.unit.app L ≫ V.map b.hom) ≫ w.inv.app K := by
    rw [a.homEquiv_naturality_right, hz]
    have hn := w.inv.naturality b.hom
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [Category.assoc, ← hn, ← Category.assoc, ← EA.functor.map_comp]
  change IsIso ((a.homEquiv (EA.functor.obj L) (EB.functor.obj K)).symm _)
  rw [← he, Equiv.symm_apply_apply]
  infer_instance

private abbrev inverseCoordinates
    {C D : Type*} [Category C] [Category D] (e : C ≌ D) : D ≌ C where
  functor := e.inverse
  inverse := e.functor
  unitIso := e.counitIso.symm
  counitIso := e.unitIso.symm
  functor_unitIso_comp := e.inverse_counitInv_comp

private theorem realizationRestriction_symm
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (EA : A ≌ C) (EB : B ≌ D) {U : D ⥤ C} {V : B ⥤ A}
    (s : EB.functor ⋙ U ≅ V ⋙ EA.functor) :
    realizationRestrictionFromInverse (inverseCoordinates EA) (inverseCoordinates EB) s.symm =
      (Functor.isoWhiskerRight EB.counitIso.symm (U ⋙ EA.inverse) ≪≫
        Functor.isoWhiskerLeft EB.inverse (Functor.isoWhiskerRight s EA.inverse) ≪≫
        Functor.isoWhiskerLeft (EB.inverse ⋙ V) EA.unitIso.symm).symm := by
  apply Iso.ext
  ext X
  simp [realizationRestrictionFromInverse, inverseCoordinates]

attribute [local irreducible] sfIntrinsicModuleEquivalence sfRealizationRestriction
  sfInverseRealizationRestriction realizationRestrictionFromInverse ordinaryScalar

section

set_option allowUnsafeReducibility true in
attribute [local reducible] ordinaryScalar ULift.commRing ULift.ring

private theorem fixedOrdinaryComparison_isIso (T : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    (L : proEtaleRingModules T (proEtaleConstantRing T A))
    (K : proEtaleRingModules T (proEtaleConstantRing T B))
    (b : changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (proEtaleConstantRingMap (T := T) φ) L ≅ K) :
    IsIso (((ProEtale.sheafExtendScalarsAdjunction φ.ulift.{u + 1, u + 1} T).homEquiv _ _).symm
      ((sfIntrinsicModuleEquivalence T A).inverse.map
          (scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1}
            (proEtaleConstantRingMap (T := T) φ) L ≫
          (proEtaleCoefficientRestrictScalars T φ).map b.hom) ≫
        (sfInverseRealizationRestriction T φ).hom.app K)) := by
  let EA := inverseCoordinates (sfIntrinsicModuleEquivalence T A)
  let EB := inverseCoordinates (sfIntrinsicModuleEquivalence T B)
  let a : ProEtale.sheafExtendScalars φ.ulift.{u + 1, u + 1} T ⊣
      sfFixedRestriction T φ := ProEtale.sheafExtendScalarsAdjunction _ T
  let d : ordinaryScalar T (proEtaleConstantRingMap (T := T) φ) ⊣
      proEtaleCoefficientRestrictScalars T φ := ordinaryAdjunction T _
  let k : sfFixedRestriction T φ ⋙ EA.inverse ≅
      EB.inverse ⋙ proEtaleCoefficientRestrictScalars T φ :=
    (sfRealizationRestriction T φ).symm
  let b' : (ordinaryScalar T (proEtaleConstantRingMap (T := T) φ)).obj L ≅ K := by
    unfold ordinaryScalar
    exact b
  have h := realizationLine_isIso EA EB a d k L K b'
  have hk : realizationRestrictionFromInverse EA EB k =
      (sfInverseRealizationRestriction T φ).symm := by
    simpa only [EA, EB, k, sfInverseRealizationRestriction] using
      (realizationRestriction_symm (sfIntrinsicModuleEquivalence T A)
        (sfIntrinsicModuleEquivalence T B) (sfRealizationRestriction T φ))
  erw [hk] at h
  dsimp only [EA, EB, inverseCoordinates, b', id_eq, Functor.id_obj] at h
  simp only [a, d, ordinaryAdjunction_unit, Iso.symm_inv, sfFixedRestriction] at h ⊢
  exact h

end

section

set_option allowUnsafeReducibility true in
attribute [local reducible] sheafCompose ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' SheafOfModules.unit PresheafOfModules.unit
  scalarTensorPower signedLinePower coefficientTwistLine finiteTensorLine
  finiteTensorLineSectionMap PresheafOfModules.restrictOver
  Functor.sheafPushforwardContinuous SheafOfModules.overFunctor
  SheafOfModules.pushforward PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ PresheafOfModules.pushforward₀Obj
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj Over.forget

private theorem ordinaryComparison (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))]
    (c : P.FiniteTensorLineMaps m hm hmn T)
    (hc : P.FiniteTensorLineMapsNormalized m hm hmn T c) (r : ℤ) :
    ∃ b : changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
        (proEtaleConstantRingMap (T := T) (P.finiteReductionRingHom m hm hmn))
        (P.finiteTensorLine T r) ≅ (P.finiteReductionSetting m hm).finiteTensorLine T r,
      c r = scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1} _ _ ≫
        (proEtaleCoefficientRestrictScalars T (P.finiteReductionRingHom m hm hmn)).map
          b.hom := by
  let α := proEtaleConstantRingMap (T := T) (P.finiteReductionRingHom m hm hmn)
  let Q := P.finiteReductionSetting m hm
  obtain ⟨b, hb⟩ := firstComparison P m hm hmn T
  obtain ⟨B, hB, heval, _⟩ := exists_signedLineComparison.{u + 1, u, u + 1} α
    (P.finiteTensorFirstLine T) (Q.finiteTensorFirstLine T)
    (firstLine_locallyFree P T) (firstLine_locallyFree Q T) b
  let d : P.FiniteTensorLineMaps m hm hmn T := fun
    | .ofNat n => scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1} α _ ≫
        (proEtaleCoefficientRestrictScalars T (P.finiteReductionRingHom m hm hmn)).map
          (B (.ofNat n)).hom
    | .negSucc n => scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1} α _ ≫
        (proEtaleCoefficientRestrictScalars T (P.finiteReductionRingHom m hm hmn)).map
          (B (.negSucc n)).hom
  have hd : P.FiniteTensorLineMapsNormalized m hm hmn T d := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro U a
      change (B 0).hom.val.app U
        (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α _ U 1 a) = α.hom.app U a
      have hh := congrArg (fun f ↦ f.val.app U
        (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α _ U 1 a)) hB.1
      refine hh.trans ?_
      simpa only [one_mul] using scalarExtensionUnitIso_tmul α U 1 a
    · intro U a x z hz
      change HEq ((B 1).hom.val.app U (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α _ U 1 z)) _
      rw [hB.2.1]
      exact hb U a x z hz
    · intro j U x y xB yB hx hy
      cases eq_of_heq hx
      cases eq_of_heq hy
      apply heq_of_eq
      change (B (.ofNat (j + 2))).hom.val.app U
        (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α _ U 1
          (siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
            (A := proEtaleConstantRing T P.Ring)
            (P.finiteTensorLine T (.ofNat (j + 1))) (P.finiteTensorFirstLine T) U x y)) = _
      rw [hB.2.2.1 j U 1 x y, ← hB.2.1]
      rfl
    · intro j U φ x φB xB hφ hx
      cases eq_of_heq hφ
      cases eq_of_heq hx
      change ((B (.negSucc j)).hom.val.app U
        (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α _ U 1 φ)).app
          (op (Over.mk (𝟙 U.unop)))
            ((B (.ofNat (j + 1))).hom.val.app U
              (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α _ U 1 x)) =
        α.hom.app U (φ.app (op (Over.mk (𝟙 U.unop))) x)
      simpa only [mul_one] using heval j U 1 1 φ x
  have hcd : c = d := by
    obtain ⟨e, he, hu⟩ := P.existsUnique_finiteTensorSemilinearReduction m hm hmn T
    exact (hu c hc).trans (hu d hd).symm
  refine ⟨B r, ?_⟩
  rw [hcd]
  cases r <;> rfl

end

private theorem fixedLine_flat (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (r : ℤ) :
    ObjectProperty.flat (P.finiteTensorFixedSheaf T r) := by
  classical
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let e := sfIntrinsicModuleEquivalence T P.Ring
  let : e.functor.IsEquivalence := e.isEquivalence_functor
  have hpres : PreservesFiniteLimits e.functor := inferInstance
  have hrefl : ReflectsFiniteLimits e.functor := inferInstance
  let hfirst : (P.finiteTensorFirstLine T).IsFiniteLocallyFreeOfRank 1 := by
    obtain ⟨I, X, hX, h⟩ := firstLine_locallyFree P T
    exact (isInvertible_iff_isFiniteLocallyFreeOfRank_one _).mp
      (isInvertible_of_forall_over_unit X hX h)
  let hline : (P.finiteTensorLine T r).IsFiniteLocallyFreeOfRank 1 :=
    (signedLineTensor_equivalence T (proEtaleConstantRing T P.Ring)
      (P.finiteTensorFirstLine T) r).1
  let hrank : (e.functor.obj (P.finiteTensorFixedSheaf T r)).IsFiniteLocallyFreeOfRank 1 :=
    IsFiniteLocallyFreeOfRank.of_iso
      (show P.finiteTensorLine T r ≅ e.functor.obj (P.finiteTensorFixedSheaf T r) from
        (e.counitIso.app (P.finiteTensorLine T r)).symm)
  have hflat' : IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology T) (R := proEtaleConstantRing T P.Ring)
      (e.functor.obj (P.finiteTensorFixedSheaf T r)) := by
    obtain ⟨I, X, hX, h⟩ :=
      (isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
        (M := e.functor.obj (P.finiteTensorFixedSheaf T r)) (r := 1)).mp hrank
    have hcover : ∃ (I : Type (u + 1)) (X : I → T.ProEt), (ProEt.topology T).CoversTop X ∧
        ∀ i, Nonempty ((e.functor.obj (P.finiteTensorFixedSheaf T r)).over (X i) ≅
          unit (((sheafCompose (ProEt.topology T)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (proEtaleConstantRing T P.Ring)).over (X i))) :=
      ⟨I, X, hX, fun i ↦ ⟨(h i).some ≪≫ freeUniqueIso (ULift.{u + 1} (Fin 1))⟩⟩
    simpa only [signedLinePower, scalarTensorPower] using
      (SignedLineDerivedBaseChange.signed_line_power_flat.{u + 1, u, u + 1}
        (proEtaleConstantRing T P.Ring)
        (e.functor.obj (P.finiteTensorFixedSheaf T r)) hcover (1 : ℤ))
  obtain ⟨q⟩ := proEtale_intrinsic_tensorRight_comparison T P.Ring
    (P.finiteTensorFixedSheaf T r)
  have hright : PreservesFiniteLimits
      (siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        (e.functor.obj (P.finiteTensorFixedSheaf T r))) := hflat'.1
  have hcomp : PreservesFiniteLimits (e.functor ⋙
      siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        (e.functor.obj (P.finiteTensorFixedSheaf T r))) :=
    @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ hpres hright
  have htcomp : PreservesFiniteLimits
      (tensorRight (P.finiteTensorFixedSheaf T r) ⋙ e.functor) :=
    @preservesFiniteLimits_of_natIso _ _ _ _ _ _ q hcomp
  have ht : PreservesFiniteLimits (tensorRight (P.finiteTensorFixedSheaf T r)) :=
    @preservesFiniteLimits_of_reflects_of_preserves _ _ _ _ _ _ _ _ htcomp hrefl
  exact (ObjectProperty.flat_iff_preservesFiniteLimits _).2
    (preservesFiniteLimits_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight (P.finiteTensorFixedSheaf T r)).symm)

private theorem single_adjunct
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (S : C ⥤ D) (R : D ⥤ C) (Q : E ⥤ F) (V : F ⥤ E)
    (i : C ⥤ E) (j : D ⥤ F) (a : S ⊣ R) (b : Q ⊣ V)
    (k : j ⋙ V ≅ R ⋙ i) (M : C) (N : D) (g : S.obj M ⟶ N) :
    purityAdjunctionSingleMap S R Q V i j a b k M ≫ j.map g =
      (b.homEquiv _ _).symm (i.map (a.homEquiv _ _ g) ≫ k.inv.app N) := by
  unfold purityAdjunctionSingleMap
  rw [← b.homEquiv_naturality_right_symm]
  congr 1
  rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (i.map (a.unit.app M) ≫ ·) (k.inv.naturality g).symm

private theorem representativeSingle_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (E : C ⥤ D) [E.Additive] (F : DerivedCategory C ⥤ DerivedCategory D)
    (rep : ∀ X : CochainComplex C ℤ, F.obj (DerivedCategory.Q.obj X) ⟶
      DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj X))
    (M : C) (h : IsIso (rep ((CochainComplex.singleFunctor C 0).obj M))) :
    IsIso (puritySingleFromRepresentativeMap E F rep M) := by
  unfold puritySingleFromRepresentativeMap
  have hi : IsIso (F.map ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app M)) :=
    (F.mapIso ((DerivedCategory.singleFunctorIsoCompQ C 0).app M)).isIso_hom
  have hj : IsIso (DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom.app M)) :=
    (DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).app M)).isIso_hom
  have hk : IsIso ((DerivedCategory.singleFunctorIsoCompQ D 0).inv.app (E.obj M)) :=
    ((DerivedCategory.singleFunctorIsoCompQ D 0).app (E.obj M)).isIso_inv
  exact IsIso.comp_isIso' hi (IsIso.comp_isIso' h (IsIso.comp_isIso' hj hk))

private theorem scalarSingle_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A))
    (hM : ObjectProperty.flat M) :
    IsIso (purityAdjunctionSingleMap
      (ProEtale.sheafExtendScalars φ T) (Sheaf.restrictScalars (ProEt.topology T) φ)
      (ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T)
      (ProEtale.SupportedEtaleTensorOrigin.proFixedRestriction φ T)
      (DerivedCategory.singleFunctor.{u + 1} _ 0) (DerivedCategory.singleFunctor.{u + 1} _ 0)
      (ProEtale.sheafExtendScalarsAdjunction φ T)
      (Adjunction.ofIsRightAdjoint
        (ProEtale.SupportedEtaleTensorOrigin.proFixedRestriction φ T))
      ((Sheaf.restrictScalars (ProEt.topology T) φ).mapDerivedCategorySingleFunctor 0) M) := by
  let E := ProEtale.sheafExtendScalars φ T
  let U := Sheaf.restrictScalars (ProEt.topology T) φ
  let F := ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T
  let adj := ProEtale.sheafExtendScalarsAdjunction φ T
  let ad := Adjunction.ofIsRightAdjoint
    (ProEtale.SupportedEtaleTensorOrigin.proFixedRestriction φ T)
  have : PreservesFiniteLimits U := by
    let := adj.rightAdjoint_preservesLimits
    infer_instance
  have : PreservesFiniteColimits U := by
    let := (Sheaf.restrictCoextendScalarsAdj
      (ProEt.topology T) φ).leftAdjoint_preservesColimits
    infer_instance
  have hk := (CochainComplex.kFlat_single_obj_iff_flat M (0 : ℤ)).2 hM
  have hi := finiteScalarRepresentative_isIso φ T
    ((CochainComplex.singleFunctor _ 0).obj M) hk
  have hr : Etale.scalarAdjunctionRepresentativeMap E U adj F ad =
      ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative φ T := by
    funext X
    unfold Etale.scalarAdjunctionRepresentativeMap
      ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative
    rfl
  rw [purityAdjunctionSingleMap_eq_representative E U adj F ad]
  unfold purityRepresentativeSingleMap
  rw [hr]
  exact representativeSingle_isIso E F
    (ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative φ T) M hi

set_option allowUnsafeReducibility true in
attribute [local reducible] Coefficient coefficientCommRing

/--
For a normalized ordinary signed-line map, the prescribed transpose is realized by
some derived comparison. The signed-line scalar comparison theorem, applied to the
first-line comparison, gives ordinary isomorphisms `d_r : B ⊗_A L_A(r) ≅ L_B(r)`;
their adjuncts form a normalized family, which is `c` by uniqueness of the
normalized ordinary family. Left-adjoint uniqueness and the realization/restriction
square carry the transpose of `d_r` to fixed-scalar coordinates, where its adjunct is
`finiteTensorFixedLineMap c r`, so the fixed-scalar transpose is invertible. The
fixed line is flat (locally free of rank one, signed-power flatness at exponent 1,
reflected through the encoding equivalence), so its single complex is K-flat and the
derived adjunction/single comparison is invertible by the finite scalar representative
theorem. Their composite is the required isomorphism; naturality of the adjunction
hom equivalences and of the exact-restriction/single comparison gives the displayed
`HEq` equation. This is the existence part of the unique comparison statement;
uniqueness is proved separately from injectivity of the scalar adjunction hom
equivalence. Source: blueprint proof Step 2; Stacks Tags 03EK, 03EM and 06YY.
(blueprint: lem-route-exists-finite-tensor-line-derived-comparison)
-/
theorem exists_finiteTensorLineDerivedComparison (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))]
    (c : P.FiniteTensorLineMaps m hm hmn T)
    (hc : P.FiniteTensorLineMapsNormalized m hm hmn T c) (r : ℤ) :
    ∃ b : (P.finiteTensorReduction m hm hmn T).obj (P.finiteTensorFixedLine T r) ≅
        (P.finiteReductionSetting m hm).finiteTensorFixedLine T r,
      (P.finiteTensorLineComparisonData m hm hmn T).Pointwise c r b := by
  classical
  let φ := P.finiteReductionRingHom m hm hmn
  let Q := P.finiteReductionSetting m hm
  let M := P.finiteTensorFixedSheaf T r
  let N := Q.finiteTensorFixedSheaf T r
  let E := ProEtale.sheafExtendScalars φ.ulift.{u + 1, u + 1} T
  let U := sfFixedRestriction T φ
  let F := P.finiteTensorReduction m hm hmn T
  let G := ProEtale.SupportedEtaleTensorOrigin.fixedRestriction φ T
  let adj : E ⊣ U := ProEtale.sheafExtendScalarsAdjunction φ.ulift.{u + 1, u + 1} T
  let ad : F ⊣ G := P.finiteTensorAdjunction m hm hmn T
  let f : M ⟶ U.obj N := P.finiteTensorFixedLineMap m hm hmn T c r
  let d : E.obj M ⟶ N := (adj.homEquiv M N).symm f
  obtain ⟨b, hb⟩ := ordinaryComparison P m hm hmn T c hc r
  have hd : IsIso d := by
    dsimp only [d, f, finiteTensorFixedLineMap]
    rw [hb]
    exact fixedOrdinaryComparison_isIso T φ _ _ b
  let i := DerivedCategory.singleFunctor.{u + 1}
    (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) 0
  let j := DerivedCategory.singleFunctor.{u + 1}
    (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} Q.Coefficient)) 0
  let s := purityAdjunctionSingleMap E U F G i j
    adj ad (U.mapDerivedCategorySingleFunctor 0) M
  have hs : IsIso s := scalarSingle_isIso φ.ulift.{u + 1, u + 1} T M (fixedLine_flat P T r)
  let v := s ≫ j.map d
  have hjd : IsIso (j.map d) := @Functor.map_isIso _ _ _ _ _ _ j d hd
  have hv : IsIso v := IsIso.comp_isIso' hs hjd
  refine ⟨@asIso _ _ _ _ v hv, ?_⟩
  have he : v = (ad.homEquiv _ _).symm
      (i.map f ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app N) := by
    have hdf : adj.homEquiv M N d = f := (adj.homEquiv M N).apply_symm_apply f
    exact (single_adjunct E U F G i j adj ad
      (U.mapDerivedCategorySingleFunctor 0) M N d).trans
        (congrArg (fun t : M ⟶ U.obj N ↦
          (ad.homEquiv (i.obj M) (j.obj N)).symm
            (i.map t ≫ (U.mapDerivedCategorySingleFunctor 0).inv.app N)) hdf)
  unfold TransposedFamilyData.Pointwise finiteTensorLineComparisonData
  dsimp only
  change HEq (ad.homEquiv _ _ v)
    (i.map f ≫
      (U.mapDerivedCategorySingleFunctor 0).inv.app N)
  apply heq_of_eq
  rw [he]
  exact (ad.homEquiv _ _).apply_symm_apply _

end WeilConjectures.PurityFiniteSetting
