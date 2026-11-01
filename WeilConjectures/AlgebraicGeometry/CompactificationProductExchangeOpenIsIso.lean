/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactificationProductExchangeDefs
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantExchangeEncoding
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicRealizationOriginComparison
import WeilConjectures.AlgebraicGeometry.OpenDirectImageFieldBaseChange
import WeilConjectures.AlgebraicGeometry.SbcExchange.SbcExchangeFormal
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedPlus

/-! # Invertibility of the open compactification factor

A component of the compactification product-projection argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

-- Fix the intrinsic pro-etale localization, which uses the standard derived category.
attribute [local instance 50000] proEtaleRingModules_hasDerivedCategory

attribute [local irreducible] proEtaleRingModulePullback proEtaleConstantRingComparison
  proEtaleAmbientRingedExchange
  proEtaleRingDerivedAdjunction proEtaleRingModuleDirectImage Functor.mapDerivedCategory

set_option maxRecDepth 4000 in
-- The exact realization and restriction have large intrinsic category instances.
private theorem originRestriction (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    Nonempty (ProEtale.finiteCoefficientIntrinsicDerivedComparison X A ⋙
      proEtaleDerivedModuleRestriction X A ≅
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory) := by
  obtain ⟨e⟩ := ProEtale.intrinsicRealization_restriction X A
  exact ⟨(Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e ≪≫ Functor.rightUnitor _)⟩

private def productSquare {S : Scheme.{u}} {U V : Over S} (f : U ⟶ V) (T : Over S) :
    ChosenCartesianSquare (prod.fst : U ⨯ T ⟶ U).left
      (prod.map f (𝟙 T)).left f.left (prod.fst : V ⨯ T ⟶ V).left :=
  { toCommSq := ((IsPullback.of_prod_fst_with_id f T).map (Over.forget S)).toCommSq
    isoPullback := ((IsPullback.of_prod_fst_with_id f T).map (Over.forget S)).isoPullback
    hom_fst := ((IsPullback.of_prod_fst_with_id f T).map
      (Over.forget S)).isoPullback_hom_fst
    hom_snd := ((IsPullback.of_prod_fst_with_id f T).map
      (Over.forget S)).isoPullback_hom_snd }

private theorem productExchange_eq_sbc (A : Type u) [CommRing A]
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) (T : Over S) :
    compactificationProductExchange A f T = SbcExchange.exchange A (productSquare f T) := by
  rfl

private theorem reflectArrowIso {C : Type*} {D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.ReflectsIsomorphisms] {X Y : C} (f : X ⟶ Y)
    {U V : D} (g : U ⟶ V) [IsIso g] (e : Nonempty (Arrow.mk (F.map f) ≅ Arrow.mk g)) :
    IsIso f := by
  obtain ⟨e⟩ := e
  have : IsIso (F.map f) :=
    ((MorphismProperty.isomorphisms D).arrow_mk_iso_iff e).2 inferInstance
  exact isIso_of_reflects_iso f F

private theorem sbcExchange_eq_ambient (A : Type u) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) :
    SbcExchange.exchange A sq = proEtaleAmbientRingedExchange sq
      (proEtaleConstantRing X A) (proEtaleConstantRing Y A)
      (proEtaleConstantRing X' A) (proEtaleConstantRing Y' A)
      (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison g A)
      (proEtaleConstantRingComparison g' A) (proEtaleConstantRingComparison f' A)
      ((heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq g' f A)).trans
        ((congr_arg_heq (fun q : X' ⟶ Y ↦ proEtaleConstantRingComparison q A) sq.w).trans
          (heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq f' g A)).symm)) := by
  rfl

set_option maxRecDepth 4000 in
-- Keep the ringed mate folded while comparing its fixed-scalar encoding.
private theorem ringed_isIso_of_fixed (A : Type u) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (K : proEtaleDerivedCategory X A)
    (h : IsIso ((ProEtale.derivedBaseChangeMap
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq.toCommSq).app
        ((proEtaleDerivedModuleRestriction X A).obj K))) :
    IsIso ((SbcExchange.exchange A sq).app K) := by
  rw [sbcExchange_eq_ambient]
  have := h
  exact reflectArrowIso (proEtaleDerivedModuleRestriction Y' A) _ _
    (proEtaleConstantExchange_encoding A sq
      ((heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq g' f A)).trans
        ((congr_arg_heq (fun q : X' ⟶ Y ↦ proEtaleConstantRingComparison q A) sq.w).trans
          (heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq f' g A)).symm)) K)

private theorem etaleProductOpen_isIso
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) (_hl : l.Prime)
    (_hne : l ≠ ringChar D.k) (A : Type u) [CommRing A] [Finite A]
    (_hA : ∃ r : ℕ, 0 < r ∧ ((l ^ r : ℕ) : A) = 0)
    (X Y T : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (B : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    (j : X ⟶ B) [IsOpenImmersion j.left] [QuasiCompact j.left]
    (Lp : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hL : Etale.DerivedCategory.isBoundedConstructible
      (ULift.{u + 1, u} A) X.left Lp.obj) :
    IsIso ((AlgebraicGeometry.Etale.baseChange
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (productSquare j T).toCommSq).app Lp) := by
  have : Fact l.Prime := ⟨_hl⟩
  let C := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  have hs : IsPullback (prod.fst : X ⨯ T ⟶ X).left
      (prod.map j (𝟙 T)).left j.left (prod.fst : B ⨯ T ⟶ B).left :=
    (IsPullback.of_prod_fst_with_id j T).map (Over.forget _)
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
  apply (Etale.isIso_derivedBaseChangeMap_app_ι_obj_iff C hs.toCommSq Lp).mp
  obtain ⟨r, hr, hA⟩ := _hA
  have hAu : (l ^ r : ULift.{u + 1, u} A) = 0 := by
    apply (ULift.ringEquiv : ULift.{u + 1, u} A ≃+* A).injective
    simpa only [map_pow, map_natCast, map_zero, Nat.cast_pow] using hA
  exact (Etale.isIso_derivedBaseChangeMap_openImmersion_field_and_isBoundedConstructible
    D.k l _hne (ULift.{u + 1, u} A) r hr hAu X.hom B.hom T.hom j.left j.w
    (prod.fst : X ⨯ T ⟶ X).left (prod.fst : B ⨯ T ⟶ B).left
    (prod.snd : B ⨯ T ⟶ T).left (prod.map j (𝟙 T)).left
    (Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (prod.fst : B ⨯ T ⟶ B) (prod.snd : B ⨯ T ⟶ T)) (prodIsProd B T))
      hs Lp.obj hL).1

private theorem fixedExchange_isIso_of_etale (A : Type u) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    (hs : IsPullback g' f' f g)
    (Lp : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hBC : IsIso ((AlgebraicGeometry.Etale.baseChange
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) hs.toCommSq).app Lp)) :
    IsIso ((ProEtale.derivedBaseChangeMap
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) hs.toCommSq).app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj Lp.obj)) := by
  let C := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  have := hBC
  have heq := ProEtale.comparison_derivedBaseChangeMap (ULift.{u + 1, u} A) hs Lp
  have hmap : IsIso ((ProEtale.comparisonUpperStar C Y').mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map
        ((AlgebraicGeometry.Etale.baseChange C hs.toCommSq).app Lp))) := inferInstance
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (Arrow.isoMk ((ProEtale.baseChangeSourceComparisonIso f g
      (ULift.{u + 1, u} A)).app Lp)
      ((ProEtale.baseChangeTargetComparisonIso g' f'
        (ULift.{u + 1, u} A)).app Lp) heq.symm)).1 hmap

private theorem isIsoAppOfOrigin {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (α : F ⟶ G) {K L : C} (e : Nonempty (K ≅ L))
    (h : IsIso (α.app K)) : IsIso (α.app L) := by
  obtain ⟨e⟩ := e
  exact (NatTrans.isIso_app_iff_of_iso α e).mp h

private theorem fixedProductOpen_isIso
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) (_hl : l.Prime)
    (_hne : l ≠ ringChar D.k) (A : Type u) [CommRing A] [Finite A]
    (_hA : ∃ r : ℕ, 0 < r ∧ ((l ^ r : ℕ) : A) = 0)
    (X Y T : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (B : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    (j : X ⟶ B) [IsOpenImmersion j.left] [QuasiCompact j.left]
    (p : B ⟶ Y) [IsProper p.left] (M : proEtaleDerivedCategory X.left A)
    (_hM : (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} A) X.left) ⋙
      ProEtale.finiteCoefficientIntrinsicDerivedComparison X.left A).essImage M) :
    IsIso ((ProEtale.derivedBaseChangeMap
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (productSquare j T).toCommSq).app
        ((proEtaleDerivedModuleRestriction X.left A).obj M)) := by
  classical
  have : Fact l.Prime := ⟨_hl⟩
  let C := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  obtain ⟨L, ⟨eM⟩⟩ := _hM
  have hLb : ∃ n : ℤ, DerivedCategory.IsGE L.obj n := by
    obtain ⟨a, b, hab, hv⟩ := L.property.2
    exact ⟨a, (DerivedCategory.isGE_iff L.obj a).mpr (fun i hi ↦ hv i (Or.inl hi))⟩
  let Lp : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology C) := ⟨L.obj, hLb⟩
  let sq := productSquare j T
  have hs : IsPullback (prod.fst : X ⨯ T ⟶ X).left
      (prod.map j (𝟙 T)).left j.left (prod.fst : B ⨯ T ⟶ B).left :=
    (IsPullback.of_prod_fst_with_id j T).map (Over.forget _)
  have : IsOpenImmersion (prod.map j (𝟙 T)).left :=
    MorphismProperty.of_isPullback hs inferInstance
  have : QuasiCompact (prod.map j (𝟙 T)).left :=
    MorphismProperty.of_isPullback hs inferInstance
  have hBC := etaleProductOpen_isIso D l _hl _hne A _hA X Y T B j Lp L.property
  have hbase := fixedExchange_isIso_of_etale A hs Lp hBC
  let eN := ((Classical.choice (originRestriction X.left A)).app L.obj).symm ≪≫
    (proEtaleDerivedModuleRestriction X.left A).mapIso eM
  exact isIsoAppOfOrigin (ProEtale.derivedBaseChangeMap C sq.toCommSq) ⟨eN⟩ hbase

set_option maxRecDepth 4000 in
-- Transport between the specified ordinary derived-category presentations.
/-- Invertibility of the actual open compactification exchange.

Source: latest blueprint det-tf-ibc-pasting.proof.md, step 5; Stacks Tag 0D6J.
(blueprint: compactification-product-exchange-open-isIso).

Proof: the supplied essential-image hypothesis gives a bounded constructible etale
origin L and its isomorphism to M. Exact realization followed by constant-scalar
restriction is the usual fixed-coefficient comparison, by the sheafification unit.
The universal product squares and stability under base change give the Cartesian
and qcqs hypotheses. Field base change makes the etale exchange at L invertible,
including for singular T. Pass to D+ using the canonical restriction comparison.
The etale/pro-etale exchange comparison identifies the fixed-coefficient exchange
as the conjugate of this map by its specified endpoint isomorphisms. Naturality
transports it to the restricted M. Finally constant-scalar exchange encoding
identifies that arrow with the image of the actual intrinsic ambient mate.
Restriction is an exact equivalence and reflects isomorphisms. -/
theorem compactificationProductExchange_open_isIso
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) (_hl : l.Prime)
    (_hne : l ≠ ringChar D.k) (A : Type u) [CommRing A] [Finite A]
    (_hA : ∃ r : ℕ, 0 < r ∧ ((l ^ r : ℕ) : A) = 0)
    (X Y T : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (B : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    (j : X ⟶ B) [IsOpenImmersion j.left] [QuasiCompact j.left]
    (p : B ⟶ Y) [IsProper p.left] (M : proEtaleDerivedCategory X.left A)
    (_hM : (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} A) X.left) ⋙
      ProEtale.finiteCoefficientIntrinsicDerivedComparison X.left A).essImage M) :
    IsIso ((compactificationProductExchange A j T).app M) := by
  rw [productExchange_eq_sbc]
  exact ringed_isIso_of_fixed A (productSquare j T) M
    (fixedProductOpen_isIso D l _hl _hne A _hA X Y T B j p M _hM)

end AlgebraicGeometry.Scheme
