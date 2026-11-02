/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClassPullbackFrame
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedOrdinaryUnit
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientNormalizedSourceEndpoint
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalPulledCompletedGeneratorExt
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalScalarPullbackUnit
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalScalarRealizationTranspose
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalSingleLimitTransport
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalSupportedGeneratorPullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalTransportedSingleEndpoint
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Realization.DiagonalRealizationPullback
public import WeilConjectures.AlgebraicGeometry.DiagonalNormalizedReductionSingleSquare
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Coefficient.DiagonalTraceCoefficientRestriction
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalRlimForgetUnit
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalRlimPullbackEndpoints
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange

/-! # The closed-source limit endpoint
Source: the latest blueprint, diagonal coefficient changes, paragraph (3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
open DiagonalTrace
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor diagonalCompletedSource

private theorem source_scalar_mono (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ) :
    Mono (l ^ (n + 1) • 𝟙 (diagonalIntegralSource Y)) := by
  let W := ProjectiveLine Y
  let k := l ^ (n + 1)
  have hk : k ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : Mono (k • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} ℤ))) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro x y h
    change k • x = k • y at h
    exact ULift.ext _ _ (nsmul_right_injective hk (congrArg ULift.down h))
  have : Mono ((Functor.const W.ProEtᵒᵖ).map
      (k • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) := NatTrans.mono_of_mono_app _
  have : Mono ((presheafToSheaf (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1}).map
      ((Functor.const W.ProEtᵒᵖ).map
        (k • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} ℤ))))) := inferInstance
  have hm : Mono (k • 𝟙 ((constantSheaf (Scheme.ProEt.topology W)
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) := by
    simpa only [constantSheaf, Functor.comp_obj, Functor.map_nsmul,
      CategoryTheory.Functor.map_id] using this
  have := (lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion Y)).map_mono
    (k • 𝟙 ((constantSheaf (Scheme.ProEt.topology W)
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))))
  simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id] using this

private theorem source_single_regular (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (n : ℕ) (i : ℤ) :
    Mono (l ^ (n + 1) • 𝟙
      (((CochainComplex.singleFunctor _ 0).obj (diagonalIntegralSource Y)).X i)) := by
  classical
  by_cases hi : i = 0
  · subst i
    let e := eqToIso (HomologicalComplex.single_obj_X_self (.up ℤ) 0
      (diagonalIntegralSource Y))
    have := source_scalar_mono l Y n
    have he : (l ^ (n + 1) • 𝟙 _) ≫ e.hom =
        e.hom ≫ (l ^ (n + 1) • 𝟙 (diagonalIntegralSource Y)) := by
      simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
        Category.id_comp, Category.comp_id]
    exact mono_of_mono_fac he
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
      (diagonalIntegralSource Y) i hi).mono _

private theorem complement_preimage
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (hX : X' ⟶ X) (hS : S' ⟶ S) [IsClosedImmersion f] [IsClosedImmersion f']
    (sq : IsPullback hX f' f hS) :
    hS ⁻¹ᵁ f.openComplement = f'.openComplement := by
  ext x
  change hS x ∉ Set.range f ↔ x ∉ Set.range f'
  constructor
  · intro h ⟨z, hz⟩
    apply h
    refine ⟨hX z, ?_⟩
    rw [← hz]
    exact congrArg (fun f ↦ f z) sq.w
  · intro h ⟨z, hz⟩
    obtain ⟨t, _, ht⟩ := Scheme.exists_preimage_of_isPullback sq z x hz
    exact h ⟨t, ht⟩

private theorem diagonal_complement_quasiCompact (Y : Scheme.{u}) :
    QuasiCompact (diagonalImmersion Y).openComplement.ι := by
  let : IsNoetherianRing (ULift.{u} ℤ) := by
    let eZ : ℤ ≃+* ULift.{u} ℤ := ULift.ringEquiv.symm
    exact isNoetherianRing_of_surjective ℤ _ eZ.toRingHom eZ.surjective
  let g := toSpecZ Y
  let i := diagonalImmersion specZ.{u}
  let i' := diagonalImmersion Y
  have : IsNoetherian (ProjectiveLine specZ.{u}) :=
    isNoetherian_of_locallyOfFiniteType (ProjectiveLine specZ.{u} ↘ specZ.{u})
  have : IsNoetherian (diagonalSurface specZ.{u}) :=
    isNoetherian_of_locallyOfFiniteType
      (pullback.fst (ProjectiveLine specZ.{u} ↘ specZ.{u})
        (ProjectiveLine specZ.{u} ↘ specZ.{u}))
  have h := complement_preimage i i' (baseP g) (baseW g)
    (diagonalBaseChange_cartesian g)
  have : QuasiCompact (((baseW g) ⁻¹ᵁ i.openComplement).ι) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict (baseW g) i.openComplement)
      (inferInstanceAs (QuasiCompact i.openComplement.ι))
  rwa [h] at this

private theorem source_map_isIso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (b : BaseSquares g) (c : UnitPullEndpoint R (baseP g)) :
    IsIso (sourcePullbackMap R g b.diagonal_square c) := by
  have hc : IsIso (CondensedRing.upperStarLowerStarAdjunction R
      (diagonalImmersion Y)).counit := inferInstance
  have hunit (M : Modules R (ProjectiveLine Y)) :
      IsIso ((CondensedRing.upperStarLowerStarAdjunction R
        (diagonalImmersion Y')).unit.app
          ((CondensedRing.upperStar R (baseW g)).obj
            ((CondensedRing.lowerStar R (diagonalImmersion Y)).obj M))) := by
    let N := (CondensedRing.upperStar R (baseW g)).obj
      ((CondensedRing.lowerStar R (diagonalImmersion Y)).obj M)
    have hz₀ := abelian_pullback_supported (diagonalImmersion Y) (diagonalImmersion Y')
      (baseP g) (baseW g) (diagonalBaseChange_cartesian g) ((Mod.forget _).obj M)
    have hz : IsZero ((upperStar Ab.{u + 1} (diagonalImmersion Y').openComplement.ι).obj
        ((Mod.forget _).obj N)) := by
      refine hz₀.of_iso ((upperStar Ab.{u + 1}
        (diagonalImmersion Y').openComplement.ι).mapIso ?_)
      exact ((upperStar Ab.{u + 1} (baseW g)).mapIso
        ((CondensedRing.lowerStarForgetIso R (diagonalImmersion Y)).app M) ≪≫
        (CondensedRing.upperStarForgetIso R (baseW g)).app
          ((CondensedRing.lowerStar R (diagonalImmersion Y)).obj M)).symm
    have := diagonal_complement_quasiCompact Y'
    have hu := (abelian_closed_support (diagonalImmersion Y')
      (diagonalImmersion Y').openComplement.ι
      (by simp only [Scheme.Opens.range_ι, Scheme.Hom.coe_openComplement])).2 _ hz
    have hm : IsIso ((Mod.forget _).map
        ((CondensedRing.upperStarLowerStarAdjunction R (diagonalImmersion Y')).unit.app N)) := by
      rw [CondensedRing.forget_map_upperStarLowerStarAdjunction_unit_app' R
        (diagonalImmersion Y') N]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have hx := exchangeRight_isIso
    (CondensedRing.upperStarLowerStarAdjunction R (diagonalImmersion Y))
    (CondensedRing.upperStarLowerStarAdjunction R (diagonalImmersion Y'))
    ((CondensedRing.upperStarComp R (diagonalImmersion Y') (baseW g)).symm ≪≫
      CondensedRing.upperStarCongr R b.diagonal_square ≪≫
      CondensedRing.upperStarComp R (baseP g) (diagonalImmersion Y)) hc hunit
  unfold sourcePullbackMap ordinaryExchange
  infer_instance

private theorem ordinary_source_data (l : ℕ) [Fact l.Prime]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (geometry : BaseSquares g)
    (hY : IsUnit (l : Γ(Y, ⊤))) (hY' : IsUnit (l : Γ(Y', ⊤))) :
    Nonempty (SourcePullback (Profinite.continuousMapRingObj.{u} ℤ_[l]) g (zlLine l)
      (spIntegralComparison (baseP g) l (bottomField l))
      (spIntegralComparison (baseW g) l (bottomField l))) := by
  let residue (T : Scheme.{u}) (p : T ⟶ Y) :
      ∀ x : T, Invertible (l : T.residueField x) := fun x ↦
    (show IsUnit (l : T.residueField x) from by
      let ψ := (T.residue x).hom.comp
        ((T.presheaf.germ ⊤ x trivial).hom.comp p.appTop.hom)
      simpa only [map_natCast] using hY.map ψ).invertible
  let residue' (T : Scheme.{u}) (p : T ⟶ Y') :
      ∀ x : T, Invertible (l : T.residueField x) := fun x ↦
    (show IsUnit (l : T.residueField x) from by
      let ψ := (T.residue x).hom.comp
        ((T.presheaf.germ ⊤ x trivial).hom.comp p.appTop.hom)
      simpa only [map_natCast] using hY'.map ψ).invertible
  let := residue (ProjectiveLine Y) (ProjectiveLine Y ↘ Y)
  let := residue' (ProjectiveLine Y') (ProjectiveLine Y' ↘ Y')
  let := residue (diagonalSurface Y)
    (pullback.fst _ _ ≫ (ProjectiveLine Y ↘ Y))
  let := residue' (diagonalSurface Y')
    (pullback.fst _ _ ≫ (ProjectiveLine Y' ↘ Y'))
  obtain ⟨p, hp⟩ := realization_zl_endpoint l (baseP g)
  obtain ⟨w, hw⟩ := realization_zl_endpoint l (baseW g)
  let endpoints : PullbackEndpoints (Profinite.continuousMapRingObj.{u} ℤ_[l])
      g (zlLine l) (spIntegralComparison (baseP g) l (bottomField l))
      (spIntegralComparison (baseW g) l (bottomField l)) :=
    ⟨diagonalClassUnitEndpoint _ g, diagonalClassUnitEndpoint _ (baseP g),
      ⟨p, hp⟩, ⟨w, hw⟩⟩
  have := source_map_isIso _ g geometry endpoints.cP
  exact ⟨⟨geometry, endpoints,
    asIso (sourcePullbackMap _ g geometry.diagonal_square endpoints.cP), rfl⟩⟩

private theorem transportedEndpoint_change
    {C C' E E' : Type*} [Category C] [Category C'] [Category E] [Category E']
    (P : C ⥤ C') (F : C ⥤ E) (F' : C' ⥤ E') (V W : E ⥤ E')
    [F'.Full] [F'.Faithful] (e : P ⋙ F' ≅ F ⋙ V) (δ : V ≅ W)
    {X : C} {X' : C'} {A : E} {A' : E'}
    (s : F.obj X ≅ A) (s' : F'.obj X' ≅ A') (a : W.obj A ≅ A') :
    diagonalTransportedEndpoint P F F' V e s s' (δ.app A ≪≫ a) =
      diagonalTransportedEndpoint P F F' W (e ≪≫ Functor.isoWhiskerLeft F δ) s s' a := by
  apply Iso.ext
  apply F'.map_injective
  simp only [diagonalTransportedEndpoint, Functor.preimageIso_hom,
    Functor.map_preimage, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% δ.hom.naturality s.hom]

private theorem transportedEndpoint_single_comparison
    {A B C D : Type*}
    [Category A] [Abelian A] [Category B] [Abelian B]
    [Category C] [Abelian C] [Category D] [Abelian D]
    [hA : HasDerivedCategory A] [hB : HasDerivedCategory B]
    [hC : HasDerivedCategory C] [hD : HasDerivedCategory D]
    (P : A ⥤ B) (F : A ⥤ C) (F' : B ⥤ D) (V : C ⥤ D)
    [P.Additive] [F.Additive] [F'.Additive] [V.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [F'.Full] [F'.Faithful]
    [F'.mapDerivedCategory.Full] [F'.mapDerivedCategory.Faithful]
    (W : DerivedCategory C ⥤ DerivedCategory D) (δ : W ≅ V.mapDerivedCategory)
    (e : P ⋙ F' ≅ F ⋙ V) {X : A} {X' : B} {Y : C} {Y' : D}
    (s : F.obj X ≅ Y) (s' : F'.obj X' ≅ Y') (b : V.obj Y ≅ Y') :
    diagonalTransportedEndpoint P.mapDerivedCategory F.mapDerivedCategory
        F'.mapDerivedCategory W
        (Functor.mapDerivedCategorySquareIso e ≪≫
          Functor.isoWhiskerLeft F.mapDerivedCategory δ.symm)
        (diagonalRealizedSingleSource F s) (diagonalRealizedSingleSource F' s')
        ((δ.app ((DerivedCategory.singleFunctor C 0).obj Y) ≪≫
          (V.mapDerivedCategorySingleFunctor 0).app Y) ≪≫
          (DerivedCategory.singleFunctor D 0).mapIso b) =
      (P.mapDerivedCategorySingleFunctor 0).app X ≪≫
        (DerivedCategory.singleFunctor B 0).mapIso
          (diagonalTransportedEndpoint P F F' V e s s' b) := by
  let a := (V.mapDerivedCategorySingleFunctor 0).app Y ≪≫
    (DerivedCategory.singleFunctor D 0).mapIso b
  have he : (Functor.mapDerivedCategorySquareIso e ≪≫
        Functor.isoWhiskerLeft F.mapDerivedCategory δ.symm) ≪≫
      Functor.isoWhiskerLeft F.mapDerivedCategory δ =
        Functor.mapDerivedCategorySquareIso e := by
    rw [Iso.trans_assoc, ← Functor.isoWhiskerLeft_trans, Iso.symm_self_id,
      Functor.isoWhiskerLeft_refl, Iso.trans_refl]
  have ht := transportedEndpoint_change P.mapDerivedCategory F.mapDerivedCategory
    F'.mapDerivedCategory W V.mapDerivedCategory
    (Functor.mapDerivedCategorySquareIso e ≪≫
      Functor.isoWhiskerLeft F.mapDerivedCategory δ.symm) δ
    (diagonalRealizedSingleSource F s) (diagonalRealizedSingleSource F' s') a
  rw [he] at ht
  have h := diagonalTransportedSingleEndpoint P F F' V e s s' b
  refine Eq.trans ?_ h
  simpa only [a, Iso.trans_assoc] using ht

private theorem transportedEndpoint_inverse_normalization
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    (P : C ⥤ C') (F : C ⥤ D) (F' : C' ⥤ D') (V : D ⥤ D')
    [F'.Full] [F'.Faithful] (e : P ⋙ F' ≅ F ⋙ V)
    {X : C} {X' : C'} {Y : D} {Y' : D'}
    (s : F.obj X ≅ Y) (s' : F'.obj X' ≅ Y') (b : V.obj Y ≅ Y') :
    e.inv.app X ≫ F'.map (diagonalTransportedEndpoint P F F' V e s s' b).hom =
      V.map s.hom ≫ b.hom ≫ s'.inv := by
  apply (cancel_epi (e.hom.app X)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  simpa only [Category.assoc] using ((Iso.comp_inv_eq s').mpr
    (diagonalTransportedEndpoint_normalization P F F' V e s s' b)).symm

private theorem adjunct_conjugate_of_eq
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {X Y : C} {X' Y' : D} (s : X ≅ Y) (s' : X' ≅ Y')
    (a : L.obj X ⟶ X') (b : L.obj Y ⟶ Y')
    (ha : a = L.map s.hom ≫ b ≫ s'.inv) :
    adj.homEquiv _ _ a = s.hom ≫ adj.homEquiv _ _ b ≫ R.map s'.inv := by
  simp only [ha, adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]

private theorem underlying_sandwich_conjugate
    {C D : Type*} [Category C] [Category D] (V : D ⥤ C)
    {X Y S : C} {X' Y' S' : D}
    (s : X ≅ Y) (s' : X' ≅ Y') (r : X ≅ S) (r' : X' ≅ S')
    (a : X ⟶ V.obj X') (b : Y ⟶ V.obj Y') (m : S ⟶ V.obj S')
    (hm : m = r.inv ≫ a ≫ V.map r'.hom)
    (ha : a = s.hom ≫ b ≫ V.map s'.inv) :
    m = (r.symm ≪≫ s).hom ≫ b ≫ V.map (r'.symm ≪≫ s').inv := by
  simp only [hm, ha, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.map_comp, Category.assoc]

private theorem generator_conjugate_transpose
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {I S T : C} {I' S' T' : D}
    (σ : S ≅ T) (σ' : S' ≅ T')
    (genMap : I ⟶ S) (genMap' : I' ⟶ S') (u : I ⟶ T) (u' : I' ⟶ T')
    (b : L.obj I ⟶ I') (q : T ⟶ R.obj T') (a : S ⟶ R.obj S')
    (ha : a = σ.hom ≫ q ≫ R.map σ'.inv)
    (hu : genMap ≫ σ.hom = u) (hu' : genMap' ≫ σ'.hom = u')
    (hq : u ≫ q = adj.homEquiv I T' (b ≫ u')) :
    genMap ≫ a = adj.homEquiv I S' (b ≫ genMap') := by
  calc
    genMap ≫ a = u ≫ q ≫ R.map σ'.inv := by
      simp only [ha, ← hu, Category.assoc]
    _ = adj.homEquiv I T' (b ≫ u') ≫ R.map σ'.inv := by
      rw [← Category.assoc, hq]
    _ = adj.homEquiv I S' ((b ≫ u') ≫ σ'.inv) := by
      rw [Adjunction.homEquiv_naturality_right adj (b ≫ u') σ'.inv]
    _ = adj.homEquiv I S' (b ≫ genMap') := by
      rw [← hu']
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private def ordinarySystemSource (f : DiagonalClassPullbackFrame l g d d' e e') :=
  f.ordinaryReduction.hom.app (diagonalIntegralSource Y) ≫
    D'.ordinary.E.map (diagonalBoundarySource (baseW g) (baseP g)
      (diagonalBaseChange_cartesian g).toCommSq)

private def OrdinaryGeneratorNormalization
    (e : CompletedRealization l (diagonalSurface Y))
    (s : e.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y) : Prop :=
  diagonalCompletedGenerator l Y ≫ e.underlying.inv.app (diagonalCompletedSource l Y) ≫
    s.hom.hom = (lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
      η[condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) (ProjectiveLine Y)]

private theorem source_generator_unit
    (eP : CompletedRealization l (ProjectiveLine Y))
    (eW : CompletedRealization l (diagonalSurface Y))
    (s : eW.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (hs : HEq (eW.underlying.inv.app (diagonalCompletedSource l Y) ≫ s.hom.hom)
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        (eP.underlying.inv.app (SheafOfModules.unit
          (Scheme.purTwistRing (ProjectiveLine Y)
            (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))) ≫ eP.unitIso.hom.hom))) :
    OrdinaryGeneratorNormalization eW s := by
  unfold OrdinaryGeneratorNormalization
  calc
    _ = diagonalCompletedGenerator l Y ≫
        (lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
          (eP.underlying.inv.app (SheafOfModules.unit
            (Scheme.purTwistRing (ProjectiveLine Y)
              (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))) ≫
            eP.unitIso.hom.hom) :=
      congrArg (fun t ↦ diagonalCompletedGenerator l Y ≫ t) (eq_of_heq hs)
    _ = _ := by
      erw [completed_generator_unit, ← Functor.map_comp]
      apply congrArg (lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
      simpa only [unitRealizationIso, Iso.trans_hom, Iso.symm_hom,
        Iso.app_inv, Functor.mapIso_hom] using! unitRealization_one l (ProjectiveLine Y) eP

private def source_reduction_single
    (f : DiagonalClassPullbackFrame l g d d' e e') :=
  diagonal_congruence_apply% (diagonalReduction_normalized_single_square
      (hA := inferInstanceAs (HasDerivedCategory.{u + 1}
        (Sheaf (Scheme.ProEt.topology (diagonalSurface Y)) Ab.{u + 1})))
      (hC := inferInstanceAs (HasDerivedCategory.{u + 1}
        (Sheaf (Scheme.ProEt.topology (diagonalSurface Y')) Ab.{u + 1})))
      (hBS := inferInstanceAs
        (HasDerivedCategory.{u + 1} (DiagonalSystems l (diagonalSurface Y))))
      (hDS := inferInstanceAs
        (HasDerivedCategory.{u + 1} (DiagonalSystems l (diagonalSurface Y'))))
      l (diagonalScalarExtension l (diagonalSurface Y))
      (diagonalScalarExtension l (diagonalSurface Y'))
      (upperStar Ab.{u + 1} (baseW g)) (diagonalClassPull l (baseW g)))
    arguments [D, D', f.ordinaryReduction, f.reduction, diagonalIntegralSource Y,
      f.reduction_computation
        ((CochainComplex.singleFunctor _ 0).obj (diagonalIntegralSource Y))
        (source_single_regular l Y),
      diagonalIntegralSource Y',
      diagonalBoundarySource (baseW g) (baseP g) (diagonalBaseChange_cartesian g).toCommSq,
      d.a, d'.a, d.a_normalization, d'.a_normalization]

/-- Scalar direct image and forgetting agree on underlying sheaf objects.
Source: blueprint diagonal coefficient changes (3), ordinary adjunction comparison.
Proof: both functors precompose the sheaf and keep its underlying additive group. -/
private theorem scalarLowerStarUnderlying_obj_eq (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) (M : DiagonalMod l X) :
    (diagonalForget l S).obj
        ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).obj M) =
      (lowerStar Ab.{u + 1} f).obj ((diagonalForget l X).obj M) := rfl

private def ordinaryCompletedSource (f : DiagonalClassPullbackFrame l g d d' e e')
    (s : e.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (s' : e'.F.obj (diagonalCompletedSource l Y') ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y') :=
  diagonalTransportedEndpoint (diagonalRealizationPull l (baseW g)) e.F e'.F
    (CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g))
    f.realization s s' f.data.supported

private def ordinarySourceUnderlyingIso
    (e : CompletedRealization l (diagonalSurface Y))
    (s : e.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y) :
    (diagonalForget l (diagonalSurface Y)).obj
        ((diagonalCompletedRestriction l (diagonalSurface Y)).obj
          (diagonalCompletedSource l Y)) ≅
      (lowerStar Ab.{u + 1} (diagonalImmersion Y)).obj
        (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) (ProjectiveLine Y)) := by
  diagonal_congruence_exact ((e.underlying.app (diagonalCompletedSource l Y)).symm ≪≫
    (Mod.forget (condensedRingObj
      (Profinite.continuousMapRingObj.{u} ℤ_[l]) (diagonalSurface Y))).mapIso s)

private theorem ordinarySourceIso_generator
    (e : CompletedRealization l (diagonalSurface Y))
    (s : e.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (hn : OrdinaryGeneratorNormalization e s) :
    diagonalCompletedGenerator l Y ≫ (ordinarySourceUnderlyingIso e s).hom =
      (lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        η[condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) (ProjectiveLine Y)] := by
  diagonal_congruence_exact hn

private def ordinarySourceAdjunct
    (f : DiagonalClassPullbackFrame l g d d' e e')
    (s : e.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (s' : e'.F.obj (diagonalCompletedSource l Y') ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y') :
    (diagonalForget l (diagonalSurface Y)).obj
        ((diagonalCompletedRestriction l (diagonalSurface Y)).obj
          (diagonalCompletedSource l Y)) ⟶
      (lowerStar Ab.{u + 1} (baseW g)).obj
        ((diagonalForget l (diagonalSurface Y')).obj
          ((diagonalCompletedRestriction l (diagonalSurface Y')).obj
            (diagonalCompletedSource l Y'))) :=
  Eq.mp (congrArg
    (fun T : Sheaf (Scheme.ProEt.topology (diagonalSurface Y)) Ab.{u + 1} ↦
      (diagonalForget l (diagonalSurface Y)).obj
          ((diagonalCompletedRestriction l (diagonalSurface Y)).obj
            (diagonalCompletedSource l Y)) ⟶ T)
    (scalarLowerStarUnderlying_obj_eq l (baseW g)
      ((diagonalCompletedRestriction l (diagonalSurface Y')).obj
        (diagonalCompletedSource l Y'))))
    ((diagonalForget l (diagonalSurface Y)).map
      ((upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) (baseW g)).homEquiv
        ((diagonalCompletedRestriction l (diagonalSurface Y)).obj
          (diagonalCompletedSource l Y))
        ((diagonalCompletedRestriction l (diagonalSurface Y')).obj
          (diagonalCompletedSource l Y'))
        (f.scalar.hom.app (diagonalCompletedSource l Y) ≫
          (diagonalCompletedRestriction l (diagonalSurface Y')).map
            (ordinaryCompletedSource f s s').hom)))

private theorem ordinarySource_realization_equation
    (f : DiagonalClassPullbackFrame l g d d' e e')
    (s : e.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (s' : e'.F.obj (diagonalCompletedSource l Y') ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y') :
    f.realization.inv.app (diagonalCompletedSource l Y) ≫
        e'.F.map (ordinaryCompletedSource f s s').hom =
      (CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g)).map s.hom ≫
        f.data.supported.hom ≫ s'.inv := by
  diagonal_congruence_exact (transportedEndpoint_inverse_normalization
    (diagonalRealizationPull l (baseW g)) e.F e'.F
    (CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g))
    f.realization s s' f.data.supported)

private theorem ordinarySource_condensed_transpose
    (f : DiagonalClassPullbackFrame l g d d' e e')
    (s : e.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (s' : e'.F.obj (diagonalCompletedSource l Y') ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y') :
    (CondensedRing.upperStarLowerStarAdjunction
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g)).homEquiv _ _
        (f.realization.inv.app (diagonalCompletedSource l Y) ≫
          e'.F.map (ordinaryCompletedSource f s s').hom) =
      s.hom ≫ (CondensedRing.upperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g)).homEquiv _ _
          f.data.supported.hom ≫
        (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l])
          (baseW g)).map s'.inv := by
  diagonal_congruence_exact (adjunct_conjugate_of_eq
    (CondensedRing.upperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g)) s s'
    (f.realization.inv.app (diagonalCompletedSource l Y) ≫
      e'.F.map (ordinaryCompletedSource f s s').hom) f.data.supported.hom
    (ordinarySource_realization_equation f s s'))

private theorem ordinarySource_underlying_transpose
    (f : DiagonalClassPullbackFrame l g d d' e e')
    (s : e.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (s' : e'.F.obj (diagonalCompletedSource l Y') ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y') :
    ((CondensedRing.upperStarLowerStarAdjunction
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g)).homEquiv _ _
        (f.realization.inv.app (diagonalCompletedSource l Y) ≫
          e'.F.map (ordinaryCompletedSource f s s').hom)).hom =
      s.hom.hom ≫ ((CondensedRing.upperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g)).homEquiv _ _
          f.data.supported.hom).hom ≫
        (lowerStar Ab.{u + 1} (baseW g)).map s'.inv.hom := by
  have h := diagonal_congruence_term% (congrArg
    (fun k : e.F.obj (diagonalCompletedSource l Y) ⟶
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g)).obj
        (e'.F.obj (diagonalCompletedSource l Y')) ↦ k.hom)
    (ordinarySource_condensed_transpose f s s'))
  diagonal_checked_exact (by
    simpa only [Mod.comp_hom', CondensedRing.lowerStar_map_hom] using! h)

private theorem ordinarySource_scalar_transpose
    (f : DiagonalClassPullbackFrame l g d d' e e')
    (s : e.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (s' : e'.F.obj (diagonalCompletedSource l Y') ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y') :
    ordinarySourceAdjunct f s s' =
      (ordinarySourceUnderlyingIso e s).hom ≫
        ((CondensedRing.upperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g)).homEquiv
          (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
          (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y') f.data.supported.hom).hom ≫
        (lowerStar Ab.{u + 1} (baseW g)).map (ordinarySourceUnderlyingIso e' s').inv := by
  have hObj := heq_of_eq (scalarLowerStarUnderlying_obj_eq l (baseW g)
    ((diagonalCompletedRestriction l (diagonalSurface Y')).obj
      (diagonalCompletedSource l Y')))
  have hm := diagonal_congruence_apply%
    (diagonalScalarRealization_transpose f
      (diagonalCompletedSource l Y) (diagonalCompletedSource l Y')) arguments[
        (ordinaryCompletedSource f s s').hom]
  have ha := ordinarySource_underlying_transpose f s s'
  have h := diagonal_congruence_apply%
    (underlying_sandwich_conjugate
      (X := (Mod.forget (condensedRingObj
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) (diagonalSurface Y))).obj
        (e.F.obj (diagonalCompletedSource l Y)))
      (Y := (Mod.forget (condensedRingObj
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) (diagonalSurface Y))).obj
          (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y))
      (S := (diagonalForget l (diagonalSurface Y)).obj
        ((diagonalCompletedRestriction l (diagonalSurface Y)).obj
          (diagonalCompletedSource l Y)))
      (X' := (Mod.forget (condensedRingObj
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) (diagonalSurface Y'))).obj
        (e'.F.obj (diagonalCompletedSource l Y')))
      (Y' := (Mod.forget (condensedRingObj
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) (diagonalSurface Y'))).obj
          (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y'))
      (S' := (diagonalForget l (diagonalSurface Y')).obj
        ((diagonalCompletedRestriction l (diagonalSurface Y')).obj
          (diagonalCompletedSource l Y')))
      (lowerStar Ab.{u + 1} (baseW g))) arguments[
      ((Mod.forget (condensedRingObj
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) (diagonalSurface Y))).mapIso s),
      ((Mod.forget (condensedRingObj
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) (diagonalSurface Y'))).mapIso s'),
      (e.underlying.app (diagonalCompletedSource l Y)),
      (e'.underlying.app (diagonalCompletedSource l Y')),
      (((CondensedRing.upperStarLowerStarAdjunction
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g)).homEquiv _ _
        (f.realization.inv.app (diagonalCompletedSource l Y) ≫
          e'.F.map (ordinaryCompletedSource f s s').hom)).hom),
      (((CondensedRing.upperStarLowerStarAdjunction
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g)).homEquiv _ _
        f.data.supported.hom).hom),
      (ordinarySourceAdjunct f s s'), hm, ha]
  diagonal_congruence_exact h

private theorem ordinarySupported_generator_transpose
    (f : DiagonalClassPullbackFrame l g d d' e e') :
    (lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        η[condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) (ProjectiveLine Y)] ≫
      ((CondensedRing.upperStarLowerStarAdjunction
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g)).homEquiv
        (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
        (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y') f.data.supported.hom).hom =
      (upperStarLowerStarAdjunction Ab.{u + 1} (baseW g)).homEquiv
        (diagonalIntegralSource Y)
        ((lowerStar Ab.{u + 1} (diagonalImmersion Y')).obj
          (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) (ProjectiveLine Y')))
        (diagonalBoundarySource (baseW g) (baseP g)
          (diagonalBaseChange_cartesian g).toCommSq ≫
          (lowerStar Ab.{u + 1} (diagonalImmersion Y')).map
            η[condensedRingObj
              (Profinite.continuousMapRingObj.{u} ℤ_[l]) (ProjectiveLine Y')]) := by
  rw [f.data.supported_normalization]
  diagonal_congruence_exact (diagonalSupportedGenerator_pullback
    (Profinite.continuousMapRingObj.{u} ℤ_[l]) g
    f.data.geometry f.data.endpoints.cP)

private theorem completed_source_generator_transpose
    (f : DiagonalClassPullbackFrame l g d d' e e')
    (s : e.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (s' : e'.F.obj (diagonalCompletedSource l Y') ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y')
    (hn : OrdinaryGeneratorNormalization e s)
    (hn' : OrdinaryGeneratorNormalization e' s') :
    diagonalCompletedGenerator l Y ≫ (diagonalForget l (diagonalSurface Y)).map
      ((upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) (baseW g)).homEquiv
        ((diagonalCompletedRestriction l (diagonalSurface Y)).obj
          (diagonalCompletedSource l Y))
        ((diagonalCompletedRestriction l (diagonalSurface Y')).obj
          (diagonalCompletedSource l Y'))
        (f.scalar.hom.app (diagonalCompletedSource l Y) ≫
          (diagonalCompletedRestriction l (diagonalSurface Y')).map
            (ordinaryCompletedSource f s s').hom)) =
      (upperStarLowerStarAdjunction Ab.{u + 1} (baseW g)).homEquiv
        (diagonalIntegralSource Y)
        ((diagonalForget l (diagonalSurface Y')).obj
          ((diagonalCompletedRestriction l (diagonalSurface Y')).obj
            (diagonalCompletedSource l Y')))
        (diagonalBoundarySource (baseW g) (baseP g)
          (diagonalBaseChange_cartesian g).toCommSq ≫ diagonalCompletedGenerator l Y') := by
  have hObj := heq_of_eq (scalarLowerStarUnderlying_obj_eq l (baseW g)
    ((diagonalCompletedRestriction l (diagonalSurface Y')).obj
      (diagonalCompletedSource l Y')))
  have h := diagonal_congruence_apply%
    (generator_conjugate_transpose
      (I := diagonalIntegralSource Y) (I' := diagonalIntegralSource Y')
      (upperStarLowerStarAdjunction Ab.{u + 1} (baseW g))
      (ordinarySourceUnderlyingIso e s) (ordinarySourceUnderlyingIso e' s')) arguments[
      (diagonalCompletedGenerator l Y), (diagonalCompletedGenerator l Y'),
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        η[condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) (ProjectiveLine Y)]),
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y')).map
        η[condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) (ProjectiveLine Y')]),
      (diagonalBoundarySource (baseW g) (baseP g)
        (diagonalBaseChange_cartesian g).toCommSq),
      ((((CondensedRing.upperStarLowerStarAdjunction
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g)).homEquiv
        (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
        (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y')) f.data.supported.hom).hom),
      (ordinarySourceAdjunct f s s'), (ordinarySource_scalar_transpose f s s'),
      (ordinarySourceIso_generator e s hn), (ordinarySourceIso_generator e' s' hn'),
      (ordinarySupported_generator_transpose f)]
  diagonal_congruence_exact h

-- Share the endpoint application so its normalization proof is reused verbatim.

private def ordinarySingleSourceComparison
    (f : DiagonalClassPullbackFrame l g d d' e e')
    (s : e.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (s' : e'.F.obj (diagonalCompletedSource l Y') ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y') :=
  (diagonal_congruence_apply% (f.sourceComparison) arguments [s, s']).hom

private theorem sourceComparison_single
    (f : DiagonalClassPullbackFrame l g d d' e e')
    (s : e.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (s' : e'.F.obj (diagonalCompletedSource l Y') ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y') :
    HEq (ordinarySingleSourceComparison f s s')
      (diagonalSingleEndpointMap
        (A := DiagonalCompleted l (diagonalSurface Y))
        (B := DiagonalCompleted l (diagonalSurface Y'))
        (hA := inferInstanceAs (HasDerivedCategory.{u + 1}
          (DiagonalCompleted l (diagonalSurface Y))))
        (hB := inferInstanceAs (HasDerivedCategory.{u + 1}
          (DiagonalCompleted l (diagonalSurface Y'))))
        (diagonalRealizationPull l (baseW g)) (ordinaryCompletedSource f s s').hom) := by
  have h := diagonal_congruence_apply%
    (transportedEndpoint_single_comparison
      (hA := inferInstanceAs (HasDerivedCategory.{u + 1}
        (DiagonalCompleted l (diagonalSurface Y))))
      (hB := inferInstanceAs (HasDerivedCategory.{u + 1}
        (DiagonalCompleted l (diagonalSurface Y'))))
      (hC := inferInstanceAs (HasDerivedCategory.{u + 1}
        (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) (diagonalSurface Y))))
      (hD := inferInstanceAs (HasDerivedCategory.{u + 1}
        (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) (diagonalSurface Y'))))
      (diagonalRealizationPull l (baseW g)) e.F e'.F
      (CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g))
      (X := diagonalCompletedSource l Y) (X' := diagonalCompletedSource l Y')
      (Y := source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
      (Y' := source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y')) arguments[
      (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g)),
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) (baseW g)),
      f.realization, s, s', f.data.supported]
  have hHom := diagonal_congruence_term% (congrArg Iso.hom h)
  have hHEq := heq_of_eq hHom
  diagonal_congruence_exact hHEq

private def ordinarySourceCone (d : ClassLimitPresentation l Y hY D) :
    Cone (D.ordinary.E.obj (diagonalIntegralSource Y)) :=
  Cone.mk _ ((Functor.const ℕᵒᵖ).map d.s₀.hom ≫
    (limit.cone (D.ordinary.E.obj (diagonalIntegralSource Y))).π)

private theorem finite_residue_torsion (l : ℕ) [Fact l.Prime] (n : ℕ)
    (M : ModuleCat.{u + 1} (diagonalResidue.{u} l n)) (y : M) :
    l ^ (n + 1) • y = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (diagonalResidue.{u} l n),
    cartierResidue_cast l (n + 1), zero_smul]

private theorem finite_source_ext
    (d' : ClassLimitPresentation l Y' hY' D') (n : ℕ)
    (a b : (diagonalClassPull l (baseW g)).obj
        ((diagonalCompletedRestriction l (diagonalSurface Y)).obj
          (diagonalCompletedSource l Y)) ⟶
      (D'.ordinary.E.obj (diagonalIntegralSource Y')).obj (op n))
    (h : (upperStar Ab.{u + 1} (baseW g)).map (diagonalCompletedGenerator l Y) ≫
        (forgetPullbackIso l (baseW g)).inv.app _ ≫
          (diagonalForget l (diagonalSurface Y')).map a =
      (upperStar Ab.{u + 1} (baseW g)).map (diagonalCompletedGenerator l Y) ≫
        (forgetPullbackIso l (baseW g)).inv.app _ ≫
          (diagonalForget l (diagonalSurface Y')).map b) : a = b := by
  have hz := d'.finite_normalization
  unfold FiniteCartierNormalization diagonalFiniteCycleNormalization at hz
  obtain ⟨z, _⟩ := hz n
  have : (diagonalForget l (diagonalSurface Y')).Faithful := by
    unfold diagonalForget
    infer_instance
  apply (diagonalForget l (diagonalSurface Y')).map_injective
  apply (cancel_epi ((forgetPullbackIso l (baseW g)).inv.app _)).mp
  apply (cancel_mono ((diagonalForget l (diagonalSurface Y')).map z.hom)).mp
  apply diagonalPulledCompletedGenerator_hom_ext l g n
    ((sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y'))
      (forget₂ (ModuleCat.{u + 1} (diagonalResidue.{u} l n)) Ab.{u + 1})).obj
        (geoCartierConstant (diagonalResidue.{u} l n) (ProjectiveLine Y')))
  · intro V y
    exact finite_residue_torsion l n
      ((geoCartierConstant (diagonalResidue.{u} l n) (ProjectiveLine Y')).obj.obj V) y
  · simpa only [Category.assoc] using congrArg
      (fun t ↦ t ≫ (diagonalForget l (diagonalSurface Y')).map z.hom) h

private theorem source_cone_generator_transpose
    (f : DiagonalClassPullbackFrame l g d d' e e') (n : ℕ) :
    let A := upperStarLowerStarAdjunction Ab.{u + 1} (baseW g)
    let B := upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) (baseW g)
    diagonalCompletedGenerator l Y ≫ (diagonalForget l (diagonalSurface Y)).map
        (B.homEquiv _ _ ((diagonalClassPull l (baseW g)).map
          ((ordinarySourceCone d).π.app (op n)) ≫ (ordinarySystemSource f).app (op n))) =
      A.homEquiv _ _ ((diagonalScalarAdjunction l (diagonalSurface Y')).unit.app
          ((upperStar Ab.{u + 1} (baseW g)).obj (diagonalIntegralSource Y)) ≫
        (diagonalForget l (diagonalSurface Y')).map
          ((D'.ordinary.π n).app _ ≫
            (D'.ordinary.E.map (diagonalBoundarySource (baseW g) (baseP g)
              (diagonalBaseChange_cartesian g).toCommSq)).app (op n))) := by
  dsimp only
  rw [Adjunction.homEquiv_naturality_left, Functor.map_comp]
  change diagonalCompletedGenerator l Y ≫
    (diagonalForget l (diagonalSurface Y)).map
      (d.s₀.hom ≫ limit.π _ (op n)) ≫ _ = _
  rw [reassoc_of% d.source_normalization n]
  rw [← Functor.map_comp]
  erw [← Adjunction.homEquiv_naturality_left]
  have hred := congrArg
    (fun t ↦ t ≫ (D'.ordinary.E.map (diagonalBoundarySource (baseW g) (baseP g)
      (diagonalBaseChange_cartesian g).toCommSq)).app (op n))
      (f.reduction_quotients n (diagonalIntegralSource Y))
  simp only [ordinarySystemSource, NatTrans.comp_app, Category.assoc] at hred ⊢
  have hu := diagonalScalarPullback_unit l (baseW g) (diagonalIntegralSource Y)
  erw [hred, Adjunction.homEquiv_naturality_right, Functor.map_comp,
    ← Category.assoc, hu]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rfl

private theorem forgetPullback_homEquiv {X S : Scheme.{u}} (f : X ⟶ S)
    (M : DiagonalMod l S) (N : DiagonalMod l X)
    (a : (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).obj M ⟶ N) :
    (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _
        ((forgetPullbackIso l f).inv.app M ≫ (diagonalForget l X).map a) =
      (diagonalForget l S).map
        ((upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).homEquiv _ _ a) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    ← forgetPullbackIso_unit, Category.assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp, Functor.map_comp]
  rfl

private theorem forgetPullback_generator_transpose {X S : Scheme.{u}} (f : X ⟶ S)
    (M : DiagonalMod l S) (N : DiagonalMod l X)
    {T : Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}}
    (gen : T ⟶ (diagonalForget l S).obj M)
    (a : (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).obj M ⟶ N) :
    (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _
        ((upperStar Ab.{u + 1} f).map gen ≫
          (forgetPullbackIso l f).inv.app M ≫ (diagonalForget l X).map a) =
      gen ≫ (diagonalForget l S).map
        ((upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).homEquiv _ _ a) := by
  rw [Adjunction.homEquiv_naturality_left, forgetPullback_homEquiv]

private theorem finite_source_generator_naturality
    (d' : ClassLimitPresentation l Y' hY' D') (n : ℕ) :
    (diagonalScalarAdjunction l (diagonalSurface Y')).unit.app
        ((upperStar Ab.{u + 1} (baseW g)).obj (diagonalIntegralSource Y)) ≫
      (diagonalForget l (diagonalSurface Y')).map
        ((D'.ordinary.π n).app _ ≫
          (D'.ordinary.E.map (diagonalBoundarySource (baseW g) (baseP g)
            (diagonalBaseChange_cartesian g).toCommSq)).app (op n)) =
      diagonalBoundarySource (baseW g) (baseP g)
          (diagonalBaseChange_cartesian g).toCommSq ≫
        diagonalCompletedGenerator l Y' ≫
          (diagonalForget l (diagonalSurface Y')).map
            ((ordinarySourceCone d').π.app (op n)) := by
  simp only [ordinarySourceCone, NatTrans.comp_app, Functor.const_map_app, limit.cone_π]
  rw [d'.source_normalization n]
  let b := diagonalBoundarySource (baseW g) (baseP g)
    (diagonalBaseChange_cartesian g).toCommSq
  have hη := (diagonalScalarAdjunction l (diagonalSurface Y')).unit.naturality b
  have hπ := (D'.ordinary.π n).naturality b
  dsimp only [Functor.comp_map, Functor.id_map] at hη hπ
  rw [← Category.assoc, hη, Category.assoc, ← Functor.map_comp]
  exact congrArg (fun t ↦ (diagonalScalarAdjunction l (diagonalSurface Y')).unit.app _ ≫
    (diagonalForget l (diagonalSurface Y')).map t) hπ.symm

private theorem ordinary_source_cone
    (f : DiagonalClassPullbackFrame l g d d' e e')
    (s : e.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (s' : e'.F.obj (diagonalCompletedSource l Y') ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y')
    (hn : OrdinaryGeneratorNormalization e s)
    (hn' : OrdinaryGeneratorNormalization e' s') :
    ((diagonalClassPull l (baseW g)).mapCone (ordinarySourceCone d)).π ≫
        ordinarySystemSource f =
      (Functor.const ℕᵒᵖ).map (f.scalar.hom.app (diagonalCompletedSource l Y) ≫
        (diagonalCompletedRestriction l (diagonalSurface Y')).map
          (ordinaryCompletedSource f s s').hom) ≫ (ordinarySourceCone d').π := by
  apply NatTrans.ext
  funext n
  obtain ⟨n⟩ := n
  dsimp only [NatTrans.comp_app, Functor.mapCone_π_app, Functor.const_map_app,
    Functor.mapCone_pt, Functor.const_obj_obj]
  apply finite_source_ext d' n
  apply ((upperStarLowerStarAdjunction Ab.{u + 1} (baseW g)).homEquiv _ _).injective
  let M : DiagonalMod l (diagonalSurface Y) :=
    (diagonalCompletedRestriction l (diagonalSurface Y)).obj (diagonalCompletedSource l Y)
  let N : DiagonalMod l (diagonalSurface Y') :=
    (D'.ordinary.E.obj (diagonalIntegralSource Y')).obj (op n)
  let a : (diagonalClassPull l (baseW g)).obj M ⟶ N :=
    (diagonalClassPull l (baseW g)).map ((ordinarySourceCone d).π.app (op n)) ≫
      (ordinarySystemSource f).app (op n)
  let b : (diagonalClassPull l (baseW g)).obj M ⟶ N :=
    (f.scalar.hom.app (diagonalCompletedSource l Y) ≫
      (diagonalCompletedRestriction l (diagonalSurface Y')).map
        (ordinaryCompletedSource f s s').hom) ≫ (ordinarySourceCone d').π.app (op n)
  have ha := forgetPullback_generator_transpose (l := l) (baseW g) M N
    (diagonalCompletedGenerator l Y) a
  have hb := forgetPullback_generator_transpose (l := l) (baseW g) M N
    (diagonalCompletedGenerator l Y) b
  refine ha.trans (Eq.trans ?_ hb.symm)
  rw [source_cone_generator_transpose f n]
  have hγn := congrArg
    (fun t ↦ t ≫ (lowerStar Ab.{u + 1} (baseW g)).map
      ((diagonalForget l (diagonalSurface Y')).map
        ((ordinarySourceCone d').π.app (op n))))
    (completed_source_generator_transpose f s s' hn hn')
  calc
    _ = (upperStarLowerStarAdjunction Ab.{u + 1} (baseW g)).homEquiv _ _
        (diagonalBoundarySource (baseW g) (baseP g)
            (diagonalBaseChange_cartesian g).toCommSq ≫
          diagonalCompletedGenerator l Y' ≫
            (diagonalForget l (diagonalSurface Y')).map
              ((ordinarySourceCone d').π.app (op n))) :=
      congrArg ((upperStarLowerStarAdjunction Ab.{u + 1} (baseW g)).homEquiv _ _)
        (finite_source_generator_naturality d' n)
    _ = _ := by
      simpa only [Adjunction.homEquiv_naturality_right, Functor.map_comp,
        Category.assoc] using! hγn.symm

private theorem sourceMap_as_cone (d : ClassLimitPresentation l Y hY D) :
    d.sourceMap =
      ((diagonalCompletedRestriction l (diagonalSurface Y)).mapDerivedCategorySingleFunctor
          0).hom.app (diagonalCompletedSource l Y) ≫
        diagonalTraceConeMap d.L _ (ordinarySourceCone d) ≫ d.L.R.map d.a.inv := by
  have h : limit.lift _ (ordinarySourceCone d) = d.s₀.hom := by
    apply limit.hom_ext
    intro n
    simpa only [ordinarySourceCone, NatTrans.comp_app,
      Functor.const_map_app, limit.cone_π] using limit.lift_π (ordinarySourceCone d) n
  simp only [ClassLimitPresentation.sourceMap, diagonalSingleLimitComparison,
    diagonalTraceConeMap, h, Category.assoc]

private theorem source_limit_of_cone
    (f : DiagonalClassPullbackFrame l g d d' e e')
    (s : e.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (s' : e'.F.obj (diagonalCompletedSource l Y') ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y')
    (hcone : ((diagonalClassPull l (baseW g)).mapCone (ordinarySourceCone d)).π ≫
        ordinarySystemSource f =
      (Functor.const ℕᵒᵖ).map (f.scalar.hom.app (diagonalCompletedSource l Y) ≫
        (diagonalCompletedRestriction l (diagonalSurface Y')).map
          (ordinaryCompletedSource f s s').hom) ≫ (ordinarySourceCone d').π) :
    (diagonalClassPull l (baseW g)).mapDerivedCategory.map d.sourceMap ≫
        f.limitComparison.app _ ≫ d'.L.R.map f.systemSource =
      f.scalarComparison.hom.app (diagonalCompletedDomain l Y) ≫
        (diagonalCompletedUnderlying l (diagonalSurface Y')).map
          (ordinarySingleSourceComparison f s s') ≫ d'.sourceMap := by
  let p : diagonalSurface Y ⟶ Y :=
    pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) ≫ (ProjectiveLine Y ↘ Y)
  let p' : diagonalSurface Y' ⟶ Y' :=
    pullback.fst (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y') ≫ (ProjectiveLine Y' ↘ Y')
  let : ∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x) :=
    fun x ↦ (residueUnits l p hY x).invertible
  let : ∀ x : diagonalSurface Y', Invertible (l : (diagonalSurface Y').residueField x) :=
    fun x ↦ (residueUnits l p' hY' x).invertible
  have hW : IsUnit (l : Γ(diagonalSurface Y, ⊤)) := by
    simpa only [map_natCast] using hY.map p.appTop.hom
  obtain ⟨c, hc⟩ := normalizedChern l (diagonalSurface Y) hW
  obtain ⟨r, ⟨a⟩⟩ := exists_diagonalTraceCoefficientRestriction l (diagonalSurface Y) c hc
  have hb := (diagonalRlim_pullback_endpoints l (baseW g) d'.L d.L f.adj' f.adj
    f.counit' f.projections' f.counit f.projections c r a).2.2.2.1
      _ (ordinarySourceCone d)
  have h := diagonal_congruence_apply% (diagonalSingleLimit_transport
      (hA := inferInstanceAs (HasDerivedCategory.{u + 1}
        (DiagonalCompleted l (diagonalSurface Y))))
      (hB := inferInstanceAs (HasDerivedCategory.{u + 1} (DiagonalMod l (diagonalSurface Y))))
      (hC := inferInstanceAs (HasDerivedCategory.{u + 1}
        (DiagonalCompleted l (diagonalSurface Y'))))
      (hD := inferInstanceAs (HasDerivedCategory.{u + 1} (DiagonalMod l (diagonalSurface Y'))))
      (hBS := inferInstanceAs
        (HasDerivedCategory.{u + 1} (DiagonalSystems l (diagonalSurface Y))))
      (hDS := inferInstanceAs
        (HasDerivedCategory.{u + 1} (DiagonalSystems l (diagonalSurface Y'))))
      (diagonalCompletedRestriction l (diagonalSurface Y)) (diagonalClassPull l (baseW g))
      (diagonalRealizationPull l (baseW g))
      (diagonalCompletedRestriction l (diagonalSurface Y'))
      (M := diagonalCompletedSource l Y) (M' := diagonalCompletedSource l Y')
      (S := D.ordinary.E.obj (diagonalIntegralSource Y))
      (S' := D'.ordinary.E.obj (diagonalIntegralSource Y')))
    arguments [f.scalar, d.L, d'.L, f.limitComparison,
      (ordinaryCompletedSource f s s').hom, ordinarySystemSource f,
      (ordinarySourceCone d).π, (ordinarySourceCone d').π,
      D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)),
      D'.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y')),
      d.a, d'.a, f.systemSource, hcone, source_reduction_single f, hb]
  have hComparison := sourceComparison_single f s s'
  rw [sourceMap_as_cone d, sourceMap_as_cone d']
  simp only [ordinarySourceCone,
    DiagonalClassPullbackFrame.scalarComparison, diagonalClassExactSquare,
    diagonalCompletedUnderlying, diagonalCompletedDomain, Functor.comp_obj,
    Iso.trans_hom] at h ⊢
  diagonal_congruence_exact h

/-- Closed-support and generator normalization of the source-limit endpoint.
There is no completed diagonal arrow in this statement.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-diagonal-tower/sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3),
closed base change and the supported constant-source endpoint.
(blueprint: lem-diagonal-class-source-limit-endpoint).

Proof: pull the global unit of the prime to both projective lines and surfaces.
Use the canonical monoidal unit pullbacks and the Cartesian integral Tate-line
comparisons to construct the two unit and line endpoints. The projective diagonal
is a closed immersion and its Cartesian pullback is the new diagonal. Apply
closed-support base change to its regular condensed coefficient module, with the
coefficient restrictions transported along the canonical constant-ring square.
Its forward map is the ordinary exchange followed by the regular-module unit
pullback, so it is exactly sourcePullbackMap. This constructs SourcePullback.
Apply diagonalClassPullbackFrame_exists to this ordinary supported data. It
provides the normalized reduction, constant/limit adjunction, scalar and realization
comparisons, and retains the supported data as its data field.

Compare the ordinary source cones at every quotient: the generator equation
for s₀, the normalized quotient equation for the reduction square, and the
scalar-unit adjunction equation give the same map on integral generators.
Local integer approximation detects these maps into prime-power torsion targets,
so the finite supported coefficient maps, and hence the full ordinary cones, agree.
Transpose the pulled cone under the normalized
constant/derived-limit adjunction. On K-injective resolutions its counit is the
ordinary cone, so both transposes agree as full strict-system morphisms.
The regular resolving-class equation identifies the reduction comparison used
here with the supplied one. Localize with the exact single comparisons.
Finally hs and hs' identify the supported realized endpoint with the closed
exchange above. Full faithfulness of the derived realization identifies its
transport with frame.sourceComparison. This proves limit_endpoint.
All cone comparisons are comparisons of ordinary sheaf morphisms or full
adjunction transposes; there is no detection of derived maps by evaluation.
The construction also applies to the empty base and to the prime two. -/
theorem diagonalClassSourceLimitEndpoint_exists (l : ℕ) [Fact l.Prime]
    (Y Y' : Scheme.{u})
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y')]
    (g : Y' ⟶ Y) (geometry : BaseSquares g)
    (hY : IsUnit (l : Γ(Y, ⊤))) (hY' : IsUnit (l : Γ(Y', ⊤)))
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (D' : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y')))
    (d : ClassLimitPresentation l Y hY D) (d' : ClassLimitPresentation l Y' hY' D')
    (eP : CompletedRealization l (ProjectiveLine Y))
    (eW : CompletedRealization l (diagonalSurface Y))
    (eP' : CompletedRealization l (ProjectiveLine Y'))
    (eW' : CompletedRealization l (diagonalSurface Y'))
    (s : eW.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (s' : eW'.F.obj (diagonalCompletedSource l Y') ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y')
    (hs : HEq (eW.underlying.inv.app (diagonalCompletedSource l Y) ≫ s.hom.hom)
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        (eP.underlying.inv.app (SheafOfModules.unit
          (Scheme.purTwistRing (ProjectiveLine Y)
            (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))) ≫ eP.unitIso.hom.hom)))
    (hs' : HEq (eW'.underlying.inv.app (diagonalCompletedSource l Y') ≫ s'.hom.hom)
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y')).map
        (eP'.underlying.inv.app (SheafOfModules.unit
          (Scheme.purTwistRing (ProjectiveLine Y')
            (Scheme.purTwistZlCompletion (ProjectiveLine Y') l))) ≫ eP'.unitIso.hom.hom))) :
    Nonempty (DiagonalClassSourceEndpoint (g := g) (d := d) (d' := d') s s') := by
  obtain ⟨data⟩ := ordinary_source_data l g geometry hY hY'
  obtain ⟨frame, _hframe⟩ := diagonalClassPullbackFrame_exists l g d d' eW eW' data
  refine ⟨⟨frame, ?_⟩⟩
  diagonal_congruence_exact (source_limit_of_cone frame s s'
    (ordinary_source_cone frame s s' (source_generator_unit eP eW s hs)
      (source_generator_unit eP' eW' s' hs')))

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
