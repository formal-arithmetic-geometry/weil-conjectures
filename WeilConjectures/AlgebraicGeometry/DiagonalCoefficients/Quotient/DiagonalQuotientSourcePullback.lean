/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientFamilyPullback
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-! # Ordinary quotient endpoints under geometric pullback

Source: diagonal tower coefficient changes, paragraph (3), scalar base change.
(blueprint: lem-diagonal-quotient-source-pullback).
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

attribute [local irreducible] quotientLine quotientLineMap derivedUpper derivedLower
  derivedScalars modelExchange singlePullback PullEndpoint.shift Endpoint.shift

private def scalarCompositor :
    Mod.extendScalarsObj (coefficientMap a X) ((CondensedRing.upperStar R f).obj M) ≅
      (CondensedRing.upperStar T f).obj (Mod.extendScalarsObj (coefficientMap a S) M) :=
  (CondensedRing.pullIso a f).app M

private def scalarExtendedIso (e : (CondensedRing.upperStar R f).obj M ≅ N) :
    Mod.extendScalarsObj (coefficientMap a X) ((CondensedRing.upperStar R f).obj M) ≅
      Mod.extendScalarsObj (coefficientMap a X) N :=
  (Mod.extendScalars (coefficientMap a X)).mapIso e

private def scalarIso (e : (CondensedRing.upperStar R f).obj M ≅ N) :
    (CondensedRing.upperStar T f).obj (Mod.extendScalarsObj (coefficientMap a S) M) ≅
      Mod.extendScalarsObj (coefficientMap a X) N :=
  (scalarCompositor a f (M := M)).symm ≪≫ scalarExtendedIso a f e

private theorem endpoint_raw {m : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X}
    (e : PullEndpoint R f M N m) :
    CondensedRing.upperStarUnitHom R f M ≫ e.iso.hom.hom = m := by
  apply ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).injective
  exact (CondensedRing.upperStarLowerStarAdjunction_homEquiv_hom R f M N e.iso.hom).symm.trans
    e.normalization

private theorem scalarIso_unit (e : (CondensedRing.upperStar R f).obj M ≅ N) :
    (upperStar Ab.{u + 1} f).map (Mod.extendUnitHom (coefficientMap a S) M) ≫
      CondensedRing.upperStarUnitHom T f (Mod.extendScalarsObj (coefficientMap a S) M) ≫
        (scalarIso a f e).hom.hom =
    CondensedRing.upperStarUnitHom R f M ≫ e.hom.hom ≫
      Mod.extendUnitHom (coefficientMap a X) N := by
  have h : CondensedRing.upperStarUnitHom R f M ≫
      Mod.extendUnitHom (coefficientMap a X) ((CondensedRing.upperStar R f).obj M) ≫
        (scalarCompositor a f (M := M)).hom.hom =
      (upperStar Ab.{u + 1} f).map (Mod.extendUnitHom (coefficientMap a S) M) ≫
        CondensedRing.upperStarUnitHom T f (Mod.extendScalarsObj (coefficientMap a S) M) :=
    CondensedRing.upperStarUnitHom_extendUnitHom_pullIso_hom_app_hom a f M
  have hi : (scalarCompositor a f (M := M)).hom.hom ≫
      (scalarCompositor a f (M := M)).inv.hom = 𝟙 _ := by
    simpa only [Mod.comp_hom', Mod.id_hom'] using
      congrArg Mod.Hom.hom (scalarCompositor a f (M := M)).hom_inv_id
  have hc := congrArg (fun k ↦ k ≫ (scalarCompositor a f (M := M)).inv.hom) h
  simp only [Category.assoc, hi, Category.comp_id] at hc
  have hn : Mod.extendUnitHom (coefficientMap a X) ((CondensedRing.upperStar R f).obj M) ≫
      (scalarExtendedIso a f e).hom.hom =
      e.hom.hom ≫ Mod.extendUnitHom (coefficientMap a X) N :=
    Mod.extendUnitHom_comp_extendScalars_map_hom (coefficientMap a X) e.hom
  dsimp only [scalarIso, Iso.trans_hom, Iso.symm_hom]
  erw [Mod.comp_hom']
  calc
    _ = CondensedRing.upperStarUnitHom R f M ≫
        Mod.extendUnitHom (coefficientMap a X) ((CondensedRing.upperStar R f).obj M) ≫
          (scalarExtendedIso a f e).hom.hom := by
      simpa only [Category.assoc] using
        congrArg (fun k ↦ k ≫ (scalarExtendedIso a f e).hom.hom) hc.symm
    _ = _ := by rw [hn]

private theorem raw_linear
    {M' : Modules T S} {N' : Modules T X}
    (k : (CondensedRing.upperStar T f).obj M' ⟶ N') :
    let m := CondensedRing.upperStarUnitHom T f M' ≫ k.hom
    (upperStar Ab.{u + 1} f).map γ[condensedRingObj T S,M'.X] ≫ m =
      Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} f) (condensedRingObj T S) M'.X ≫
        (condensedPullbackHom T f ⊗ₘ m) ≫ γ[condensedRingObj T X,N'.X] := by
  let q := Mod.extendUnit (condensedPullbackHom T f)
    (((upperStar Ab.{u + 1} f).mapMod (condensedRingObj T S)).obj M') ≫
      (Mod.comap (condensedPullbackHom T f)).map k
  have h := Mod.act_hom q
  change (Functor.LaxMonoidal.μ (upperStar Ab.{u + 1} f)
      (condensedRingObj T S) M'.X ≫
    (upperStar Ab.{u + 1} f).map γ[condensedRingObj T S,M'.X]) ≫
      (CondensedRing.upperStarUnitHom T f M' ≫ k.hom) =
    (upperStar Ab.{u + 1} f).obj (condensedRingObj T S) ◁
      (CondensedRing.upperStarUnitHom T f M' ≫ k.hom) ≫
      condensedPullbackHom T f ▷ N'.X ≫ γ[condensedRingObj T X,N'.X] at h
  have h' := congrArg (fun t ↦ Functor.OplaxMonoidal.δ
    (upperStar Ab.{u + 1} f) (condensedRingObj T S) M'.X ≫ t) h
  simp only [Category.assoc] at h'
  erw [Functor.Monoidal.δ_μ_assoc] at h'
  simpa only [Category.assoc, MonoidalCategory.tensorHom_def'] using h'

private theorem scalar_tensor (e : (CondensedRing.upperStar R f).obj M ≅ N) :
    let m := CondensedRing.upperStarUnitHom T f
      (Mod.extendScalarsObj (coefficientMap a S) M) ≫ (scalarIso a f e).hom.hom
    (upperStar Ab.{u + 1} f).map (Mod.extendπ (coefficientMap a S) M) ≫ m =
      Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} f) (condensedRingObj T S) M.X ≫
        (condensedPullbackHom T f ⊗ₘ
          (CondensedRing.upperStarUnitHom R f M ≫ e.hom.hom)) ≫
            Mod.extendπ (coefficientMap a X) N := by
  dsimp only
  erw [← Mod.whiskerLeft_extendUnitHom_smul' (coefficientMap a S) M,
    Functor.map_comp, Category.assoc, raw_linear f (scalarIso a f e).hom]
  erw [← Functor.OplaxMonoidal.δ_natural_right_assoc]
  simp only [MonoidalCategory.tensorHom_def', Category.assoc]
  erw [← whiskerLeft_comp_assoc]
  erw [scalarIso_unit a f e]
  simp only [whiskerLeft_comp_assoc]
  erw [whisker_exchange_assoc]
  erw [Mod.whiskerLeft_extendUnitHom_smul' (coefficientMap a X) N]

private theorem scalar_endpoint
    {m : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X}
    (e : PullEndpoint R f M N m) :
    ∃ m' : (upperStar Ab.{u + 1} f).obj
      (Mod.extendScalarsObj (coefficientMap a S) M).X ⟶
        (Mod.extendScalarsObj (coefficientMap a X) N).X,
      ScalarPullMap a f M N m m' ∧
      Nonempty (PullEndpoint T f (Mod.extendScalarsObj (coefficientMap a S) M)
        (Mod.extendScalarsObj (coefficientMap a X) N) m') := by
  let j := scalarIso a f e.iso
  refine ⟨CondensedRing.upperStarUnitHom T f _ ≫ j.hom.hom, ?_, ⟨⟨j, ?_⟩⟩⟩
  · unfold ScalarPullMap
    simpa only [endpoint_raw f e] using scalar_tensor a f e.iso
  · exact CondensedRing.upperStarLowerStarAdjunction_homEquiv_hom T f _ _ j.hom

private theorem quotient_endpoint
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (n : ℕ) {X S : Scheme.{u}} (f : X ⟶ S)
    (e : PullEndpoint (Profinite.padicIntegersRingObj.{u} l E.1) f
      (spIntegralTwist S l E) (spIntegralTwist X l E) (spIntegralComparison f l E)) :
    ∃ m : (upperStar Ab.{u + 1} f).obj (quotientLine l E π n S).X ⟶
        (quotientLine l E π n X).X,
      QuotientPullMap l E π n f m ∧
      Nonempty (PullEndpoint
        (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) f
        (quotientLine l E π n S) (quotientLine l E π n X) m) := by
  unfold QuotientPullMap quotientLine
  exact scalar_endpoint (quotientMap l E π n) f e

private theorem unit_endpoint
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} (f : X ⟶ S) :
    Nonempty (UnitPullEndpoint R f) := by
  refine ⟨⟨(Functor.Monoidal.εIso (CondensedRing.upperStar R f)).symm, ?_⟩⟩
  exact CondensedRing.homEquiv_εIso_inv_hom R f

private theorem exchange_restriction_iso
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    {L : A ⥤ B} {U : B ⥤ A} {L' : A' ⥤ B'} {U' : B' ⥤ A'}
    (adj : L ⊣ U) (adj' : L' ⊣ U') {G : A ⥤ A'} {H : B ⥤ B'}
    (theta : G ⋙ L' ≅ L ⋙ H) (M : B)
    [hc : IsIso adj.counit] [hc' : IsIso adj'.counit] :
    IsIso (L'.map ((Adjunction.exchangeRight adj adj' theta).app M)) := by
  have he : L'.map ((Adjunction.exchangeRight adj adj' theta).app M) ≫
      adj'.counit.app (H.obj M) =
      theta.hom.app (U.obj M) ≫ H.map (adj.counit.app M) := by
    have h := (adj'.homEquiv _ _).symm_apply_apply
      (theta.hom.app (U.obj M) ≫ H.map (adj.counit.app M))
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_unit] at h
    rw [Adjunction.exchangeRight_app, ← U'.map_comp]
    exact h
  have : IsIso (L'.map ((Adjunction.exchangeRight adj adj' theta).app M) ≫
      adj'.counit.app (H.obj M)) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (adj'.counit.app _)

private theorem module_disjoint_zero
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {Z U S : Scheme.{u}}
    (i : Z ⟶ S) (j : U ⟶ S) [IsOpenImmersion j]
    (h : Disjoint (Set.range i.base) (Set.range j.base)) (M : Modules R Z) :
    IsZero ((CondensedRing.upperStar R j).obj ((CondensedRing.lowerStar R i).obj M)) :=
  CondensedRing.isZero_of_isZero_X R
    ((ProEtale.isZero_upperStar_lowerStar_of_disjoint Ab.{u + 1} i j h M.X).of_iso
      (CondensedRing.upperStarObjXIso R j _))

private theorem closed_restriction
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {Z S Z' S' : Scheme.{u}}
    (i : Z ⟶ S) (i' : Z' ⟶ S') [IsClosedImmersion i] [IsClosedImmersion i']
    (hZ : Z' ⟶ Z) (hS : S' ⟶ S) (h : i' ≫ hS = hZ ≫ i) (M : Modules R Z) :
    IsIso ((CondensedRing.upperStar R i').map ((ordinaryExchange R i i' hZ hS h).app M)) := by
  let theta := ((CondensedRing.upperStarComp R i' hS).symm ≪≫
    CondensedRing.upperStarCongr R h ≪≫ CondensedRing.upperStarComp R hZ i)
  have he : ordinaryExchange R i i' hZ hS h =
      Adjunction.exchangeRight (CondensedRing.upperStarLowerStarAdjunction R i)
        (CondensedRing.upperStarLowerStarAdjunction R i') theta := rfl
  rw [he]
  exact exchange_restriction_iso
    (CondensedRing.upperStarLowerStarAdjunction R i)
    (CondensedRing.upperStarLowerStarAdjunction R i') theta M
    (hc := CondensedRing.isIso_upperStarLowerStarAdjunction_counit_of_isClosedImmersion R i)
    (hc' := CondensedRing.isIso_upperStarLowerStarAdjunction_counit_of_isClosedImmersion R i')

private theorem closed_exchange_iso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {Z S Z' S' : Scheme.{u}} [IsNoetherian S']
    (i : Z ⟶ S) (i' : Z' ⟶ S') [IsClosedImmersion i] [IsClosedImmersion i']
    (hZ : Z' ⟶ Z) (hS : S' ⟶ S) (h : i' ≫ hS = hZ ≫ i)
    (sq : IsPullback hZ i' i hS) (M : Modules R Z) :
    IsIso ((ordinaryExchange R i i' hZ hS h).app M) := by
  let j := i.openComplement.ι
  let k := pullback.snd j hS
  let p := pullback.fst j hS
  let : TopologicalSpace.NoetherianSpace (pullback j hS : Scheme.{u}) :=
    k.isOpenEmbedding.isInducing.noetherianSpace
  have hc : IsCompl (Set.range i.base) (Set.range j.base) := by
    change IsCompl (Set.range i) (Set.range i.openComplement.ι)
    rw [Scheme.Opens.range_ι, Scheme.Hom.coe_openComplement]
    exact isCompl_compl
  have hk : IsCompl (Set.range i'.base) (Set.range k.base) := by
    change IsCompl (Set.range i') (Set.range (pullback.snd j hS))
    rw [Scheme.range_snd_of_isPullback sq, Scheme.Pullback.range_snd]
    rw [hc.compl_eq.symm, Set.preimage_compl]
    exact isCompl_compl
  have hs : IsZero ((CondensedRing.upperStar R k).obj
      ((CondensedRing.upperStar R hS).obj ((CondensedRing.lowerStar R i).obj M))) := by
    let e := (CondensedRing.upperStarComp R k hS).symm ≪≫
      CondensedRing.upperStarCongr R (pullback.condition (f := j) (g := hS)).symm ≪≫
      CondensedRing.upperStarComp R p j
    exact ((CondensedRing.upperStar R p).map_isZero
      (module_disjoint_zero R i j hc.disjoint M)).of_iso (e.app _)
  have ht : IsZero ((CondensedRing.upperStar R k).obj
      ((CondensedRing.lowerStar R i').obj ((CondensedRing.upperStar R hZ).obj M))) :=
    module_disjoint_zero R i' k hk.disjoint _
  have detect := CondensedRing.jointlyReflectIsomorphisms_upperStar_of_isCompl R i' k hk
  apply detect.isIso_of_pairFunctor _ (hs.isIso ht _) ?_
  exact closed_restriction R i i' hZ hS h M

private theorem diagonal_pullback {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (s : BaseSquares g) :
    IsPullback (baseP g) (diagonalImmersion Y') (diagonalImmersion Y) (baseW g) := by
  let q := (ProjectiveLine Y ↘ Y)
  let q' := (ProjectiveLine Y' ↘ Y')
  have hd₁ : diagonalImmersion Y ≫ pullback.fst q q = 𝟙 _ := pullback.diagonal_fst q
  have hd₂ : diagonalImmersion Y ≫ pullback.snd q q = 𝟙 _ := pullback.diagonal_snd q
  have hd₁' : diagonalImmersion Y' ≫ pullback.fst q' q' = 𝟙 _ :=
    pullback.diagonal_fst q'
  have hd₂' : diagonalImmersion Y' ≫ pullback.snd q' q' = 𝟙 _ :=
    pullback.diagonal_snd q'
  have hs₁ : pullback.fst q' q' ≫ baseP g = baseW g ≫ pullback.fst q q := s.first_square
  have hs₂ : pullback.snd q' q' ≫ baseP g = baseW g ≫ pullback.snd q q := s.second_square
  have hdiag : diagonalImmersion Y' ≫ baseW g = baseP g ≫ diagonalImmersion Y :=
    s.diagonal_square
  refine IsPullback.of_isLimit' ⟨hdiag.symm⟩
    (PullbackCone.IsLimit.mk _
      (fun c ↦ c.snd ≫ pullback.fst q' q') ?_ ?_ ?_)
  · intro c
    have h := congrArg (fun t ↦ t ≫ pullback.fst q q) c.condition
    simpa only [Category.assoc, hd₁, Category.comp_id, ← hs₁] using h.symm
  · intro c
    have he : c.snd ≫ pullback.fst q' q' = c.snd ≫ pullback.snd q' q' := by
      apply (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g).hom_ext
      · have h := congrArg (fun t ↦ t ≫ pullback.fst q q) c.condition
        have h' := congrArg (fun t ↦ t ≫ pullback.snd q q) c.condition
        simp only [Category.assoc, hd₁, hd₂, Category.comp_id, ← hs₁, ← hs₂] at h h'
        exact h.symm.trans h'
      · simpa only [Category.assoc] using congrArg (fun t ↦ c.snd ≫ t)
          (pullback.condition (f := q') (g := q'))
    apply pullback.hom_ext (f := q') (g := q')
    · simp only [Category.assoc, hd₁', Category.comp_id]
    · simpa only [Category.assoc, hd₂', Category.comp_id] using he
  · intro c m _ hm
    have h := congrArg (fun t ↦ t ≫ pullback.fst q' q') hm
    simpa only [Category.assoc, hd₁', Category.comp_id] using h

private theorem source_map_closed_iso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsNoetherian (diagonalSurface Y')] (geo : BaseSquares g)
    (cP : UnitPullEndpoint R (baseP g)) :
    IsIso (sourcePullbackMap R g geo.diagonal_square cP) := by
  unfold sourcePullbackMap
  apply IsIso.comp_isIso'
  · apply closed_exchange_iso
    exact diagonal_pullback g geo
  · infer_instance

private theorem assemble_source
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsNoetherian (diagonalSurface Y')]
    (L : ∀ X : Scheme.{u}, Modules R X)
    (mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
      (L (ProjectiveLine Y')).X)
    (mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
      (L (diagonalSurface Y')).X)
    (geo : BaseSquares g) (ends : PullbackEndpoints R g L mP mW) :
    Nonempty (SourcePullback R g L mP mW) := by
  have : IsIso (sourcePullbackMap R g geo.diagonal_square ends.cP) :=
    source_map_closed_iso R g geo ends.cP
  exact ⟨{
    geometry := geo
    endpoints := ends
    supported := asIso (sourcePullbackMap R g geo.diagonal_square ends.cP)
    supported_normalization := asIso_hom _ }⟩

private theorem source_from_endpoints
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsNoetherian Y'] (L : ∀ X : Scheme.{u}, Modules R X)
    (mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
      (L (ProjectiveLine Y')).X)
    (mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
      (L (diagonalSurface Y')).X)
    (geo : BaseSquares g) (ends : PullbackEndpoints R g L mP mW) :
    Nonempty (SourcePullback R g L mP mW) := by
  have : IsProper (ProjectiveLine Y' ↘ Y') :=
    ProjectiveSpace.instIsProper (ULift.{u} (Fin 2)) Y'
  let : IsNoetherian (ProjectiveLine Y') :=
    isNoetherian_of_locallyOfFiniteType (ProjectiveLine Y' ↘ Y')
  let : IsNoetherian (diagonalSurface Y') :=
    isNoetherian_of_locallyOfFiniteType
      (pullback.fst (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
  exact assemble_source R g L mP mW geo ends

private theorem combine_endpoints
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsNoetherian Y] [IsNoetherian Y'] (L : ∀ X : Scheme.{u}, Modules R X)
    (P : ((upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
      (L (ProjectiveLine Y')).X) → Prop)
    (Q : ((upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
      (L (diagonalSurface Y')).X) → Prop)
    (geo : BaseSquares g)
    (hp : ∃ m, P m ∧ Nonempty (PullEndpoint R (baseP g)
      (L (ProjectiveLine Y)) (L (ProjectiveLine Y')) m))
    (hw : ∃ m, Q m ∧ Nonempty (PullEndpoint R (baseW g)
      (L (diagonalSurface Y)) (L (diagonalSurface Y')) m)) :
    ∃ mP mW, P mP ∧ Q mW ∧ Nonempty (SourcePullback R g L mP mW) := by
  obtain ⟨mP, hP, ⟨eP⟩⟩ := hp
  obtain ⟨mW, hW, ⟨eW⟩⟩ := hw
  obtain ⟨cY⟩ := unit_endpoint R g
  obtain ⟨cP⟩ := unit_endpoint R (baseP g)
  exact ⟨mP, mW, hP, hW, source_from_endpoints R g L mP mW geo ⟨cY, cP, eP, eW⟩⟩

/-- Extension of the integral source and line comparisons to an ordinary quotient.
No class, trace, right derived model, or scalar compatibility is used here.

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3), coefficient functors
commuting with pullback; original quotient-base-change proof, step 1.
(blueprint: lem-diagonal-quotient-source-pullback).

Proof: Write a for the condensed quotient coefficient map. The coefficient square
for inverse image commutes by naturality of condensedPullbackHom. The ordinary
scalar/pullback compositor, obtained by conjugating comapLowerStarIso, therefore
identifies pullback of extension of scalars with extension of module pullback.
Extend the two integral line isomorphisms through this compositor. Transposing
their module maps through the ordinary geometric adjunction gives mP and mW.
On the defining coequalizers of extension of scalars, the compositor sends a
coefficient tensor a root to the pulled-back coefficient tensor the integral
root comparison. Naturality of extendUnit and the normalization of the two
integral PullEndpoints give precisely the two QuotientPullMap equations.
The coefficient-unit comparisons are the regular-module pullbacks. The diagonal
square is cartesian by projective-space base change. Closed
restriction of the ordinary exchange is invertible by the mate-counit identity,
and both open restrictions vanish by disjointness. Joint open/closed detection
therefore makes the exchange invertible. Unfold sourcePullbackMap and infer its
two component isomorphisms from their actual types. Take asIso of that map as
supported, and retain the three original geometric square equations.
All constructions are ordinary tensor constructions, so no flatness or regularity
of the quotient is required, including pi = 0 or a unit. -/
theorem diagonalQuotient_sourcePullback
    (l : ℕ) [Fact l.Prime] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsNoetherian Y] [IsNoetherian Y']
    (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (n : ℕ)
    (s : SourcePullback (Profinite.padicIntegersRingObj.{u} l E.1) g
      (fun X ↦ spIntegralTwist X l E)
      (spIntegralComparison (baseP g) l E) (spIntegralComparison (baseW g) l E)) :
    ∃ (mP : (upperStar Ab.{u + 1} (baseP g)).obj
        (quotientLine l E π n (ProjectiveLine Y)).X ⟶
          (quotientLine l E π n (ProjectiveLine Y')).X)
      (mW : (upperStar Ab.{u + 1} (baseW g)).obj
        (quotientLine l E π n (diagonalSurface Y)).X ⟶
          (quotientLine l E π n (diagonalSurface Y')).X),
      QuotientPullMap l E π n (baseP g) mP ∧
      QuotientPullMap l E π n (baseW g) mW ∧
      Nonempty (SourcePullback
        (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) g
        (quotientLine l E π n) mP mW) := by
  exact combine_endpoints
    (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) g
    (quotientLine l E π n) (QuotientPullMap l E π n (baseP g))
    (QuotientPullMap l E π n (baseW g)) s.geometry
    (quotient_endpoint l E π n (baseP g) s.endpoints.lineP)
    (quotient_endpoint l E π n (baseW g) s.endpoints.lineW)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
