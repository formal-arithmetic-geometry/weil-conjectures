/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap
public import Sheaf.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.CoherentEtaleRawDirectImageComparison
import all Sheaf.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
import WeilConjectures.AlgebraicGeometry.Modules.Ext
import Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChange
import Sheaf.AlgebraicGeometry.ProperFlatSingleDerivedDirectImagePerfect
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex
import Sheaf.AlgebraicGeometry.FiniteFreeBottomDifferentialZero
import Sheaf.AlgebraicGeometry.Curve.CanonicalAdditiveCohomologyComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.AlgebraicGeometry.ProperFlatGlobalSections
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel

/-! # Structure-sheaf direct images for smooth proper curves

Source: Stacks Project, curves.tex, Tag 0GKA, (a),(b), and etale-cohomology.tex,
Tag 03P2 (blueprint: lem-weil-pbc-smooth-curve-etale-structure-direct-images).

Linearity is expressed on the canonical local cohomology classes generating the
higher direct image. This specifies the natural scalar action without replacing
it by a freely chosen module structure on an additive sheaf.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

set_option autoImplicit false

/-- Localized structure coefficients over an etale base object.
Source: Stacks Project, Tags 03P2 and 03Q8
(blueprint: lem-weil-pbc-smooth-curve-etale-structure-direct-images). -/
noncomputable abbrev curveLocalStructure {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Etale) :=
  (upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).obj X.etaleAdditiveSheaf

/-- Localization identifies a coefficient section with a lifted function.
Source: Stacks Project, Tags 03P2 and 03Q8
(blueprint: lem-weil-pbc-smooth-curve-etale-structure-direct-images). -/
noncomputable def curveLocalFunction {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Etale)
    (T : (pullback U.hom f).Etale)
    (x : (curveLocalStructure f U).obj.obj (op T)) : ULift.{u + 1} Γ(T.left, ⊤) :=
  (((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
    (pullback.snd U.hom f) inferInstance).hom.app X.etaleAdditiveSheaf).hom.app (op T)) x

/-- The normalization characterizing multiplication by a base function on local coefficients.
All etale test objects and all sections occur, so the endomorphism is determined uniquely.
Source: Stacks Project, Tags 03P2 and 03Q8
(blueprint: lem-weil-pbc-smooth-curve-etale-structure-direct-images). -/
def IsCurveLocalScalar {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Etale)
    (a : Γ(U.left, ⊤)) (μ : curveLocalStructure f U ⟶ curveLocalStructure f U) : Prop :=
  ∀ (T : (pullback U.hom f).Etale) (x : (curveLocalStructure f U).obj.obj (op T)),
    curveLocalFunction f U T (μ.hom.app (op T) x) =
      ULift.up (@id Γ(T.left, ⊤) ((T.hom ≫ pullback.fst U.hom f).appTop a) *
        (curveLocalFunction f U T x).down)

/-- Action of the specified local coefficient endomorphism on restricted abelian cohomology.
Source: Stacks Project, Tags 03P2 and 03Q8
(blueprint: lem-weil-pbc-smooth-curve-etale-structure-direct-images). -/
noncomputable def curveLocalCohomologyMap {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Etale)
    (μ : curveLocalStructure f U ⟶ curveLocalStructure f U) :
    rawAffineRestrictedCohomology f 1 X.etaleAdditiveSheaf U ⟶
      rawAffineRestrictedCohomology f 1 X.etaleAdditiveSheaf U :=
  (cohomology AddCommGrpCat.{u + 1} (pullback U.hom f) 1).map
    (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map μ))

private theorem exists_curveLocalScalar {X S : Scheme.{u}} (f : X ⟶ S)
    (U : S.Etale) (a : Γ(U.left, ⊤)) :
    ∃ μ : curveLocalStructure f U ⟶ curveLocalStructure f U,
      IsCurveLocalScalar f U a μ := by
  let e : curveLocalStructure f U ≅ (pullback U.hom f).etaleAdditiveSheaf :=
    (upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
      (pullback.snd U.hom f) inferInstance).app X.etaleAdditiveSheaf
  let r := (pullback.fst U.hom f).appTop a
  let m := Scheme.Modules.etaleAdditiveSmul (pullback U.hom f) r
  refine ⟨e.hom ≫ m ≫ e.inv, ?_⟩
  intro T x
  have he : (e.hom ≫ m ≫ e.inv) ≫ e.hom = e.hom ≫ m := by simp
  have hx := congrArg (fun k ↦ k.hom.app (op T) x) he
  change curveLocalFunction f U T
      ((e.hom ≫ m ≫ e.inv).hom.app (op T) x) = _
  change e.hom.hom.app (op T) ((e.hom ≫ m ≫ e.inv).hom.app (op T) x) = _
  change e.hom.hom.app (op T) ((e.hom ≫ m ≫ e.inv).hom.app (op T) x) =
    m.hom.app (op T) (e.hom.hom.app (op T) x) at hx
  rw [hx]
  apply ULift.ext
  change (@id Γ(T.left, ⊤) (e.hom.hom.app (op T) x).down) * (@id Γ(T.left, ⊤) (T.hom.appTop r)) =
    (@id Γ(T.left, ⊤) ((T.hom ≫ pullback.fst U.hom f).appTop a)) *
      (@id Γ(T.left, ⊤) (e.hom.hom.app (op T) x).down)
  rw [Scheme.Hom.comp_appTop]
  exact mul_comm _ _

private theorem isIso_appTop_of_structure_unit {X S : Scheme.{u}} (f : X ⟶ S)
    (h : IsIso ((Classical.choose
      (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app
        (SheafOfModules.unit S.ringCatSheaf))) : IsIso f.appTop := by
  let := h
  obtain ⟨hb, he⟩ := Scheme.Modules.tensorPullbackObjUnitToUnit_isIso f
  let := hb
  have hq : IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
    rw [← he]
    infer_instance
  let := hq
  let F := SheafOfModules.toSheaf S.ringCatSheaf ⋙
    sheafToPresheaf _ AddCommGrpCat.{u} ⋙ (evaluation _ _).obj (op ⊤)
  have : IsIso (F.map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) := inferInstance
  apply (ConcreteCategory.isIso_iff_bijective f.appTop).2
  exact ConcreteCategory.bijective_of_isIso (F.map
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))

private theorem smooth_curve_etale_structure_hzero {X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f] :
    IsIso (Scheme.etaleAdditiveSheafToLowerStar f) := by
  have : IsIso ((sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      (Scheme.etaleAdditiveSheafToLowerStar f)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).2
    let p := pullback.fst U.unop.hom f
    have hp := isIso_structureSheafMap_of_proper_flat_geometricallyReduced_connected_fibers
      p (fun s ↦ inferInstance) (fun s ↦ inferInstance)
    have hs : IsIso p.appTop := isIso_appTop_of_structure_unit _ hp.1
    let := hs
    have hb := ConcreteCategory.bijective_of_isIso p.appTop
    change Function.Bijective (fun x : ULift.{u + 1} Γ(U.unop.left, ⊤) ↦
      ULift.up (p.appTop x.down))
    exact (ULift.up_bijective).comp (hb.comp ULift.down_bijective)
  exact isIso_of_reflects_iso _
    (sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})

private theorem perfect_curve_homology_one_locally_free
    (S : Scheme.{u})
    [HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    [∀ s : S, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace))]
    (P : schemeDerivedCategory S) (hP : S.IsPerfect P)
    (hzero : ∀ (s : S) (i : ℤ), i < 0 ∨ 1 < i →
      Scheme.derivedFiberBetti S P i s = 0)
    (hone : ∀ s : S, Scheme.derivedFiberBetti S P 0 s = 1)
    (hH : ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj P).IsFiniteLocallyFreeOfRank 1) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1).obj P).IsFiniteLocallyFree := by
  classical
  let : ∀ V : S.Opens, HasWeakSheafify
      ((Opens.grothendieckTopology S.carrier).over V)
        AddCommGrpCat.{u} := inferInstance
  let : ∀ V : S.Opens,
      ((Opens.grothendieckTopology S.carrier).over V).WEqualsLocallyBijective
        AddCommGrpCat.{u} := inferInstance
  have hlocal (s : S) : ∃ U : S.Opens, s ∈ U ∧ ∃ r : ℕ,
      Nonempty (((Scheme.Modules.restrictFunctor U.ι).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1).obj P)) ≅
          SheafOfModules.free (ULift.{u} (Fin r))) := by
    obtain ⟨_, _, U, hs, _, K, _, hrank, ⟨e⟩⟩ :=
      Scheme.exists_finiteFreeResidueModel S P hP s
    let : ∀ V : U.toScheme.Opens, HasWeakSheafify
        ((Opens.grothendieckTopology U.toScheme.carrier).over V)
          AddCommGrpCat.{u} := inferInstance
    let : ∀ V : U.toScheme.Opens,
        ((Opens.grothendieckTopology U.toScheme.carrier).over
          V).WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
    have hz (i : ℤ) (hi : i < 0 ∨ 1 < i) : IsZero (K.X i) := by
      obtain ⟨ei⟩ := hrank i
      rw [hzero s i hi] at ei
      have hf : IsZero (SheafOfModules.free
          (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin 0))) := by
        apply (IsZero.iff_id_eq_zero _).2
        apply (SheafOfModules.freeHomEquiv _).injective
        funext j
        exact Fin.elim0 j.down
      exact hf.of_iso ei
    let F : SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U) ⥤
        U.toScheme.Modules := (Scheme.Modules.overEquiv (X := S) U).functor
    have : F.Additive := Functor.additive_of_preserves_binary_products F
    let O := SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U
    let L : CochainComplex U.toScheme.Modules ℤ := (F.mapHomologicalComplex (.up ℤ)).obj K
    let cmp (i : ℤ) : (Scheme.Modules.restrictFunctor U.ι).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) i).obj P) ≅ L.homology i :=
      (Scheme.Modules.overFunctorEquiv U).symm.app _ ≪≫
        F.mapIso ((O.mapDerivedCategoryHomologyFunctorIso i).app P ≪≫
          (DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
          (DerivedCategory.homologyFunctorFactors _ i).app K) ≪≫
        ((F.mapHomologicalComplexHomologyIso (.up ℤ) i).app K).symm
    let ef (i : ℤ) : L.X i ≅ SheafOfModules.free
        (R := U.toScheme.ringCatSheaf)
          (ULift.{u} (Fin (Scheme.derivedFiberBetti S P i s))) :=
      F.mapIso (hrank i).some ≪≫
        (SheafOfModules.mapFreeIso F _
          (Scheme.Modules.overEquivFunctorObjUnitIso U)).symm
    have hneg (i : ℤ) (hi : i < 0) : IsZero (L.X i) := F.map_isZero (hz i (Or.inl hi))
    have : ((Scheme.Modules.restrictFunctor U.ι).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj P)).IsFiniteLocallyFreeOfRank
            1 := by
      let := hH
      infer_instance
    have hL : (L.homology 0).IsFiniteLocallyFreeOfRank 1 :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (cmp 0)
    have hd : L.d 0 1 = 0 := Scheme.finiteFreeBottom_differential_zero U.toScheme L 0 1 hneg
      (by simpa only [hone s] using Nonempty.intro (ef 0))
      ⟨Scheme.derivedFiberBetti S P 1 s, ⟨ef 1⟩⟩ hL
    have hg : (L.sc' 0 1 2).g = 0 := (F.map_isZero (hz 2 (by omega))).eq_of_tgt _ _
    let eh : L.homology 1 ≅ L.X 1 :=
      L.homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫
        (ShortComplex.HomologyData.ofZeros (L.sc' 0 1 2) hd hg).left.homologyIso
    exact ⟨U, hs, Scheme.derivedFiberBetti S P 1 s, ⟨cmp 1 ≪≫ eh ≪≫ ef 1⟩⟩
  choose U hs r he using hlocal
  apply Scheme.Modules.isFiniteLocallyFree_of_restrict_iso_free _ (fun s ↦ (U s).ι)
    (κ := fun s ↦ ULift.{u} (Fin (r s)))
  · simpa only [Scheme.Opens.opensRange_ι] using
      (eq_top_iff.mpr fun s _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨s, hs s⟩ :
        (⨆ s, U s) = ⊤)
  · exact he

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  derivedPullback

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem smooth_curve_structure_first_locally_free
    {X S : Scheme.{u}} [CompactSpace S] [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1) :
    ((Scheme.Modules.higherDirectImage f 1).obj
      (SheafOfModules.unit X.ringCatSheaf)).IsFiniteLocallyFree := by
  classical
  let : ∀ Y : Scheme.{u}, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    fun Y ↦ HasDerivedCategory.standard _
  let : ∀ (Y : Scheme.{u}) (U : Y.Opens), HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U)) :=
    fun Y U ↦ HasDerivedCategory.standard _
  let : ∀ U : S.Opens, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) :=
    fun U ↦ HasDerivedCategory.standard _
  let : ∀ Y : Scheme.{u}, HasDerivedCategory.{u + 1} Y.Modules :=
    fun Y ↦ HasDerivedCategory.standard _
  let : ∀ Y : Scheme.{u}, Abelian.HasKInjectiveResolutions Y.Modules :=
    fun Y ↦ by
      let : IsGrothendieckAbelian.{u} Y.Modules := Scheme.Modules.isGrothendieckAbelian Y
      infer_instance
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have : SheafOfModules.IsInvertible.{u, u, u} OX := by
    dsimp only [OX]
    infer_instance
  have : OX.IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  let K : schemeDerivedCategory S := (schemeDerivedDirectImage f).obj
    ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj OX)
  have hflat : Scheme.Modules.IsFlatOver OX f := Scheme.Modules.isFlatOver_of_isInvertible f OX
  have hK : S.IsPerfect K := properFlat_single_derivedDirectImage_perfect f OX hflat
  let fibreIso (s : S) : (derivedPullback (S.fromSpecResidueField s)).obj K ≅
      (schemeDerivedDirectImage (f.fiberToSpecResidueField s)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (f.fiber s).toRingedSpace)) 0).obj
            (SheafOfModules.unit (f.fiber s).ringCatSheaf)) := by
    let e := (nonempty_derivedBaseChange_iso_of_isFlatOver f OX hflat
      (S.fromSpecResidueField s)).some
    obtain ⟨h, _⟩ := Scheme.Modules.tensorPullbackObjUnitToUnit_isIso (f.fiberι s)
    let := h
    exact e ≪≫ (schemeDerivedDirectImage (f.fiberToSpecResidueField s)).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso
        (asIso (Scheme.Modules.tensorPullbackObjUnitToUnit (f.fiberι s))))
  have unitIso {Y T : Scheme.{u}} (g : Y ⟶ T)
      [IsProper g] [Smooth g] [GeometricallyConnected g] :
      Nonempty ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
        SheafOfModules.unit T.ringCatSheaf) := by
    obtain ⟨hu, _⟩ :=
      isIso_structureSheafMap_of_proper_flat_geometricallyReduced_connected_fibers
        g (fun s ↦ inferInstance) (fun s ↦ inferInstance)
    let := hu
    obtain ⟨ht, he⟩ := Scheme.Modules.tensorPullbackObjUnitToUnit_isIso g
    let := ht
    have hq : IsIso (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) := by
      rw [← he]
      infer_instance
    exact ⟨(asIso (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)).symm⟩
  let zeroIso {Y T : Scheme.{u}} (g : Y ⟶ T)
      [IsProper g] [Smooth g] [GeometricallyConnected g] :
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).obj
          ((schemeDerivedDirectImage g).obj ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              (SheafOfModules.unit Y.ringCatSheaf))) ≅
        SheafOfModules.unit T.ringCatSheaf :=
    (Scheme.Modules.pushforward g).homologyRightDerivedFunctorObjSingleFunctorIso
      (SheafOfModules.unit Y.ringCatSheaf) 0 ≪≫
      (Scheme.Modules.pushforward g).rightDerivedZeroIsoSelf.app _ ≪≫ (unitIso g).some
  have hH : ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj K).IsFiniteLocallyFreeOfRank 1 := by
    have : (SheafOfModules.unit S.ringCatSheaf).IsFiniteLocallyFreeOfRank 1 :=
      (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one.{u, u, u}
        (SheafOfModules.unit S.ringCatSheaf)).mp inferInstance
    exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (zeroIso f).symm
  let sectionsEquiv (s : S) (M : (Spec (S.residueField s)).Modules) :
      ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (S.residueField s)).inv.hom).obj
        ((SheafOfModules.evaluation
          (moduleRings (Spec (S.residueField s)).toRingedSpace) (op ⊤)).obj M)) ≃ₗ[
          S.residueField s] ((moduleSpecΓFunctor (R := S.residueField s)).obj M) :=
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro a x
        change ((Scheme.ΓSpecIso (S.residueField s)).inv a) •
            (x : M.val.obj (op ⊤)) =
          ((moduleRings (Spec (S.residueField s)).toRingedSpace).obj.map
            ((initialOpOfTerminal isTerminalTop).to (op ⊤)))
              ((Scheme.ΓSpecIso (S.residueField s)).inv a) • (x : M.val.obj (op ⊤))
        rw [show (initialOpOfTerminal isTerminalTop).to
          (op (⊤ : (Spec (S.residueField s)).Opens)) = 𝟙 _ from Subsingleton.elim _ _,
          CategoryTheory.Functor.map_id]
        rfl }
  have hone (s : S) : Scheme.derivedFiberBetti S K 0 s = 1 := by
    have : IsProper (f.fiberToSpecResidueField s) := by
      change IsProper (pullback.snd f _)
      infer_instance
    have : Smooth (f.fiberToSpecResidueField s) := by
      change Smooth (pullback.snd f _)
      infer_instance
    have : GeometricallyConnected (f.fiberToSpecResidueField s) := by
      change GeometricallyConnected (pullback.snd f _)
      infer_instance
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0
    let e := H.mapIso (fibreIso s) ≪≫ zeroIso (f.fiberToSpecResidueField s) ≪≫
      (SheafOfModules.freeUniqueIso (R := (Spec (S.residueField s)).ringCatSheaf)
        (ULift.{u} (Fin 1))).symm
    exact (sectionsEquiv s (H.obj
      ((derivedPullback (S.fromSpecResidueField s)).obj K))).finrank_eq.trans (by
        simpa only [Fintype.card_ulift, Fintype.card_fin] using
          (Scheme.Modules.finrank_moduleSpecΓFunctor_obj_free
            (Field.toIsField (S.residueField s)) e).1)
  have hzero (s : S) (i : ℤ) (hi : i < 0 ∨ 1 < i) :
      Scheme.derivedFiberBetti S K i s = 0 := by
    rcases hi with hi | hi
    · let g := f.fiberToSpecResidueField s
      let M : (f.fiber s).Modules := SheafOfModules.unit (f.fiber s).ringCatSheaf
      have hge := (Scheme.Modules.pushforward g).isGE_rightDerivedFunctor_obj_singleFunctor M
      have hzi := (DerivedCategory.isGE_iff _ 0).mp hge i hi
      have hz := hzi.of_iso
        ((DerivedCategory.homologyFunctor _ i).mapIso (fibreIso s))
      have hzv :=
        (ModuleCat.restrictScalars (Scheme.ΓSpecIso (S.residueField s)).inv.hom).map_isZero
        ((SheafOfModules.evaluation _ (op ⊤)).map_isZero hz)
      have : Subsingleton (Scheme.derivedFiberCohomology S K i s) :=
        ModuleCat.subsingleton_of_isZero hzv
      exact Module.finrank_zero_of_subsingleton
    · let q := i.toNat
      have hq : (q : ℤ) = i := Int.toNat_of_nonneg (by omega)
      let G := Scheme.Modules.pushforward (f.fiberToSpecResidueField s)
      let M : (f.fiber s).Modules := SheafOfModules.unit (f.fiber s).ringCatSheaf
      have : LocallyOfFiniteType (f.fiberToSpecResidueField s) := by
        change LocallyOfFiniteType (pullback.snd f _)
        infer_instance
      have : QuasiCompact (f.fiberToSpecResidueField s) := by
        change QuasiCompact (pullback.snd f _)
        infer_instance
      have : IsLocallyNoetherian (f.fiber s) :=
        LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
      have : CompactSpace (f.fiber s) :=
        QuasiCompact.compactSpace_of_compactSpace (f.fiberToSpecResidueField s)
      have : IsNoetherian (f.fiber s) := ⟨⟩
      let e : (DerivedCategory.homologyFunctor _ i).obj
          ((derivedPullback (S.fromSpecResidueField s)).obj K) ≅
          (G.rightDerived q).obj M := by
        rw [← hq]
        exact (DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso (fibreIso s) ≪≫
          G.homologyRightDerivedFunctorObjSingleFunctorIso M q
      obtain ⟨c, _⟩ := Scheme.Modules.exists_addEquiv_sections_higherDirectImage_H_of_field
        (f.fiberToSpecResidueField s) q
      have hdimq : topologicalKrullDim (f.fiber s) < q := by
        rw [hdim s]
        exact_mod_cast (show 1 < q by omega)
      have : Subsingleton (M.H q) :=
        Scheme.Modules.subsingleton_H_of_topologicalKrullDim_lt M hdimq
      have hs : Subsingleton Γ((Scheme.Modules.higherDirectImage
          (f.fiberToSpecResidueField s) q).obj M, ⊤) := (c M).injective.subsingleton
      let : Subsingleton ((moduleSpecΓFunctor (R := S.residueField s)).obj
          ((G.rightDerived q).obj M)) := by
        change Subsingleton Γ((G.rightDerived q).obj M, ⊤)
        exact hs
      have hv : Subsingleton (Scheme.derivedFiberCohomology S K i s) :=
        Function.Injective.subsingleton
          (((moduleSpecΓFunctor (R := S.residueField s)).mapIso e).toLinearEquiv).injective
      let := hv
      exact Module.finrank_zero_of_subsingleton
  have hf := perfect_curve_homology_one_locally_free S K hK hzero hone hH
  let := hf
  exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u, u, u}
    (M := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1).obj K)
    ((Scheme.Modules.pushforward f).homologyRightDerivedFunctorObjSingleFunctorIso OX 1)

attribute [local irreducible] abelianHigherDirectImageClass canonicalComparison
  Scheme.Modules.higherDirectImage

private theorem sheafified_raw_iso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (A B : Sheaf J AddCommGrpCat.{u + 1})
    (c : (presheafToSheaf J AddCommGrpCat.{u + 1}).obj P ≅ A)
    (b : P ⟶ B.obj) [Presheaf.IsLocallyInjective J b]
    [Presheaf.IsLocallySurjective J b] :
    ∃ e : A ≅ B, toSheafify J P ≫ c.hom.hom ≫ e.hom.hom = b := by
  let l : (presheafToSheaf J AddCommGrpCat.{u + 1}).obj P ⟶ B :=
    ⟨sheafifyLift J b B.property⟩
  have hl : toSheafify J P ≫ l.hom = b := toSheafify_sheafifyLift _ _ _
  have : IsIso l := by
    apply (Sheaf.isLocallyBijective_iff_isIso l).mp
    constructor
    · have : Presheaf.IsLocallyInjective J (toSheafify J P ≫ l.hom) := by
        rw [hl]
        infer_instance
      exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
        J (toSheafify J P) l.hom
    · have : Presheaf.IsLocallySurjective J (toSheafify J P ≫ l.hom) := by
        rw [hl]
        infer_instance
      exact Presheaf.isLocallySurjective_of_isLocallySurjective J (toSheafify J P) l.hom
  refine ⟨c.symm ≪≫ asIso l, ?_⟩
  have he : c.hom ≫ (c.symm ≪≫ asIso l).hom = l := by simp
  change toSheafify J P ≫ (c.hom ≫ (c.symm ≪≫ asIso l).hom).hom = b
  rw [he]
  exact hl

/-- The structural direct image is the base structure sheaf, and the first abelian higher
image is the associated sheaf of a finite locally free module, with its natural scalars.
The last two clauses express module-linearity: multiplication is uniquely prescribed on
all localized coefficient sections; its cohomological action commutes with the displayed
isomorphism on canonical local classes. These classes locally generate the higher image.
No module action on the higher image is assumed or chosen arbitrarily.

Source: Stacks Project, curves.tex, Tag 0GKA, (a),(b), smooth specialization;
etale-cohomology.tex, Tag 03P2
(blueprint: lem-weil-pbc-smooth-curve-etale-structure-direct-images).

Proof:
1. Apply proper-flat global sections after every etale base change. The tensor-unit
   comparison identifies the canonical module unit with structural function pullback.
   Its sectionwise ULift is bijective, proving the displayed degree-zero map is an iso.
2. Put K = Rf_* O_X[0]. The proper-flat single-object theorem makes K perfect.
   Relatively-flat derived base change identifies its fibres with the derived direct
   images of the fibre structure sheaves. They have no negative cohomology; their H0
   has dimension one by proper-flat global sections. Noetherian dimension vanishing
   kills cohomology above degree one.
3. At each point take the finite-free residue model of K. Its only possible terms
   have degrees zero and one, and its degree-zero term and H0 both have rank one.
   The finite-free bottom-differential theorem forces its differential to vanish,
   also over a nonreduced base. Its H1 is therefore its finite-free degree-one term.
   Exact restriction and the homology comparisons give finite local freeness of the
   concretely constructed E = R^1 f_* O_X. This module is also quasi-coherent.
4. The raw coherent direct-image comparison supplies a locally bijective map b from
   raw classes to E_et, with the prescribed scalar formula. Sheafify b and use the
   canonical abelian higher-image comparison, normalized on its class map, to obtain
   e. The sheafification identity gives e(class(z)) = b(z).
5. Conjugate explicit multiplication on the localized additive structure sheaf by
   the localization isomorphism. Structural pullback and commutativity give its
   required value on every test-object section. The scalar formula for b and the
   class identity from Step 4 give the final assertion. Empty bases and variable
   or zero ranks use the same argument. -/
theorem smooth_curve_etale_structure_direct_images {X S : Scheme.{u}}
    [CompactSpace S] [IsLocallyNoetherian S] (f : X ⟶ S)
    [IsProper f] [Smooth f] [GeometricallyConnected f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1) :
    IsIso (Scheme.etaleAdditiveSheafToLowerStar f) ∧
      ∃ (E : S.Modules) (_ : E.IsFiniteLocallyFree) (_ : E.IsQuasicoherent)
        (e : (DerivedCategory.Plus.homologyFunctor
          (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) 1).obj
            ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj X.etaleAdditiveSheaf)) ≅
          Scheme.Modules.liftedCoherentEtaleSheaf E),
        ∀ (U : S.Etale) (a : Γ(U.left, ⊤)),
          ∃ μ : curveLocalStructure f U ⟶ curveLocalStructure f U,
            IsCurveLocalScalar f U a μ ∧
            ∀ (z z' : (abelianHigherDirectImageRawPresheaf f 1
                X.etaleAdditiveSheaf).obj (op U)),
              rawRestrictedCohomologyComparison f 1 X.etaleAdditiveSheaf U z' =
                curveLocalCohomologyMap f U μ
                  (rawRestrictedCohomologyComparison f 1 X.etaleAdditiveSheaf U z) →
              e.hom.hom.app (op U)
                  (abelianHigherDirectImageClass f 1 X.etaleAdditiveSheaf U z') =
                ULift.up (a • @id Γ((Scheme.Modules.tensorPullback U.hom).obj E, ⊤)
                  (e.hom.hom.app (op U)
                    (abelianHigherDirectImageClass f 1 X.etaleAdditiveSheaf U z)).down) := by
  refine ⟨smooth_curve_etale_structure_hzero f, ?_⟩
  let E : S.Modules := (Scheme.Modules.higherDirectImage f 1).obj
    (SheafOfModules.unit X.ringCatSheaf)
  have hfree : E.IsFiniteLocallyFree := smooth_curve_structure_first_locally_free f hdim
  have hqc : E.IsQuasicoherent := Scheme.Modules.isQuasicoherent_higherDirectImage f
    (SheafOfModules.unit X.ringCatSheaf) 1
  let := hqc
  obtain ⟨b, hinj, hsurj, hscalar⟩ := exists_coherent_etale_raw_direct_image_comparison f 1
  let := hinj
  let := hsurj
  let c := canonicalComparison f 1 X.etaleAdditiveSheaf
  obtain ⟨e, he⟩ := sheafified_raw_iso S.smallEtaleTopology
    (abelianHigherDirectImageRawPresheaf f 1 X.etaleAdditiveSheaf) _
    (Scheme.Modules.liftedCoherentEtaleSheaf E) c b
  refine ⟨E, hfree, hqc, e, ?_⟩
  intro U a
  obtain ⟨μ, hμ⟩ := exists_curveLocalScalar f U a
  refine ⟨μ, hμ, ?_⟩
  intro z z' hz
  have hc (t : (abelianHigherDirectImageRawPresheaf f 1
      X.etaleAdditiveSheaf).obj (op U)) :
      e.hom.hom.app (op U) (abelianHigherDirectImageClass f 1 X.etaleAdditiveSheaf U t) =
        b.app (op U) t := by
    have h := congrArg (fun k ↦ k.app (op U) t) he
    exact (congrArg (e.hom.hom.app (op U))
      (canonicalComparison_class f 1 X.etaleAdditiveSheaf U t)).symm.trans h
  apply (hc z').trans
  apply (hscalar U a μ hμ z z' hz).trans
  exact congrArg (fun t : ULift.{u + 1}
    Γ((Scheme.Modules.tensorPullback U.hom).obj E, ⊤) ↦ ULift.up (a • t.down))
    (hc z).symm

end AlgebraicGeometry.Etale
