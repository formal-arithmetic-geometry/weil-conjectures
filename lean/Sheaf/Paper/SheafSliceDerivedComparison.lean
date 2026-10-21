/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.Paper.SheafSliceOrdinaryData
public import Sheaf.CategoryTheory.RingedSheafSliceAdjunction
public import Sheaf.CategoryTheory.RingedPresentationData
public import Sheaf.CategoryTheory.RingedCoefficientCounitPresentations
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.SheafSliceOrdinaryComparison
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Sheaf.SixFunctors.ResolvingDerivedAdjunction
import all Sheaf.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Sheaf.Paper.RingedSliceDerivedComparisons
import all Sheaf.Paper.RingedSliceDerivedMate
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-! # Canonical unbounded derived comparisons on sheaf slices

Source: Stacks Project, Modules on Sites, Tag 04IF; Sites, Tag 04H1;
Cohomology on Sites, Tags 0G7E, 08FI, 07A6 and 07A7
(blueprint: lem-sbc-ringed-topos-sheaf-slice-derived-comparison).

## Main definitions and statement

* `SheafSliceSetLocalization`: the sectionwise normalization of slice localization.
* `RingedSheafSliceOrdinaryComparison`: the canonical ordinary ringed square.
* `HasRingedSheafSliceDerivedComparison`: the derived comparisons and their normalizations.
* `ringedSheafSliceDerivedComparison`: existence for every ringed morphism and target sheaf.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RingedCoefficientCounit

namespace CategoryTheory

/-- The derived part of the canonical sheaf-slice square, on its ordinary output data.
All comparisons use actual exact derived restrictions and the existing normalized derived
adjunction interface. Source: Stacks 04IF, 0G7E, 08FI, 07A6, 07A7 and 09T5
(blueprint: lem-sbc-ringed-topos-sheaf-slice-derived-comparison). -/
def HasRingedSheafSliceDerivedComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {RX : Sheaf J CommRingCat.{u}} {RY : Sheaf K CommRingCat.{u}}
    {f : RingedToposMorphism (localCoefficientRings RX) (localCoefficientRings RY)}
    {A : Sheaf K (Type u)}
    [HasDerivedCategory.{w} (modules RX)] [HasDerivedCategory.{w} (modules RY)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      (elementRing (localCoefficientRings RX) (f.inverse.obj A)))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      (elementRing (localCoefficientRings RY) A))]
    (o : RingedSheafSliceOrdinaryComparison RX RY f A) : Prop :=
  letI := o.targetRestrictionAdditive
  letI := o.sourceRestrictionAdditive
  letI := o.targetRestrictionLimits
  letI := o.sourceRestrictionLimits
  letI := o.targetRestrictionColimits
  letI := o.sourceRestrictionColimits
  ∃ globalDerived : DerivedAdjunction.{w} o.pullback f.modules o.ordinaryAdjunction,
  ∃ sliceDerived : DerivedAdjunction.{w} o.slicePullback o.slice.modules o.sliceOrdinaryAdjunction,
  ∃ theta : (elementModulePullback.{u, u} (localCoefficientRings RY) A).mapDerivedCategory.{w, w} ⋙
      sliceDerived.left ≅
    globalDerived.left ⋙
      (elementModulePullback.{u, u}
        (localCoefficientRings RX) (f.inverse.obj A)).mapDerivedCategory.{w, w},
  ∃ beta : globalDerived.right ⋙
      (elementModulePullback.{u, u} (localCoefficientRings RY) A).mapDerivedCategory ≅
    (elementModulePullback.{u, u}
      (localCoefficientRings RX) (f.inverse.obj A)).mapDerivedCategory.{w, w} ⋙
      sliceDerived.right,
  -- globalFlat_computation
  (∀ T : CochainComplex (modules RY) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := RY) T →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u} (R := RY) (T.X n)) →
      IsIso (globalDerived.epsilon.app T)) ∧
  -- sliceFlat_computation
  (∀ T : CochainComplex (ringedSiteModules.{u, u, u, u}
      (elementRing (localCoefficientRings RY) A)) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := presentationElementRing RY A) T →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u}
      (R := presentationElementRing RY A) (T.X n)) →
      IsIso (sliceDerived.epsilon.app T)) ∧
  -- theta_representative
  (∀ T : CochainComplex (modules RY) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := RY) T →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u} (R := RY) (T.X n)) →
    theta.hom.app (DerivedCategory.Q.{w}.obj T) ≫
      (elementModulePullback.{u, u}
        (localCoefficientRings RX) (f.inverse.obj A)).mapDerivedCategory.{w, w}.map
        (globalDerived.epsilon.app T) ≫
      (elementModulePullback.{u, u}
        (localCoefficientRings RX) (f.inverse.obj A)).mapDerivedCategoryFactors.{w, w}.hom.app
        ((onComplex o.pullback).obj T) =
    sliceDerived.left.map
      ((elementModulePullback.{u, u}
        (localCoefficientRings RY) A).mapDerivedCategoryFactors.{w, w}.hom.app T) ≫
      sliceDerived.epsilon.app
        ((onComplex (elementModulePullback.{u, u} (localCoefficientRings RY) A)).obj T) ≫
      DerivedCategory.Q.{w}.map ((NatIso.mapHomologicalComplex o.sigma (.up ℤ)).hom.app T)) ∧
  -- beta_representative
  (∀ I : CochainComplex (modules RX) ℤ, I.IsKInjective →
    (elementModulePullback.{u, u} (localCoefficientRings RY) A).mapDerivedCategory.{w, w}.map
        (globalDerived.eta.app I) ≫
      beta.hom.app (DerivedCategory.Q.{w}.obj I) ≫
      sliceDerived.right.map ((elementModulePullback.{u, u}
        (localCoefficientRings RX) (f.inverse.obj A)).mapDerivedCategoryFactors.{w, w}.hom.app I) =
    (elementModulePullback.{u, u}
      (localCoefficientRings RY) A).mapDerivedCategoryFactors.{w, w}.hom.app
        ((onComplex f.modules).obj I) ≫
      DerivedCategory.Q.{w}.map ((NatIso.mapHomologicalComplex o.delta (.up ℤ)).hom.app I) ≫
      sliceDerived.eta.app ((onComplex (elementModulePullback.{u, u}
        (localCoefficientRings RX) (f.inverse.obj A))).obj I)) ∧
  -- derived_mate
  ((mateEquiv globalDerived.adj sliceDerived.adj
      (TwoSquare.mk _ _ _ _ theta.hom)).natTrans = beta.hom) ∧
  -- counit
  (∀ E : DerivedCategory (modules RX),
    theta.hom.app (globalDerived.right.obj E) ≫
      (elementModulePullback.{u, u}
        (localCoefficientRings RX) (f.inverse.obj A)).mapDerivedCategory.{w, w}.map
        (globalDerived.adj.counit.app E) =
    sliceDerived.left.map (beta.hom.app E) ≫ sliceDerived.adj.counit.app
      ((elementModulePullback.{u, u} (localCoefficientRings RX)
        (f.inverse.obj A)).mapDerivedCategory.{w, w}.obj E))



set_option maxHeartbeats 800000 in
-- The resolving-class construction instantiates several categories of large module sheaves.
private theorem sliceNormalizedDerived
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RX : Sheaf J CommRingCat.{u}) (RY : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism (localCoefficientRings RX) (localCoefficientRings RY))
    [HasDerivedCategory.{w} (modules RX)] [HasDerivedCategory.{w} (modules RY)]
    (G : modules RY ⥤ modules RX) [G.Additive] (a : G ⊣ f.modules) :
    ∃ d : DerivedAdjunction.{w} G f.modules a,
      (∀ P : CochainComplex (modules RY) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := RY) P →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u} (R := RY) (P.X n)) →
          IsIso (d.epsilon.app P)) ∧
      ∀ (M : CochainComplex (modules RY) ℤ) (I : CochainComplex (modules RX) ℤ)
        (h : (onComplex G).obj M ⟶ I),
        d.adj.homEquiv _ _ (d.epsilon.app M ≫ DerivedCategory.Q.map h) =
          DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv M I h) ≫
            d.eta.app I := by
  classical
  let A := modules RY
  let B := modules RX
  let πA := HomotopyCategory.quotient A (.up ℤ)
  let GF := G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh.{w}
  obtain ⟨G', hG', a', _, hpres⟩ := f.exists_kFlatPullback J K RX RY
  let := hG'
  let c := NatIso.mapHomologicalComplex (a'.leftAdjointUniq a) (.up ℤ)
  have hpresG (P Q : CochainComplex A ℤ) (s : P ⟶ Q)
      (hP : P.IsAcyclicTensorKFlat) (hfP : ∀ n : ℤ, (P.X n).IsFlat)
      (hQ : Q.IsAcyclicTensorKFlat) (hfQ : ∀ n : ℤ, (Q.X n).IsFlat)
      (hs : QuasiIso s) : QuasiIso ((onComplex G).map s) := by
    have h := hpres P Q s hP hfP hQ hfQ hs
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (c.app P) (c.app Q) (c.hom.naturality s).symm)).1 h
  let P : Set (HomotopyCategory A (.up ℤ)) :=
    {X | ∃ M : CochainComplex A ℤ, πA.obj M = X ∧
      M.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (M.X n).IsFlat}
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (X' : HomotopyCategory A (.up ℤ)) (s : X' ⟶ X),
        X' ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨M, s, hM, hf, hs, _⟩ := CochainComplex.exists_isKFlatResolution X
    exact ⟨πA.obj M, πA.map s, ⟨M, rfl, hM, hf⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hinv : ∀ (X Y : HomotopyCategory A (.up ℤ)) (s : X ⟶ Y),
      X ∈ P → Y ∈ P → HomotopyCategory.quasiIso A (.up ℤ) s → IsIso (GF.map s) := by
    intro X Y s hX hY hs
    obtain ⟨X, rfl, hX, hfX⟩ := hX
    obtain ⟨Y, rfl, hY, hfY⟩ := hY
    obtain ⟨s, rfl⟩ := πA.map_surjective s
    have hq := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).1 hs
    have ht := hpresG X Y s hX hfX hY hfY hq
    change IsIso (DerivedCategory.Qh.map
      ((G.mapHomotopyCategory (.up ℤ)).map (πA.map s)))
    rw [Functor.mapHomotopyCategory_map]
    exact Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso B (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ht)
  obtain ⟨_, L, εh, hL, _, hεh⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory.{w} B) GF P hres hinv
  let := hL
  obtain ⟨ε, hε, hεapp⟩ := leftDerivedOnComplexes G (𝟭 (DerivedCategory.{w} B)) L εh
  let := (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions
    J RX).1
  obtain ⟨RF, η, hη, hηgood⟩ := CategoryTheory.exists_derived f.modules
  obtain ⟨d, hd⟩ := derivedAdjunctionOfResolvingClass G f.modules a P hres hinv L εh hL
    RF η hη
  let e : DerivedAdjunction.{w} G f.modules a := {
    left := L
    right := RF
    epsilon := ε
    eta := η
    isLeft := hε
    isRight := hη
    onInjective := hηgood
    adj := d
    homFormula := by
      intro M I hI h
      apply (d.homEquiv _ _).injective
      rw [Equiv.apply_symm_apply, hεapp, hd]
      rw [Equiv.apply_symm_apply] }
  refine ⟨e, ?_, ?_⟩
  · intro M hM hf
    change IsIso (ε.app M)
    rw [hεapp]
    apply hεh (πA.obj M)
    refine ⟨M, rfl, ?_, ?_⟩
    · exact (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat M).mp hM
    · intro n
      exact (flat_iff_flatOnSite _).mpr (hf n)
  · intro M I h
    change d.homEquiv _ _ (ε.app M ≫ DerivedCategory.Q.map h) = _
    rw [hεapp]
    exact hd M I h


set_option maxHeartbeats 800000 in
-- Four exact localizations and their two adjunctions occur in each mate equation.
private theorem derivedComparisonOfOrdinary
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {RX : Sheaf J CommRingCat.{u}} {RY : Sheaf K CommRingCat.{u}}
    {f : RingedToposMorphism (localCoefficientRings RX) (localCoefficientRings RY)}
    {A : Sheaf K (Type u)}
    [HasDerivedCategory.{w} (modules RX)] [HasDerivedCategory.{w} (modules RY)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      (elementRing (localCoefficientRings RX) (f.inverse.obj A)))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      (elementRing (localCoefficientRings RY) A))]
    (o : RingedSheafSliceOrdinaryComparison RX RY f A) :
    HasRingedSheafSliceDerivedComparison.{u, w} o := by
  classical
  let := o.slicePullbackAdditive
  let := o.pullbackAdditive
  let := o.targetRestrictionAdditive
  let := o.sourceRestrictionAdditive
  let := o.targetRestrictionLimits
  let := o.sourceRestrictionLimits
  let := o.targetRestrictionColimits
  let := o.sourceRestrictionColimits
  let rA := elementModulePullback.{u, u} (localCoefficientRings RY) A
  let rB := elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A)
  let jA := rA.mapDerivedCategory.{w, w}
  let jB := rB.mapDerivedCategory.{w, w}
  let cA := rA.mapDerivedCategoryFactors.{w, w}
  let cB := rB.mapDerivedCategoryFactors.{w, w}
  obtain ⟨e, he, hen⟩ := sliceNormalizedDerived RX RY f o.pullback o.ordinaryAdjunction
  let : HasDerivedCategory.{w} (modules (presentationElementRing RX (f.inverse.obj A))) := by
    change HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      (elementRing (localCoefficientRings RX) (f.inverse.obj A)))
    infer_instance
  let : HasDerivedCategory.{w} (modules (presentationElementRing RY A)) := by
    change HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      (elementRing (localCoefficientRings RY) A))
    infer_instance
  obtain ⟨l, hl, hln⟩ := sliceNormalizedDerived
    (presentationElementRing RX (f.inverse.obj A)) (presentationElementRing RY A)
    o.slice o.slicePullback o.sliceOrdinaryAdjunction
  let := e.isRight
  let := l.isRight
  let := (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions
    J RX).1
  let := (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions
    (elementTopology (f.inverse.obj A)) (presentationElementRing RX (f.inverse.obj A))).1
  obtain ⟨beta, hb⟩ := SheafOfModules.rightComparisonGeneric f.modules o.slice.modules rA rB
    jA jB cA cB (NatIso.mapHomologicalComplex o.delta (.up ℤ))
    o.sourceKInjective e.right l.right e.eta l.eta
  let m := ((mateEquiv e.adj l.adj).symm (TwoSquare.mk _ _ _ _ beta.hom)).natTrans
  have hfac (P : CochainComplex (modules RY) ℤ) :
      m.app (DerivedCategory.Q.{w}.obj P) ≫
          jB.map (e.epsilon.app P) ≫ cB.hom.app ((onComplex o.pullback).obj P) =
        l.left.map (cA.hom.app P) ≫ l.epsilon.app ((onComplex rA).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex o.sigma (.up ℤ)).hom.app P) := by
    apply SheafOfModules.mateOnRepresentative
      (o.ordinaryAdjunction.mapHomologicalComplex (.up ℤ))
      (o.sliceOrdinaryAdjunction.mapHomologicalComplex (.up ℤ))
      (onComplex rA) (onComplex rB)
      DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
      e.adj l.adj jA jB cA cB e.epsilon e.eta l.epsilon l.eta
      (NatIso.mapHomologicalComplex o.delta (.up ℤ)) beta P
      ((NatIso.mapHomologicalComplex o.sigma (.up ℤ)).hom.app P)
    · apply HomologicalComplex.hom_ext
      intro n
      change o.sliceOrdinaryAdjunction.homEquiv _ _ (o.sigma.hom.app (P.X n)) = _
      rw [Adjunction.homEquiv_unit]
      have h := unit_mateEquiv o.ordinaryAdjunction o.sliceOrdinaryAdjunction
        (TwoSquare.mk _ _ _ _ o.sigma.hom) (P.X n)
      change rA.map (o.ordinaryAdjunction.unit.app (P.X n)) ≫
        ((mateEquiv o.ordinaryAdjunction o.sliceOrdinaryAdjunction
          (TwoSquare.mk _ _ _ _ o.sigma.hom)).natTrans).app
            (o.pullback.obj (P.X n)) = _ at h
      rw [o.ordinary_mate] at h
      exact h.symm
    · exact SheafOfModules.unitOfNormalized
        (o.ordinaryAdjunction.mapHomologicalComplex (.up ℤ))
        DerivedCategory.Q DerivedCategory.Q e.adj e.epsilon e.eta hen P
    · exact hb _
    · exact hln _ _ _
  have hm : IsIso m := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro X
    obtain ⟨P, s, hp, hf, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (DerivedCategory.Q.{w}.objPreimage X)
    let := hs
    have hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u} (R := RY) (P.X n) := by
      intro n
      apply (flat_iff_flatOnSite _).mp
      exact hf n
    obtain ⟨hrp, hrf⟩ := o.targetKFlat P hp hflat
    have := he P hp hflat
    have := hl ((onComplex rA).obj P) hrp hrf
    have hh := hfac P
    have : IsIso (m.app (DerivedCategory.Q.{w}.obj P) ≫
        jB.map (e.epsilon.app P) ≫ cB.hom.app ((onComplex o.pullback).obj P)) := by
      rw [hh]
      infer_instance
    have : IsIso (m.app (DerivedCategory.Q.{w}.obj P)) :=
      IsIso.of_isIso_comp_right (m.app (DerivedCategory.Q.{w}.obj P))
        (jB.map (e.epsilon.app P) ≫ cB.hom.app ((onComplex o.pullback).obj P))
    exact SheafOfModules.isIsoAppTransport m
      (asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso X)
  let := hm
  let theta := asIso m
  have hmate : (mateEquiv e.adj l.adj
      (TwoSquare.mk _ _ _ _ theta.hom)).natTrans = beta.hom := by
    change (mateEquiv e.adj l.adj
      ((mateEquiv e.adj l.adj).symm (TwoSquare.mk _ _ _ _ beta.hom))).natTrans = _
    rw [Equiv.apply_symm_apply]
  refine ⟨e, l, theta, beta, he, hl, ?_, ?_, hmate, ?_⟩
  · intro P _ _
    exact hfac P
  · intro I _
    exact hb I
  · intro E
    have h := mateEquiv_counit e.adj l.adj (TwoSquare.mk _ _ _ _ theta.hom) E
    change l.left.map (((mateEquiv e.adj l.adj
      (TwoSquare.mk _ _ _ _ theta.hom)).natTrans).app E) ≫
        l.adj.counit.app (jB.obj E) = _ at h
    rw [hmate] at h
    exact h.symm

/-- Every ringed-topos morphism has canonical ordinary and unbounded derived comparisons
on the slice at any sheaf of sets.

Source: Stacks 04IF and 04H1; unbounded computations: 0G7E, 08FI, 07A6, 07A7 and 09T5
(blueprint: lem-sbc-ringed-topos-sheaf-slice-derived-comparison).

Proof. First construct the ordinary comparison square (Stacks 04IF). Its exact
restrictions give the canonical termwise localization factors. For either ordinary
pullback, transport quasi-isomorphism preservation from the tensor pullback along
the unique isomorphism of left adjoints. Flat-term K-flat resolutions form a
resolving class. Apply `derivedAdjunctionOfResolvingClass` to obtain the derived
adjunction with its chain-transpose normalization on every complex.

Right-derived uniqueness, using preservation of K-injectives by source restriction,
constructs beta and its representative equation. Define theta to be its inverse
mate. The ordinary mate equation and the normalized derived units imply the
representative equation for theta. On a flat-term K-flat resolution, both epsilon
comparisons and the ordinary sigma are invertible, so theta is invertible.
Transport this along the resolution to every derived object. The counit identity
is the standard mate identity. No flatness of the structural map is used. -/
theorem ringedSheafSliceDerivedComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RX : Sheaf J CommRingCat.{u}) (RY : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism (localCoefficientRings RX) (localCoefficientRings RY))
    (A : Sheaf K (Type u))
    [HasDerivedCategory.{w} (modules RX)] [HasDerivedCategory.{w} (modules RY)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      (elementRing (localCoefficientRings RX) (f.inverse.obj A)))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      (elementRing (localCoefficientRings RY) A))] :
    ∃ o : RingedSheafSliceOrdinaryComparison RX RY f A,
      HasRingedSheafSliceDerivedComparison.{u, w} o := by
  obtain ⟨o⟩ := ringedSheafSliceOrdinaryComparison RX RY f A
  exact ⟨o, derivedComparisonOfOrdinary o⟩

end CategoryTheory
