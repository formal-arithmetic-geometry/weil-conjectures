/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q44 and U7
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
import Sheaf.CategoryTheory.SiteTorIntervalRestriction
import Sheaf.Paper.WeilTensorProduct
import Sheaf.Algebra.Homology.KFlatClosure
import Sheaf.Algebra.Homology.AcyclicKFlatTensor
import Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat
import Sheaf.Algebra.Homology.SliceTensorNatural
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Data.Fintype.Order

/-!
# Local and global finite Tor dimension on a quasi-compact pro-etale site

Source: Stacks Project, Tags 08FZ and 09C2, the uniform Tor interval in the proof of
`lemma-describe-constructible-complexes`
(blueprint: lem-sfb-proetale-tor-local-global).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The recorded exact derived slice restriction at the standard localizations used by
`HasCoefficientModelTorAmplitude`. Both rings are the actual sectionwise restrictions.
Source: Stacks Tags 03DH and 08JB (blueprint: lem-sfb-proetale-tor-local-global). -/
def coefficientModelSliceRestriction {C : Type w} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w}) (V : C) :
    ConstantCompletion.D R ⥤ ConstantCompletion.D (R.over V) :=
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  letI := HasDerivedCategory.standard (SheafOfModules.{w} ((siteModuleRings R).over V))
  ringedDerivedRestrictionSized (siteModuleRings R) V

end CategoryTheory

section ProofHelpers
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MonoidalCategory
namespace CategoryTheory

-- Signed symmetry of the total tensor; Stacks Tag 06YT.
private noncomputable def tensor_symmetry
    {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) (K L : ConstantCompletion.Cx R) :
    letI := SheafOfModules.monoidalCategory R
    CochainComplex.mapBifunctor K L (curriedTensor _) ≅
      CochainComplex.mapBifunctor L K (curriedTensor _) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let T := curriedTensor (ConstantCompletion.Mod R)
  let A := ((T.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L
  let B := ((T.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L
  let e : A ≅ B := HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ HomologicalComplex.Hom.isoOfComponents
      (fun q ↦ β_ (K.X p) (L.X q)) (by
        intro q q' hq
        exact (BraidedCategory.braiding_naturality_right (K.X p) (L.d q q')).symm))
    (by
      intro p p' hp
      ext q : 1
      exact (BraidedCategory.braiding_naturality_left (K.d p p') (L.X q)).symm)
  exact HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
    HomologicalComplex.mapBifunctorFlipIso L K T (.up ℤ)

-- The acyclic K-flat cone tests against arbitrary complexes; Tags 06Y0 and 06YT.
private theorem tensor_quasiIso
    {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) {P P' : ConstantCompletion.Cx R}
    (f : P ⟶ P') (hf : QuasiIso f)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := R) P')
    (D : ConstantCompletion.Cx R) :
    letI := SheafOfModules.monoidalCategory R
    QuasiIso (HomologicalComplex.mapBifunctorMap f (𝟙 D) (curriedTensor _) (.up ℤ)) := by
  let := SheafOfModules.monoidalCategory R
  let := Classical.choice (SheafOfModules.tensorClosed R).1
  have hc : (CochainComplex.mappingCone f).Acyclic :=
    (CochainComplex.mappingCone.quasiIso_iff_acyclic f).1 hf
  have hk := CochainComplex.isKFlat_mappingCone f hP hP'
  have ht := SheafOfModules.tensor_acyclic_of_isKFlat _ hk hc D
  have ht' : (CochainComplex.mapBifunctor (CochainComplex.mappingCone f) D
      (curriedTensor _)).Acyclic :=
    fun q ↦ (ht q).of_iso (tensor_symmetry R _ _)
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  exact fun q ↦ (ht' q).of_iso
    (CochainComplex.mapBifunctorMappingCone₁Iso f D (curriedTensor _))

-- Compare an arbitrary K-flat model with a flat-term resolution; Tags 06YS and 06YT.
private theorem tensor_representation
    {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) (P D : ConstantCompletion.Cx R)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    letI := HasDerivedCategory.standard (ConstantCompletion.Mod R)
    Nonempty ((ConstantCompletion.Q R).obj (((ringedKoszulTensor R).obj P).obj D) ≅
      (SheafOfModules.wfSiteDerivedTensor J R).obj
        ((ConstantCompletion.Q R).obj P, (ConstantCompletion.Q R).obj D)) := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let := SheafOfModules.monoidalCategory R
  let := Classical.choice (SheafOfModules.tensorClosed R).1
  obtain ⟨F, f, hF, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
  have : QuasiIso f := hf
  let t := HomologicalComplex.mapBifunctorMap f (𝟙 D) (curriedTensor _) (.up ℤ)
  have : QuasiIso t := tensor_quasiIso R f hf hF hP D
  have : IsIso (DerivedCategory.Q.map t) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ t).2 inferInstance
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hf
  obtain ⟨e⟩ := SheafOfModules.wfSiteDerivedTensor_first J R F D hF hflat
  exact ⟨(asIso (DerivedCategory.Q.map t)).symm ≪≫ e ≪≫
    (SheafOfModules.wfSiteDerivedTensor J R).mapIso
      (Iso.prod (asIso (DerivedCategory.Q.map f)) (Iso.refl _))⟩


-- The localization homology factorization gives the same universal Tor test; Tag 08FZ.
private theorem coefficientModelTorAmplitude_iff_localizedTensor
    {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) (M : ConstantCompletion.D R) (a b : ℤ) :
    HasCoefficientModelTorAmplitude R M a b ↔
      a ≤ b ∧
        letI := HasDerivedCategory.standard (ConstantCompletion.Mod R)
        ∀ (N : ConstantCompletion.Mod R) (q : ℤ), q < a ∨ b < q →
          IsZero ((DerivedCategory.homologyFunctor _ q).obj
            ((SheafOfModules.wfSiteDerivedTensor J R).obj
              (M, (DerivedCategory.singleFunctor _ 0).obj N))) := by
  classical
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  constructor
  · rintro ⟨hab, h⟩
    refine ⟨hab, ?_⟩
    intro N q hq
    obtain ⟨P, f, hP, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (DerivedCategory.Q.objPreimage M)
    have : IsIso (DerivedCategory.Q.map f) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hf
    let e : (ConstantCompletion.Q R).obj P ≅ M :=
      asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso M
    let D := (HomologicalComplex.single (ConstantCompletion.Mod R) (.up ℤ) 0).obj N
    have hz := h P hP ⟨e⟩ N q hq
    obtain ⟨t⟩ := tensor_representation R P D hP
    let c := t ≪≫ (SheafOfModules.wfSiteDerivedTensor J R).mapIso
      (Iso.prod e (Iso.refl _))
    exact hz.of_iso ((DerivedCategory.homologyFunctorFactors _ q).symm.app _ ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso c).symm
  · rintro ⟨hab, h⟩
    refine ⟨hab, ?_⟩
    intro P hP he N q hq
    obtain ⟨e⟩ := he
    let D := (HomologicalComplex.single (ConstantCompletion.Mod R) (.up ℤ) 0).obj N
    obtain ⟨t⟩ := tensor_representation R P D hP
    let c := t ≪≫ (SheafOfModules.wfSiteDerivedTensor J R).mapIso
      (Iso.prod e (Iso.refl _))
    exact (h N q hq).of_iso
      ((DerivedCategory.homologyFunctorFactors _ q).symm.app _ ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso c)

-- Tag 08H5, transported between the two recorded derived restriction models.
private theorem coefficientModelTorAmplitude_restrict
    {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) (V : C)
    (M : ConstantCompletion.D R) (a b : ℤ)
    (h : HasCoefficientModelTorAmplitude R M a b) :
    HasCoefficientModelTorAmplitude (R.over V)
      ((coefficientModelSliceRestriction R V).obj M) a b := by
  classical
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (R.over V))
  let := HasDerivedCategory.standard (SheafOfModules.{w} ((siteModuleRings R).over V))
  obtain ⟨hab, htest⟩ := (coefficientModelTorAmplitude_iff_localizedTensor R M a b).1 h
  apply (coefficientModelTorAmplitude_iff_localizedTensor (R.over V) _ a b).2
  refine ⟨hab, ?_⟩
  intro N q hq
  have hz := siteTorIntervalRestriction J R V a b hab M htest N q hq
  let A := siteModuleRings R
  let F := SheafOfModules.overFunctor.{w} A V
  have : F.Additive := (ringedOverFunctor_exactGeneral.{w, w, w, w} A V).1
  have : PreservesFiniteLimits F := (ringedOverFunctor_exactGeneral.{w, w, w, w} A V).2.1
  have : PreservesFiniteColimits F := (ringedOverFunctor_exactGeneral.{w, w, w, w} A V).2.2
  let e : ringedSiteDerivedRestrictionOfUniverses.{w, w, w, w, w + 1, w + 1} A V M ≅
      (coefficientModelSliceRestriction R V).obj M :=
    (F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage M)).symm ≪≫
      F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso M)
  exact hz.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
    ((SheafOfModules.wfSiteDerivedTensor (J.over V) (R.over V)).mapIso
      (Iso.prod e.symm (Iso.refl _))))

-- Exact K-flat restriction and natural tensor restriction; Tags 0E8K, 07A4 and 08FZ.
private theorem coefficientModelTorAmplitude_restricted_test_isZero
    {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) (V : C)
    (M : ConstantCompletion.D R) (a b : ℤ)
    (h : HasCoefficientModelTorAmplitude (R.over V)
      ((coefficientModelSliceRestriction R V).obj M) a b)
    (P : ConstantCompletion.Cx R)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (e : Nonempty ((ConstantCompletion.Q R).obj P ≅ M))
    (N : ConstantCompletion.Mod R) (q : ℤ) (hq : q < a ∨ b < q) :
    IsZero ((SheafOfModules.overFunctor (siteModuleRings R) V).obj
      ((((ringedKoszulTensor R).obj P).obj
        ((HomologicalComplex.single (ConstantCompletion.Mod R)
          (ComplexShape.up ℤ) 0).obj N)).homology q)) := by
  classical
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (R.over V))
  let A := siteModuleRings R
  let F : ConstantCompletion.Mod R ⥤ ConstantCompletion.Mod (R.over V) :=
    SheafOfModules.overFunctor.{w} A V
  have : F.Additive := (ringedOverFunctor_exactGeneral.{w, w, w, w} A V).1
  have : PreservesFiniteLimits F := (ringedOverFunctor_exactGeneral.{w, w, w, w} A V).2.1
  have : PreservesFiniteColimits F := (ringedOverFunctor_exactGeneral.{w, w, w, w} A V).2.2
  let FC := F.mapHomologicalComplex (.up ℤ)
  have hres : CochainComplex.IsKFlatIndependentCoefficients (R := R.over V) (FC.obj P) :=
    (SheafOfModules.ringedSite_restriction_exact_kflat.{w, w, w} J R V).2.2 P hP
  obtain ⟨e⟩ := e
  have er : Nonempty ((ConstantCompletion.Q (R.over V)).obj (FC.obj P) ≅
      (coefficientModelSliceRestriction R V).obj M) :=
    ⟨(F.mapDerivedCategoryFactors.app P).symm ≪≫ F.mapDerivedCategory.mapIso e⟩
  have hz := h.2 (FC.obj P) hres er (F.obj N) q hq
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory (R.over V)
  let := Classical.choice (SheafOfModules.tensorClosed R).1
  let := Classical.choice (SheafOfModules.tensorClosed (R.over V)).1
  let d : tensorRight N ⋙ F ≅ F ⋙ tensorRight (F.obj N) :=
    NatIso.ofComponents
      (fun L ↦ SheafOfModules.sliceTensorIso (J := J.over V) (Over.forget V) R L N)
      (by
        intro L L' f
        simpa [F, SheafOfModules.sliceCommModuleRestriction,
          SheafOfModules.sliceModuleRestriction, SheafOfModules.overFunctor] using
          SheafOfModules.sliceTensorIso_natural (J := J.over V)
          (Over.forget V) R f (𝟙 N))
  let dC := ((Functor.mapHomologicalComplexCompIso (Iso.refl (tensorRight N ⋙ F))
    (.up ℤ)).app P) ≪≫ ((NatIso.mapHomologicalComplex d (.up ℤ)).app P) ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ tensorRight (F.obj N)))
        (.up ℤ)).app P).symm
  let K := CochainComplex.mapBifunctor P
    ((HomologicalComplex.single _ (.up ℤ) 0).obj N) (curriedTensor _)
  let c := FC.mapIso (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) N P) ≪≫
    dC ≪≫ (CochainComplex.mapBifunctorSingle₂Iso
      (curriedTensor _) (F.obj N) (FC.obj P)).symm
  let hc := ((K.sc q).mapHomologyIso F).symm ≪≫
    (HomologicalComplex.homologyFunctor _ (.up ℤ) q).mapIso c
  exact hz.of_iso hc

-- Detect zero sectionwise using uniqueness for covering sieves; Stacks Tag 00VR.
private theorem isZero_of_slice_cover
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat) {I : Type*} (V : I → C) (hV : J.CoversTop V)
    (F : SheafOfModules R)
    (hF : ∀ i, IsZero ((SheafOfModules.overFunctor R (V i)).obj F)) : IsZero F := by
  apply (IsZero.iff_id_eq_zero F).2
  apply (SheafOfModules.toSheaf R).map_injective
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply F.isSheaf.hom_ext (hV.cover U.unop)
  rintro ⟨W, f, ⟨i, ⟨g⟩⟩⟩
  have h := congrArg
    (fun k ↦ k.val.app (Opposite.op (Over.mk g)))
    ((hF i).eq_of_src (𝟙 _) 0)
  have hz : (𝟙 (F.val.presheaf.obj (Opposite.op W))) = 0 := by
    apply AddCommGrpCat.hom_ext
    exact congrArg (fun k ↦ k.hom.toAddMonoidHom) h
  change (𝟙 _ : F.val.presheaf.obj U ⟶ _) ≫ _ = 0 ≫ _
  simp only [Category.id_comp, zero_comp]
  rw [← Category.comp_id (F.val.presheaf.map f.op), hz, comp_zero]

end CategoryTheory

namespace AlgebraicGeometry.Scheme

-- Retain finitely many original presieve members over an affine target; Tag 0989.
private theorem affine_finite_cover
    (X : Scheme.{u}) (U : X.ProEt) [IsAffine U.left]
    (S : Presieve ((AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).obj U))
    (hS : Sieve.generate S ∈ coefficientProEtaleModelTopology.{u, v} X _)
    (P : coefficientProEtaleSiteModel.{u, v} X → Prop)
    (hP : ∀ (V : coefficientProEtaleSiteModel.{u, v} X) (f : V ⟶ AsSmall.up.obj U),
      S f → P V) :
    ∃ (n : ℕ) (V : Fin n → coefficientProEtaleSiteModel.{u, v} X),
      Sieve.ofObjects V (AsSmall.up.obj U) ∈ coefficientProEtaleModelTopology.{u, v} X _ ∧
        ∀ i, P (V i) := by
  classical
  let F : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt := AsSmall.down
  have : F.IsEquivalence :=
    inferInstanceAs ((AsSmall.equiv.{u, u + 1, max v (u + 1)}
      (C := X.ProEt)).inverse.IsEquivalence)
  have hdown : (Sieve.generate S).functorPushforward F ∈ ProEt.topology X U :=
    (Functor.mem_inducedTopology_iff_of_isCoverDense _ _ _).1 hS
  obtain ⟨T, hT, hTS⟩ :=
    (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition
      (J := ProEt.precoverage X)).1 hdown
  let E : (ProEt.precoverage X).ZeroHypercover U :=
    ⟨T.preZeroHypercover, by simpa using hT⟩
  let G := ProEt.forget X ⋙ Over.forget X
  let D := E.map G (le_refl _)
  have : QuasiCompactCover D.toPreZeroHypercover := by
    exact inferInstanceAs (QuasiCompactCover
      (show Scheme.Cover (Scheme.propQCPrecoverage (@WeaklyEtale)) U.left from D).1)
  obtain ⟨n, idx, W, hW, hcov⟩ :=
    QuasiCompactCover.exists_isAffineOpen_of_isCompact D.toPreZeroHypercover
      (U := ⊤) (by simpa using isCompact_univ (X := U.left))
  have hmember (i : Fin n) : ∃ (V : coefficientProEtaleSiteModel.{u, v} X),
      P V ∧ Nonempty ((E.X (idx i)) ⟶ F.obj V) := by
    have ht : T (E.f (idx i)) := (idx i).2
    obtain ⟨V, f, g, hf, _⟩ := hTS _ _ ht
    obtain ⟨V', k, l, hl, _⟩ := hf
    exact ⟨V', hP V' l hl, ⟨g ≫ F.map k⟩⟩
  choose V hV e using hmember
  refine ⟨n, V, ?_, hV⟩
  let Yobj (i : Fin n) : X.ProEt := ProEt.mk ((W i).ι ≫ (E.X (idx i)).hom)
  let g (i : Fin n) : Yobj i ⟶ U := MorphismProperty.Over.homMk
    ((W i).ι ≫ (D.f (idx i))) (by
      change (W i).ι ≫ (E.f (idx i)).left ≫ U.hom = _
      have hw := (E.f (idx i)).w
      change (E.f (idx i)).left ≫ U.hom = (E.X (idx i)).hom ≫ 𝟙 X at hw
      have hw' : (E.f (idx i)).left ≫ U.hom = (E.X (idx i)).hom :=
        hw.trans (@Category.comp_id Scheme inferInstance _ _ _)
      exact congrArg (fun k ↦ (W i).ι ≫ k) hw')
  let B : Scheme.Cover (Scheme.precoverage (@WeaklyEtale)) U.left :=
    { I₀ := Fin n
      X := fun i ↦ (W i).toScheme
      f := fun i ↦ (g i).left
      mem₀ := by
        rw [Scheme.ofArrows_mem_precoverage_iff]
        constructor
        · intro x
          have hx : x ∈ ⋃ i, D.f (idx i) '' (W i) := by rw [hcov]; trivial
          obtain ⟨i, y, hy, hxy⟩ := Set.mem_iUnion.mp hx
          exact ⟨i, ⟨⟨y, hy⟩, hxy⟩⟩
        · intro i
          have : WeaklyEtale (D.f (idx i)) :=
            (show Scheme.Cover (Scheme.precoverage (@WeaklyEtale)) U.left from
              D.weaken Scheme.propQCPrecoverage_le_precoverage).map_prop _
          exact MorphismProperty.comp_mem _ _ _ inferInstance this }
  have (i : Fin n) : IsAffine (B.X i) := hW i
  have (i : Fin n) : IsAffine ((W i).toScheme) := hW i
  have : QuasiCompactCover B.1 :=
    QuasiCompactCover.of_finite
  let K : (ProEt.precoverage X).ZeroHypercover U :=
    { I₀ := Fin n
      X := Yobj
      f := g
      mem₀ := by
        change (Presieve.ofArrows Yobj g).map G ∈ Scheme.proetalePrecoverage U.left
        rw [Presieve.map_ofArrows]
        exact B.ofQuasiCompactCover.mem₀ }
  apply (Functor.mem_inducedTopology_iff_of_isCoverDense _ _ _).2
  apply (ProEt.topology X).superset_covering _
    (Precoverage.generate_mem_toGrothendieck K.mem₀)
  rw [Sieve.generate_le_iff]
  rintro Z f ⟨i⟩
  refine ⟨AsSmall.up.obj (Yobj i), AsSmall.up.map (g i), 𝟙 _, ?_, ?_⟩
  · refine ⟨i, ⟨AsSmall.up.map
        (MorphismProperty.Over.homMk (W i).ι (by simp [Yobj]) ≫ (e i).some)⟩⟩
  · rfl


-- Combine the affine selections over a finite open cover; Tags 098B and 098C.
private theorem coefficientProEtale_exists_finite_cover
    (X : Scheme.{u}) [CompactSpace X]
    (P : coefficientProEtaleSiteModel.{u, v} X → Prop)
    (hP : ∀ U : coefficientProEtaleSiteModel.{u, v} X,
      ∃ S : Presieve U,
        Sieve.generate S ∈ coefficientProEtaleModelTopology.{u, v} X U ∧
          ∀ (V : coefficientProEtaleSiteModel.{u, v} X) (f : V ⟶ U), S f → P V) :
    ∃ (n : ℕ) (V : Fin n → coefficientProEtaleSiteModel.{u, v} X),
      (coefficientProEtaleModelTopology.{u, v} X).CoversTop V ∧ ∀ i, P (V i) := by
  classical
  let 𝒰 := X.affineCover.finiteSubcover
  let W (i : 𝒰.I₀) : X.ProEt := ProEt.mk (𝒰.f i)
  have (i : 𝒰.I₀) : IsAffine (W i).left := by
    dsimp [W, 𝒰, OpenCover.finiteSubcover]
    change IsAffine (X.affineCover.X _)
    infer_instance
  have hf (i : 𝒰.I₀) : ∃ (n : ℕ)
      (V : Fin n → coefficientProEtaleSiteModel.{u, v} X),
      Sieve.ofObjects V (AsSmall.up.obj (W i)) ∈
        coefficientProEtaleModelTopology.{u, v} X _ ∧ ∀ j, P (V j) := by
    obtain ⟨S, hS, hSP⟩ := hP (AsSmall.up.obj (W i))
    exact affine_finite_cover X (W i) S hS P hSP
  choose n V hV hPV using hf
  let I := Σ i : 𝒰.I₀, Fin (n i)
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I, fun j ↦ V (e.symm j).1 (e.symm j).2, ?_,
    fun j ↦ hPV _ _⟩
  let T : X.ProEt := ProEt.mk (𝟙 X)
  have ht : IsTerminal T := by
    apply IsTerminal.ofUniqueHom
      (fun U ↦ MorphismProperty.Over.homMk U.hom (by change U.hom ≫ 𝟙 X = U.hom; simp))
    intro U f
    apply MorphismProperty.Over.Hom.ext
    have hw := f.w
    change f.left ≫ 𝟙 X = U.hom ≫ 𝟙 X at hw
    change f.left = U.hom
    exact (@Category.comp_id Scheme inferInstance _ _ f.left).symm.trans
      (hw.trans (@Category.comp_id Scheme inferInstance _ _ U.hom))
  have : (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).IsEquivalence :=
    inferInstanceAs ((AsSmall.equiv.{u, u + 1, max v (u + 1)}
      (C := X.ProEt)).functor.IsEquivalence)
  have ht' : IsTerminal (AsSmall.up.obj T : coefficientProEtaleSiteModel.{u, v} X) :=
    (IsTerminal.isTerminalObj AsSmall.up T ht)
  apply (GrothendieckTopology.coversTop_iff_of_isTerminal _ _ ht' _).2
  let f (i : 𝒰.I₀) : W i ⟶ T := MorphismProperty.Over.homMk (𝒰.f i) (by
    change 𝒰.f i ≫ 𝟙 X = 𝒰.f i
    simp)
  have hc : Sieve.generate (Presieve.ofArrows W f) ∈ ProEt.topology X T := by
    apply Precoverage.generate_mem_toGrothendieck
    change (Presieve.ofArrows W f).map (ProEt.forget X ⋙ Over.forget X) ∈
      proetalePrecoverage X
    rw [Presieve.map_ofArrows]
    apply etalePrecoverage_le_proetalePrecoverage
    change 𝒰.presieve₀ ∈ etalePrecoverage X
    exact (Scheme.precoverage_mono (show (@IsOpenImmersion :
      MorphismProperty Scheme) ≤ @Etale from fun _ _ _ _ ↦ inferInstance)) _ 𝒰.mem₀
  have hc' : (Sieve.generate (Presieve.ofArrows W f)).functorPushforward
      (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X) ∈
        coefficientProEtaleModelTopology.{u, v} X (AsSmall.up.obj T) := by
    exact (CoverPreserving.of_isContinuous AsSmall.up _ _).cover_preserve hc
  apply (coefficientProEtaleModelTopology.{u, v} X).transitive hc'
  intro Z g hg
  obtain ⟨Y, t, k, hk, _⟩ := hg
  obtain ⟨Y', l, m, hm, _⟩ := hk
  obtain ⟨i⟩ := hm
  apply (coefficientProEtaleModelTopology.{u, v} X).superset_covering _
    ((coefficientProEtaleModelTopology.{u, v} X).pullback_stable (k ≫ AsSmall.up.map l) (hV i))
  rintro Z' a ⟨j, ⟨b⟩⟩
  refine ⟨e ⟨i, j⟩, ?_⟩
  change Nonempty (Z' ⟶ (fun p : I ↦ V p.1 p.2) (e.symm (e ⟨i, j⟩)))
  rw [e.symm_apply_apply]
  exact ⟨b⟩

end AlgebraicGeometry.Scheme
end ProofHelpers

namespace AlgebraicGeometry.Scheme

/-- Global finite Tor dimension is equivalent to finite Tor dimension locally on every
object of the small pro-etale site. A covering is expressed by a presieve whose generated
sieve belongs to the topology; each of its arrows has its own ordered Tor interval.
The coefficient-sized small model retains all objects and coverings of the recorded site.
Source: Stacks Tags 08FZ and 09C2 (blueprint: lem-sfb-proetale-tor-local-global).

Proof:
1. Exact module restriction (`lem-pur-site-restriction-module-adjunction-exact`) commutes
   with cohomology (`lem-weil-pbc-exact-functor-complex-cohomology`). The localization case
   of `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` identifies restricted derived
   tensor with derived tensor of restrictions, for arbitrary unbounded complexes.
2. A global interval remains an interval against every slice module by
   `lem-sf-site-tor-interval-restriction`. Use the identity covering of each object.
   The two recorded restrictions both send Q(C) to Q(C|U). The tensor models agree by
   `lem-weil-pbc-site-derived-tensor-descent`, since flat-term K-flat resolutions are K-flat.
3. Conversely, quasi-compactness gives a finite affine open covering of X. Apply the local
   hypothesis to each member. The affine-target finite refinement in `sk-def-pe-site`
   refines each resulting covering to a finite affine covering. Compose these coverings,
   using `def-weil-pbc-sites-and-cohomology`, to obtain a finite covering of X.
4. Restrict the selected intervals further along the refinement, again using
   `lem-sf-site-tor-interval-restriction`. Relocalization identifies the iterated restriction
   with restriction to the refined object (`def-pur-localized-ringed-site`). Take the minimum
   of the finitely many lower bounds and 0, and the maximum of the upper bounds and 0.
   This gives an ordered common interval and includes the empty-scheme case.
5. For every global module N and q outside this interval, step 1 identifies the restriction
   of H^q(M tensor N) with the corresponding local cohomology. Step 4 makes each zero.
6. Base change the finite cover to any test object T. Sectionwise slice restriction and
   the sheaf equalizer axiom make sections over T inject into the product of zero groups.
   Thus the global cohomology sheaf is zero. The empty cover has the same conclusion.
-/
theorem hasFiniteCoefficientProEtaleTorAmplitude_iff_locally
    (X : Scheme.{u}) [CompactSpace X]
    (A : Type (max v (u + 1))) [CommRing A]
    (M : ConstantCompletion.D
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) A)) :
    HasFiniteCoefficientProEtaleTorAmplitude X A M ↔
      ∀ U : coefficientProEtaleSiteModel.{u, v} X,
        ∃ S : Presieve U,
          Sieve.generate S ∈ coefficientProEtaleModelTopology.{u, v} X U ∧
            ∀ (V : coefficientProEtaleSiteModel.{u, v} X) (f : V ⟶ U), S f →
              ∃ a b : ℤ,
                HasCoefficientModelTorAmplitude
                  ((ConstantCompletion.constant
                    (coefficientProEtaleModelTopology.{u, v} X) A).over V)
                  ((coefficientModelSliceRestriction
                    (ConstantCompletion.constant
                      (coefficientProEtaleModelTopology.{u, v} X) A) V).obj M) a b := by
  constructor
  · rintro ⟨a, b, h⟩ U
    refine ⟨⊤, ?_, ?_⟩
    · simp
    · intro V f _
      exact ⟨a, b, coefficientModelTorAmplitude_restrict _ V M a b h⟩
  · classical
    intro hlocal
    obtain ⟨n, V, hcover, hV⟩ := coefficientProEtale_exists_finite_cover X
      (fun V ↦ ∃ a b : ℤ, HasCoefficientModelTorAmplitude
        ((ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) A).over V)
        ((coefficientModelSliceRestriction
          (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) A) V).obj M)
        a b) hlocal
    choose a b hab using hV
    obtain ⟨lo, hlo⟩ := Finite.bddBelow_range a
    obtain ⟨hi, hhi⟩ := Finite.bddAbove_range b
    refine ⟨min lo 0, max hi 0, ?_, ?_⟩
    · exact (min_le_right _ _).trans (le_max_right _ _)
    · intro P hP e N q hq
      apply isZero_of_slice_cover _ V hcover
      intro i
      apply coefficientModelTorAmplitude_restricted_test_isZero _ (V i) M
        (a i) (b i) (hab i) P hP e N q
      rcases hq with hq | hq
      · exact Or.inl (hq.trans_le ((min_le_left _ _).trans (hlo ⟨i, rfl⟩)))
      · exact Or.inr (((hhi ⟨i, rfl⟩).trans (le_max_left _ _)).trans_lt hq)

end AlgebraicGeometry.Scheme
