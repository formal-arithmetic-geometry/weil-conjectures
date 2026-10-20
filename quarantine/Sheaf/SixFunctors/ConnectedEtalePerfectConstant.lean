/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.DerivedStalk
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Sites.Point.Basic

import Sheaf.SixFunctors.GeometricStalkTensorConstantSingle
import Sheaf.SixFunctors.WeaklyContractibleEtaleConstantModels
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.Paper.SiteBoundedConstantModel
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison

import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Topology.Connected.Clopen
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
import WeilConjectures.ConstructibleSheaf.Pullback

/-!
# Connected étale finite-Tor complexes are locally constant perfect complexes

Source: Stacks Project, `etale-cohomology.tex`, Tag 09BI, lemma-connected-ctf-locally-constant;
the weakly contractible pro-étale corollary is from `proetale.tex`, Tag 09C6,
and `sites.tex`, Tag 090K (blueprint: lem-sfb-connected-etale-perfect-constant).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- The derived geometric stalk, obtained from the exact fibre functor.
Source: Stacks Project, `etale-cohomology.tex`, Tag 09BI
(blueprint: lem-sfb-connected-etale-perfect-constant). -/
noncomputable def geometricStalk
    (R : Type (u + 1)) [CommRing R] {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ⥤
      _root_.DerivedCategory (ModuleCat.{u + 1} R) := by
  let F := (pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} R)
  letI : F.Additive := (pointSmallEtale x).sheafFiber_additive
  exact F.mapDerivedCategory

private instance : etalePrecoverage.{u}.IsStableUnderComposition :=
  inferInstanceAs (precoverage @AlgebraicGeometry.Etale).IsStableUnderComposition

private instance : etalePrecoverage.{u}.IsStableUnderBaseChange :=
  inferInstanceAs (precoverage @AlgebraicGeometry.Etale).IsStableUnderBaseChange

private instance : JointlySurjective etalePrecoverage.{u} :=
  inferInstanceAs (JointlySurjective (precoverage @AlgebraicGeometry.Etale))

private instance (R : Type (u + 1)) [CommRing R] :
    PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} R)) :=
  preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _

set_option backward.isDefEq.respectTransparency false in
private noncomputable def overRestrictionIso
    {X : Scheme.{u}} (B : Type (u + 1)) [CommRing B] (U : X.Etale) :
    X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) U ⋙
      (Scheme.Etale.overSheafEquiv U (ModuleCat.{u + 1} B)).functor ≅
        upperStar (ModuleCat.{u + 1} B) U.hom :=
  let R := GrothendieckTopology.localizationRestriction (ModuleCat.{u + 1} B)
    @AlgebraicGeometry.Etale @AlgebraicGeometry.Etale le_rfl U.hom U.prop
  let e : X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) U ⋙
      (Scheme.Etale.overSheafEquiv U (ModuleCat.{u + 1} B)).functor ≅ R :=
    ((fullyFaithfulSheafToPresheaf U.left.smallEtaleTopology
      (ModuleCat.{u + 1} B)).whiskeringRight _).preimageIso
        (NatIso.ofComponents
          (fun F ↦ by
            change ((Scheme.Etale.etaleToOver U).op ⋙
              (Over.forget U).op ⋙ F.obj) ≅ _
            exact Functor.isoWhiskerRight
              (NatIso.op (Scheme.Etale.etaleToOverCompForgetIso U).symm) F.obj)
          (by
            intro F G φ
            apply NatTrans.ext
            funext T
            dsimp
            exact (φ.hom.naturality _).symm))
  e ≪≫ (GrothendieckTopology.upperStarIsoLocalizationRestriction
    (ModuleCat.{u + 1} B) @AlgebraicGeometry.Etale @AlgebraicGeometry.Etale
    le_rfl U.hom U.prop).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem noetherian_bounded_constant_models
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [IsNoetherianRing B]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (a b : ℤ) (hab : a ≤ b)
    (hvan : ∀ q : ℤ, q < a ∨ b < q → IsZero
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) q).obj K))
    (hloc : ∀ (q : ℤ) (V : X.Etale),
      ∃ (I : Type (u + 1)) (U : I → X.Etale) (f : ∀ i, U i ⟶ V),
        Sieve.ofArrows U f ∈ X.smallEtaleTopology V ∧
        ∀ i, ∃ M : ModuleCat.{u + 1} B, Module.Finite B M ∧ Nonempty
          (((DerivedCategory.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) q).obj K).over (U i) ≅
            (constantSheaf (X.smallEtaleTopology.over (U i))
              (ModuleCat.{u + 1} B)).obj M)) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i : 𝒰.I₀,
      ∃ E : CochainComplex (ModuleCat.{u + 1} B) ℤ,
        (∀ n : ℤ, Module.Finite B (E.X n)) ∧
        (∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) ∧ Nonempty
          ((upperStar (ModuleCat.{u + 1} B) (𝒰.f i)).mapDerivedCategory.obj K ≅
            DerivedCategory.Q.obj
              (((constantSheaf (𝒰.X i).smallEtaleTopology
                (ModuleCat.{u + 1} B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E))  := by
  classical
  let e : X.Etale ≌ AsSmall.{u + 1} X.Etale := AsSmall.equiv
  let J := e.inverse.inducedTopology X.smallEtaleTopology
  let S := e.sheafCongr X.smallEtaleTopology J (ModuleCat.{u + 1} B)
  have : S.functor.Additive := Functor.additive_of_preserves_binary_products _
  let K' := S.functor.mapDerivedCategory.obj K
  let T := e.functor.obj (Scheme.Etale.mk (𝟙 X))
  have hT : IsTerminal T := (Scheme.Etale.isTerminalMkId X).isTerminalObj e.functor
  let P := J.toPrecoverage
  have hP : P.toGrothendieck = J := by
    apply le_antisymm J.toGrothendieck_toPrecoverage_le
    intro V R hR
    simpa only [Sieve.generate_sieve] using
      Precoverage.generate_mem_toGrothendieck ((J.arrows_mem_toPrecoverage_iff R).mpr hR)
  have site := exists_site_bounded_constant_model P T hT B
  rw [hP] at site
  have hvan' (q : ℤ) (hq : q < a ∨ b < q) : IsZero
      ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{u + 1} B)) q).obj K') :=
    (S.functor.map_isZero (hvan q hq)).of_iso
      ((S.functor.mapDerivedCategoryHomologyFunctorIso q).app K).symm
  have hloc' : ∀ (q : ℤ) (V : AsSmall.{u + 1} X.Etale),
      ∃ (I : Type (u + 1)) (U : I → AsSmall.{u + 1} X.Etale) (f : ∀ i, U i ⟶ V),
        Sieve.ofArrows U f ∈ J V ∧
        ∀ i, ∃ M : ModuleCat.{u + 1} B, Module.Finite B M ∧ Nonempty
          (((DerivedCategory.homologyFunctor
            (Sheaf J (ModuleCat.{u + 1} B)) q).obj K').over (U i) ≅
            (constantSheaf (J.over (U i)) (ModuleCat.{u + 1} B)).obj M) := by
    intro q V
    rcases V with ⟨V⟩
    obtain ⟨I, U, f, hf, hM⟩ := hloc q V
    refine ⟨I, fun i ↦ e.functor.obj (U i), fun i ↦ e.functor.map (f i), ?_, ?_⟩
    · rw [← Sieve.functorPushforward_ofArrows]
      exact (e.functor.functorPushforward_mem_iff X.smallEtaleTopology J).mpr hf
    · intro i
      obtain ⟨M, hM, ⟨hi⟩⟩ := hM i
      let ei := Over.postEquiv (X := U i) e
      have : ei.functor.IsCocontinuous (X.smallEtaleTopology.over (U i))
          (J.over (e.functor.obj (U i))) := by
        change (Over.post (X := U i) e.functor).IsCocontinuous _ _
        infer_instance
      have : ei.inverse.IsCocontinuous (J.over (e.functor.obj (U i)))
          (X.smallEtaleTopology.over (U i)) := by
        change (Over.post (X := e.functor.obj (U i)) e.inverse ⋙
          Over.map (e.unitIso.inv.app (U i))).IsCocontinuous _ _
        have : (Over.map (e.unitIso.inv.app (U i))).IsCocontinuous
            (X.smallEtaleTopology.over (e.inverse.obj (e.functor.obj (U i))))
            (X.smallEtaleTopology.over (U i)) := by
          constructor
          intro A R hR
          change Sieve.overEquiv A (R.functorPullback _) ∈ X.smallEtaleTopology A.left
          rw [Sieve.overEquiv_functorPullback_map]
          exact hR
        exact isCocontinuous_comp _ _
          (J.over (e.functor.obj (U i)))
          (X.smallEtaleTopology.over (e.inverse.obj (e.functor.obj (U i))))
      have : ei.inverse.IsDenseSubsite (J.over (e.functor.obj (U i)))
          (X.smallEtaleTopology.over (U i)) :=
        ei.isDenseSubsite_inverse_of_isCocontinuous _ _
      let Si := ei.sheafCongr (X.smallEtaleTopology.over (U i))
        (J.over (e.functor.obj (U i))) (ModuleCat.{u + 1} B)
      refine ⟨M, hM, ⟨?_⟩⟩
      let H := (DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) q).obj K
      have hr : (S.functor.obj H).over (e.functor.obj (U i)) ≅
          Si.functor.obj (H.over (U i)) := Iso.refl _
      exact (J.overPullback (ModuleCat.{u + 1} B) (e.functor.obj (U i))).mapIso
          ((S.functor.mapDerivedCategoryHomologyFunctorIso q).app K).symm ≪≫
        hr ≪≫ Si.functor.mapIso hi ≪≫
        (ei.constantSheafSheafCongrIso (X.smallEtaleTopology.over (U i))
          (J.over (e.functor.obj (U i))) (ModuleCat.{u + 1} B)
          CategoryTheory.Over.mkIdTerminal).app M
  obtain ⟨I, U, f, hf, hM⟩ := site K' a b hab hvan' hloc'
  let V (i : I) := e.inverse.obj (U i)
  let g (i : I) : V i ⟶ Scheme.Etale.mk (𝟙 X) := e.inverse.map (f i)
  have hc : Sieve.ofArrows V g ∈ X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X)) := by
    have hf' : Sieve.ofArrows U f ∈ J T := hf
    change Sieve.ofArrows (fun i ↦ e.inverse.obj (U i))
      (fun i ↦ e.inverse.map (f i)) ∈ X.smallEtaleTopology (e.inverse.obj T)
    rw [← Sieve.functorPushforward_ofArrows]
    exact (e.inverse.functorPushforward_mem_iff J X.smallEtaleTopology).mpr hf'
  have hs : ∀ x : X, ∃ i : I, ∃ y : (V i).left, (g i).left y = x := by
    have hr := (ofArrows_mem_smallEtaleTopology_iff (f := g)).mp hc
    intro x
    have hx : x ∈ ⋃ i, Set.range (g i).left := hr.symm ▸ Set.mem_univ x
    simpa only [Set.mem_iUnion, Set.mem_range] using hx
  choose index point hpoint using hs
  let 𝒰 : Cover.{u} etalePrecoverage X :=
    Cover.mkOfCovers X (fun x ↦ (V (index x)).left)
      (fun x ↦ (V (index x)).hom)
      (fun x ↦ ⟨x, point x, by
        have hw : (g (index x)).left = (V (index x)).hom := by
          have hh := MorphismProperty.Over.w (g (index x))
          change (g (index x)).left ≫ 𝟙 X = (V (index x)).hom at hh
          exact (Category.comp_id _).symm.trans hh
        exact (congrArg (fun q : (V (index x)).left ⟶ X ↦ q (point x)) hw).symm.trans
          (hpoint x)⟩)
      (fun _ ↦ inferInstance)
  refine ⟨𝒰, fun x ↦ ?_⟩
  obtain ⟨E, hfinite, hsupport, ⟨hmodel⟩⟩ := hM (index x)
  refine ⟨E, hfinite, hsupport, ⟨?_⟩⟩
  let W := V (index x)
  let ei := Over.postEquiv (X := W) e
  have : ei.functor.IsCocontinuous (X.smallEtaleTopology.over W)
      (J.over (e.functor.obj W)) := by
    change (Over.post (X := W) e.functor).IsCocontinuous _ _
    infer_instance
  have : ei.inverse.IsCocontinuous (J.over (e.functor.obj W))
      (X.smallEtaleTopology.over W) := by
    change (Over.post (X := e.functor.obj W) e.inverse ⋙
      Over.map (e.unitIso.inv.app W)).IsCocontinuous _ _
    have : (Over.map (e.unitIso.inv.app W)).IsCocontinuous
        (X.smallEtaleTopology.over (e.inverse.obj (e.functor.obj W)))
        (X.smallEtaleTopology.over W) := by
      constructor
      intro A R hR
      change Sieve.overEquiv A (R.functorPullback _) ∈ X.smallEtaleTopology A.left
      rw [Sieve.overEquiv_functorPullback_map]
      exact hR
    exact isCocontinuous_comp _ _ (J.over (e.functor.obj W))
      (X.smallEtaleTopology.over (e.inverse.obj (e.functor.obj W)))
  have : ei.inverse.IsDenseSubsite (J.over (e.functor.obj W))
      (X.smallEtaleTopology.over W) := ei.isDenseSubsite_inverse_of_isCocontinuous _ _
  let Si := ei.sheafCongr (X.smallEtaleTopology.over W)
    (J.over (e.functor.obj W)) (ModuleCat.{u + 1} B)
  let F := X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) W
  let F' := J.overPullback (ModuleCat.{u + 1} B) (e.functor.obj W)
  have : Si.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : F.Additive := Functor.additive_of_preserves_binary_products _
  have : F'.Additive := Functor.additive_of_preserves_binary_products _
  let hr : F ⋙ Si.functor ≅ S.functor ⋙ F' :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  let c := ei.constantSheafSheafCongrIso (X.smallEtaleTopology.over W)
    (J.over (e.functor.obj W)) (ModuleCat.{u + 1} B) CategoryTheory.Over.mkIdTerminal
  have he : Si.functor.mapDerivedCategory.obj (F.mapDerivedCategory.obj K) ≅
      Si.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj
        (((constantSheaf (X.smallEtaleTopology.over W)
          (ModuleCat.{u + 1} B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)) :=
    ((Functor.mapDerivedCategoryCompIso F Si.functor).app K).symm ≪≫
      (Functor.mapDerivedCategoryNatIso hr).app K ≪≫
      (Functor.mapDerivedCategoryCompIso S.functor F').app K ≪≫ hmodel ≪≫
      (DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso c
        (ComplexShape.up ℤ)).app E)).symm ≪≫
      (Si.functor.mapDerivedCategoryFactors.app _).symm
  let emodel := Si.functor.mapDerivedCategory.preimageIso he
  let Z := Scheme.Etale.overSheafEquiv W (ModuleCat.{u + 1} B)
  have : Z.functor.Additive := Functor.additive_of_preserves_binary_products _
  let hz := (Functor.mapDerivedCategoryNatIso (overRestrictionIso B W)).app K
  let cz : constantSheaf (X.smallEtaleTopology.over W) (ModuleCat.{u + 1} B) ⋙
      Z.functor ≅ constantSheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} B) :=
    (Scheme.Etale.overEquiv W).constantSheafSheafCongrIso
    (X.smallEtaleTopology.over W) W.left.smallEtaleTopology (ModuleCat.{u + 1} B)
    CategoryTheory.Over.mkIdTerminal
  exact hz.symm ≪≫ (Functor.mapDerivedCategoryCompIso F Z.functor).app K ≪≫
    Z.functor.mapDerivedCategory.mapIso emodel ≪≫
    Z.functor.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso cz
      (ComplexShape.up ℤ)).app E)


private noncomputable def constantValuePullbackIso
    {Y : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : Y.Etale) (M : ModuleCat.{u + 1} Λ)
    (e : F.over U ≅
      (constantSheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)).obj M) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom).obj F ≅
      (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M :=
  (overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} Λ) U F).symm ≪≫
    (Scheme.Etale.overSheafEquiv U (ModuleCat.{u + 1} Λ)).functor.mapIso e ≪≫
    ((Scheme.Etale.overEquiv U).constantSheafSheafCongrIso
      (Y.smallEtaleTopology.over U) U.left.smallEtaleTopology
      (ModuleCat.{u + 1} Λ) CategoryTheory.Over.mkIdTerminal).app M

private noncomputable def constantValueStalkIso
    {Y : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : Y.Etale) (M : ModuleCat.{u + 1} Λ)
    (e : F.over U ≅
      (constantSheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)).obj M)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U.left) :
    ((pointSmallEtale (s ≫ U.hom)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj F ≅ M := by
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  exact ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) U.hom s).app F).symm ≪≫
    (pointSmallEtale s).sheafFiber.mapIso (constantValuePullbackIso F U M e) ≪≫
    (pointSmallEtale s).sheafFiberConstantSheafIso M

private theorem local_fg_module_models
    (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hloc : IsLocallyConstantSheaf F)
    (hfin : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      Module.Finite R (((pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} R)).obj F))
    (V : X.Etale) :
    ∃ (I : Type (u + 1)) (U : I → X.Etale) (f : ∀ i, U i ⟶ V),
      Sieve.ofArrows U f ∈ X.smallEtaleTopology V ∧
      ∀ i, ∃ M : ModuleCat.{u + 1} R, Module.Finite R M ∧ Nonempty
        (F.over (U i) ≅
          (constantSheaf (X.smallEtaleTopology.over (U i)) (ModuleCat.{u + 1} R)).obj M) := by
  classical
  have := hloc
  let G := (upperStar (ModuleCat.{u + 1} R) V.hom).obj F
  have hG : IsLocallyConstantSheaf G := IsLocallyConstantSheaf.upperStar V.hom F
  obtain ⟨d₀⟩ := hG.nonempty_locallyConstantDatum
  let 𝒰 : Cover.{u} etalePrecoverage V.left :=
    { I₀ := { i : d₀.cover.I₀ // Nonempty (d₀.cover.X i) }
      X i := d₀.cover.X i.1
      f i := d₀.cover.f i.1
      mem₀ := by
        refine (presieve₀_mem_precoverage_iff _).mpr
          ⟨fun y ↦ ?_, fun i ↦ d₀.cover.map_prop i.1⟩
        obtain ⟨i, x, hx⟩ := d₀.cover.exists_eq y
        exact ⟨⟨i, ⟨x⟩⟩, x, hx⟩ }
  let U (i : 𝒰.I₀) : X.Etale := Scheme.Etale.mk (𝒰.f i ≫ V.hom)
  let f (i : 𝒰.I₀) : U i ⟶ V := MorphismProperty.Over.homMk (𝒰.f i) rfl
  refine ⟨ULift.{u + 1} 𝒰.I₀, fun i ↦ U i.down, fun i ↦ f i.down, ?_, ?_⟩
  · rw [ofArrows_mem_smallEtaleTopology_iff]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    exact ⟨⟨i⟩, y, hy⟩
  · intro i
    have := d₀.isConstant i.down.1
    obtain ⟨M, ⟨e⟩⟩ :=
      (G.over (𝒰.etalePrecoverageToEtale i.down)).mem_essImage_of_isConstant
    let z : 𝒰.X i.down := Classical.choice i.down.2
    let Ω := AlgebraicClosure ((𝒰.X i.down).residueField z)
    let t : Spec (.of Ω) ⟶ 𝒰.X i.down := (𝒰.X i.down).algClosurePoint z
    let eM : ((pointSmallEtale (t ≫ 𝒰.f i.down)).sheafFiber
        (A := ModuleCat.{u + 1} R)).obj G ≅ M :=
      constantValueStalkIso G (𝒰.etalePrecoverageToEtale i.down) M e.symm t
    let eF : ((pointSmallEtale ((t ≫ 𝒰.f i.down) ≫ V.hom)).sheafFiber
        (A := ModuleCat.{u + 1} R)).obj F ≅ M :=
      ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) V.hom
        (t ≫ 𝒰.f i.down)).app F).symm ≪≫ eM
    have hM : Module.Finite R M :=
      Module.Finite.equiv eF.toLinearEquiv
    refine ⟨M, hM, ⟨?_⟩⟩
    let S := Scheme.Etale.overSheafEquiv (U i.down) (ModuleCat.{u + 1} R)
    apply S.fullyFaithfulFunctor.preimageIso
    exact overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} R) (U i.down) F ≪≫
      (upperStarComp (ModuleCat.{u + 1} R) (𝒰.f i.down) V.hom).app F ≪≫
      constantValuePullbackIso G (𝒰.etalePrecoverageToEtale i.down) M e.symm ≪≫
      (((Scheme.Etale.overEquiv (U i.down)).constantSheafSheafCongrIso
        (X.smallEtaleTopology.over (U i.down)) (U i.down).left.smallEtaleTopology
        (ModuleCat.{u + 1} R) CategoryTheory.Over.mkIdTerminal).app M).symm

private noncomputable def constantDerivedFiberIso
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (E : DerivedCategory (ModuleCat.{u + 1} B)) :
    ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
      ((pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} B))
      (Functor.additive_of_preserves_binary_products _) _ _).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj E)) ≅
      E := by
  let F := (pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} B)
  have : F.Additive := Functor.additive_of_preserves_binary_products _
  let c := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)
  have : F ⋙ 𝟭 (ModuleCat.{u + 1} B) = F := rfl
  have hc : c ⋙ F ≅ 𝟭 (ModuleCat.{u + 1} B) :=
    (pointSmallEtale x).constantSheafCompSheafFiberIso _ _
  exact ((Functor.mapDerivedCategoryCompIso c F).app E).symm ≪≫
    (Functor.mapDerivedCategoryNatIso hc).app E ≪≫
    (Functor.mapDerivedCategoryIdIso (ModuleCat.{u + 1} B)).app E

private noncomputable def localModelFiberIso
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (U : Scheme.{u}) (f : U ⟶ X)
    (E : DerivedCategory (ModuleCat.{u + 1} B))
    (e : (upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory.obj K ≅
      (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj E)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ U) :
    ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
      ((pointSmallEtale (x ≫ f)).sheafFiber (A := ModuleCat.{u + 1} B))
      (Functor.additive_of_preserves_binary_products _) _ _).obj K) ≅ E := by
  let F := (pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} B)
  have : F.Additive := Functor.additive_of_preserves_binary_products _
  let G := (pointSmallEtale (x ≫ f)).sheafFiber
    (A := ModuleCat.{u + 1} B)
  have : G.Additive := Functor.additive_of_preserves_binary_products _
  exact ((Functor.mapDerivedCategoryNatIso
    (upperStarCompSheafFiberIso (ModuleCat.{u + 1} B) f x)).app K).symm ≪≫
    (Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} B) f) F).app K ≪≫
    F.mapDerivedCategory.mapIso e ≪≫ constantDerivedFiberIso U B x E

private theorem models_iso_on_overlap
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (𝒰 : Cover.{u} etalePrecoverage X)
    (E : 𝒰.I₀ → DerivedCategory (ModuleCat.{u + 1} B))
    (e : ∀ i, (upperStar (ModuleCat.{u + 1} B) (𝒰.f i)).mapDerivedCategory.obj K ≅
      (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj
        (E i))
    (i j : 𝒰.I₀) (y : 𝒰.X i) (z : 𝒰.X j) (h : 𝒰.f i y = 𝒰.f j z) :
    Nonempty (E i ≅ E j) := by
  let x := 𝒰.f i y
  let Ω := AlgebraicClosure (X.residueField x)
  let s : Spec (.of Ω) ⟶ X := X.algClosurePoint x
  have hx : s default = x := X.algClosurePoint_base x default
  obtain ⟨si, hsi, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f i) s y hx.symm
  obtain ⟨sj, hsj, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f j) s z (hx.trans h).symm
  have ei := localModelFiberIso X B K (𝒰.X i) (𝒰.f i) (E i) (e i) si
  have ej := localModelFiberIso X B K (𝒰.X j) (𝒰.f j) (E j) (e j) sj
  rw [hsi] at ei
  rw [hsj] at ej
  exact ⟨ei.symm ≪≫ ej⟩
private theorem connected_models
    (X : Scheme.{u}) [ConnectedSpace X] (B : Type (u + 1)) [CommRing B]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (𝒰 : Cover.{u} etalePrecoverage X)
    (E : 𝒰.I₀ → DerivedCategory (ModuleCat.{u + 1} B))
    (e : ∀ i, (upperStar (ModuleCat.{u + 1} B) (𝒰.f i)).mapDerivedCategory.obj K ≅
      (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj
        (E i))
    (E₀ : DerivedCategory (ModuleCat.{u + 1} B))
    (hne : ∃ i, Nonempty (𝒰.X i) ∧ Nonempty (E i ≅ E₀)) :
    ∀ i, Nonempty (𝒰.X i) → Nonempty (E i ≅ E₀) := by
  classical
  let O : Set X := ⋃ i, ⋃ (_ : Nonempty (E i ≅ E₀)), Set.range (𝒰.f i)
  have hopen : IsOpen O := isOpen_iUnion fun i ↦
    isOpen_iUnion fun _ ↦ (𝒰.f i).isOpenMap.isOpen_range
  have hc : Oᶜ = ⋃ i, ⋃ (_ : ¬ Nonempty (E i ≅ E₀)), Set.range (𝒰.f i) := by
    ext x
    simp only [Set.mem_compl_iff, O, Set.mem_iUnion, Set.mem_range]
    constructor
    · intro hx
      obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
      refine ⟨i, ?_, y, hy⟩
      intro hi
      exact hx ⟨i, hi, y, hy⟩
    · rintro ⟨i, hi, y, hy⟩ ⟨j, hj, z, hz⟩
      obtain ⟨eij⟩ := models_iso_on_overlap X B K 𝒰 E e i j y z (hy.trans hz.symm)
      exact hi ⟨eij ≪≫ hj.some⟩
  have hcompl : IsOpen Oᶜ := by
    rw [hc]
    exact isOpen_iUnion fun i ↦ isOpen_iUnion fun _ ↦ (𝒰.f i).isOpenMap.isOpen_range
  have hnonempty : O.Nonempty := by
    obtain ⟨i, ⟨y⟩, hi⟩ := hne
    exact ⟨𝒰.f i y, Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, ⟨y, rfl⟩⟩⟩⟩
  have hall : O = Set.univ :=
    (show IsClopen O from ⟨isOpen_compl_iff.mp hcompl, hopen⟩).eq_univ hnonempty
  intro i ⟨y⟩
  have hy : 𝒰.f i y ∈ O := hall.symm ▸ Set.mem_univ _
  have hy' : ∃ j, ∃ (_ : Nonempty (E j ≅ E₀)), ∃ z, 𝒰.f j z = 𝒰.f i y := by
    simpa only [O, Set.mem_iUnion, Set.mem_range] using hy
  obtain ⟨j, hj, z, hz⟩ := hy'
  obtain ⟨eij⟩ := models_iso_on_overlap X B K 𝒰 E e i j y z hz.symm
  exact ⟨eij ≪≫ hj.some⟩

private theorem connected_model_from_fiber
    (X : Scheme.{u}) [ConnectedSpace X] (B : Type (u + 1)) [CommRing B]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (𝒰 : Cover.{u} etalePrecoverage X)
    (E : 𝒰.I₀ → DerivedCategory (ModuleCat.{u + 1} B))
    (e : ∀ i, (upperStar (ModuleCat.{u + 1} B) (𝒰.f i)).mapDerivedCategory.obj K ≅
      (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj
        (E i))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ∃ 𝒱 : Cover.{u} etalePrecoverage X, ∀ i : 𝒱.I₀, Nonempty
      ((upperStar (ModuleCat.{u + 1} B) (𝒱.f i)).mapDerivedCategory.obj K ≅
        (constantSheaf (𝒱.X i).smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj
          ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
            ((pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} B))
            (Functor.additive_of_preserves_binary_products _) _ _).obj K)) := by
  classical
  let E₀ := (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
    ((pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} B))
    (Functor.additive_of_preserves_binary_products _) _ _).obj K
  obtain ⟨j, y, hy⟩ := 𝒰.exists_eq (x default)
  obtain ⟨t, ht, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f j) x y hy
  have ej := localModelFiberIso X B K (𝒰.X j) (𝒰.f j) (E j) (e j) t
  rw [ht] at ej
  have hmodels : ∀ i, Nonempty (𝒰.X i) → Nonempty (E i ≅ E₀) :=
    connected_models X B K 𝒰 E e E₀ ⟨j, ⟨y⟩, ⟨ej.symm⟩⟩
  let 𝒱 : Cover.{u} etalePrecoverage X :=
    { I₀ := { i : 𝒰.I₀ // Nonempty (𝒰.X i) }
      X i := 𝒰.X i.1
      f i := 𝒰.f i.1
      mem₀ := by
        refine (presieve₀_mem_precoverage_iff _).mpr
          ⟨fun z ↦ ?_, fun i ↦ 𝒰.map_prop i.1⟩
        obtain ⟨i, w, hw⟩ := 𝒰.exists_eq z
        exact ⟨⟨i, ⟨w⟩⟩, w, hw⟩ }
  refine ⟨𝒱, fun i ↦ ⟨?_⟩⟩
  exact e i.1 ≪≫
    (constantSheaf (𝒰.X i.1).smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.mapIso
      (hmodels i.1 i.2).some


private theorem connected_lisse_constant_models
    (R : Type (u + 1)) [CommRing R] [IsNoetherianRing R]
    (X : Scheme.{u}) [ConnectedSpace X]
    (L : _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (hbounded : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) q).obj L))
    (hlisse : ∀ q : ℤ,
      IsLocallyConstantSheaf
        ((_root_.DerivedCategory.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) q).obj L) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
        Module.Finite R
          (((pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} R)).obj
            ((_root_.DerivedCategory.homologyFunctor
              (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) q).obj L)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ∃ (𝒰 : Cover.{u} etalePrecoverage X),
      (∀ i : 𝒰.I₀, Nonempty
        ((upperStar (ModuleCat.{u + 1} R) (𝒰.f i)).mapDerivedCategory.obj L ≅
          (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} R)).mapDerivedCategory.obj
            ((geometricStalk R x).obj L))) ∧
      (∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω'] (y : Spec (.of Ω') ⟶ X),
        Nonempty ((geometricStalk R x).obj L ≅ (geometricStalk R y).obj L)) := by
  classical
  obtain ⟨a, b, hvan⟩ := hbounded
  have hvan' (q : ℤ) (hq : q < min a b ∨ b < q) : IsZero
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) q).obj L) :=
    hvan q (hq.imp (fun h ↦ lt_of_lt_of_le h (min_le_left _ _)) id)
  obtain ⟨𝒰, h𝒰⟩ := noetherian_bounded_constant_models X R L (min a b) b
    (min_le_right _ _) hvan'
    (fun q V ↦ local_fg_module_models X R _ (hlisse q).1 (hlisse q).2 V)
  choose M hfinite hsupport emodel using h𝒰
  let E (i : 𝒰.I₀) := _root_.DerivedCategory.Q.obj (M i)
  have e (i : 𝒰.I₀) :
      (upperStar (ModuleCat.{u + 1} R) (𝒰.f i)).mapDerivedCategory.obj L ≅
        (constantSheaf (𝒰.X i).smallEtaleTopology
          (ModuleCat.{u + 1} R)).mapDerivedCategory.obj (E i) :=
    (emodel i).some ≪≫
      ((constantSheaf (𝒰.X i).smallEtaleTopology
        (ModuleCat.{u + 1} R)).mapDerivedCategoryFactors.app (M i)).symm
  obtain ⟨𝒱, h𝒱⟩ := connected_model_from_fiber X R L 𝒰 E e Ω x
  refine ⟨𝒱, h𝒱, ?_⟩
  intro Ω' _ _ y
  obtain ⟨i, z, hz⟩ := 𝒱.exists_eq (y default)
  obtain ⟨t, ht, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒱.f i) y z hz
  have ey := localModelFiberIso X R L (𝒱.X i) (𝒱.f i)
    ((geometricStalk R x).obj L) (h𝒱 i).some t
  rw [ht] at ey
  exact ⟨ey.symm⟩

/-- A connected étale complex with finite locally constant cohomology and finite Tor
amplitude is locally a constant perfect ring complex, with the same geometric stalk.

Source: Stacks Project, `etale-cohomology.tex`, Tag 09BI, lemma-connected-ctf-locally-constant;
the weakly contractible clause is the trivialization in `proetale.tex`, Tag 09C6,
using `sites.tex`, Tag 090K (blueprint: lem-sfb-connected-etale-perfect-constant).

Proof. Apply the bounded constant-model theorem to the given bounded complex.
Exact geometric stalks identify local models whose images intersect. Since etale maps
are open, the union of images for each model is clopen; connectedness gives one model,
which can be taken to be the derived stalk at a chosen geometric point. The Noetherian
cohomology criterion makes this stalk pseudo-coherent. Testing the Tor hypothesis on
constant degree-zero modules and using the derived tensor/stalk comparison gives finite
Tor amplitude, hence perfectness. The same local models identify every geometric stalk.
For an affine weakly contractible pro-etale object, pull the cover back, take a finite
affine refinement and its disjoint coproduct, assemble the models on its clopen components,
and pull back along the section provided by weak contractibility. This also covers empty
or disconnected weakly contractible objects.
-/
theorem connected_etale_perfect_constant
    (R : Type (u + 1)) [CommRing R] [IsNoetherianRing R]
    (X : Scheme.{u}) [Nonempty X] [ConnectedSpace X]
    (L : _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (hbounded : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) q).obj L))
    (hlisse : ∀ q : ℤ,
      IsLocallyConstantSheaf
        ((DerivedCategory.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) q).obj L) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (x : Spec (.of Ω) ⟶ X),
        Module.Finite R
          (((pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} R)).obj
            ((DerivedCategory.homologyFunctor
              (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) q).obj L)))
    (hTor : ∃ a b : ℤ, a ≤ b ∧ ∀
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (q : ℤ),
      q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) q).obj
        (((derivedTensor (ModuleCat.{u + 1} R) X).obj L).obj
          ((DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) 0).obj F)))) :
    ∃ (E : _root_.DerivedCategory (ModuleCat.{u + 1} R)),
      DerivedCategory.IsPerfectRingComplex E ∧
      ∃ (𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage X),
        (∀ i : 𝒰.I₀,
          Nonempty
            ((Etale.upperStar (ModuleCat.{u + 1} R) (𝒰.f i)).mapDerivedCategory.obj L ≅
              ((constantSheaf (𝒰.X i).smallEtaleTopology
                (ModuleCat.{u + 1} R)).mapDerivedCategory.obj E))) ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (x : Spec (.of Ω) ⟶ X),
          Nonempty (E ≅ ((geometricStalk R x).obj L))) ∧
        (∀ (W : X.ProEt) [IsAffine W.left],
          (hW : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W) →
          Nonempty
            (((ProEtale.upperStar (ModuleCat.{u + 1} R) W.hom).mapDerivedCategory.obj
              ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.obj L)) ≅
              ((constantSheaf (Scheme.ProEt.topology W.left)
                (ModuleCat.{u + 1} R)).mapDerivedCategory.obj E)))
    := by
  classical
  let z : X := Classical.arbitrary X
  let Ω := AlgebraicClosure (X.residueField z)
  let x : Spec (.of Ω) ⟶ X := X.algClosurePoint z
  let F := (pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} R)
  have : F.Additive := (pointSmallEtale x).sheafFiber_additive
  let E := (geometricStalk R x).obj L
  have hpc : _root_.DerivedCategory.IsPseudoCoherent E := by
    have hcrit :=
      _root_.DerivedCategory.isPseudoCoherent_iff_boundedAbove_finite_homology.{u+1,u+1,u+1}
        R E
    apply hcrit.2
    constructor
    · obtain ⟨a, b, hb⟩ := hbounded
      refine ⟨b, fun q hq ↦ ?_⟩
      exact (F.map_isZero (hb q (Or.inr hq))).of_iso
        ((F.mapDerivedCategoryHomologyFunctorIso q).app L).symm
    · intro q
      let H := (_root_.DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) q).obj L
      let H' := (_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) q).obj E
      let e : F.obj H ≅ H' := (F.mapDerivedCategoryHomologyFunctorIso q).app L
      have hf : Module.Finite R (F.obj H) := (hlisse q).2 Ω x
      exact ⟨Submodule.fg_of_linearEquiv e.toLinearEquiv.symm hf.fg_top⟩
  obtain ⟨a, b, hab, hTor⟩ := hTor
  have ht : _root_.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} R) a b E := by
    intro N
    have hzero (q : ℤ) (hq : q < a ∨ b < q) : IsZero
        ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) q).obj
          (MonoidalCategory.tensorObj E
            ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} R) 0).obj N))) := by
      have h := hTor ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj N) q hq
      have hs := (F.map_isZero h).of_iso
        ((F.mapDerivedCategoryHomologyFunctorIso q).app _).symm
      exact hs.of_iso
        ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) q).mapIso
          (geometricStalk_tensor_constant_single R x L N).some).symm
    exact ⟨(_root_.DerivedCategory.isGE_iff _ a).2 (fun q hq ↦ hzero q (Or.inl hq)),
      (_root_.DerivedCategory.isLE_iff _ b).2 (fun q hq ↦ hzero q (Or.inr hq))⟩
  have hperfect : _root_.DerivedCategory.IsPerfectRingComplex E := by
    obtain ⟨P, ⟨c, d, hsupport⟩, hfin, hproj, ⟨e⟩⟩ :=
      _root_.DerivedCategory.isPerfect_of_pseudoCoherent_finiteTorAmplitude E hpc
        ⟨a, b, hab, ht⟩
    refine ⟨P, c, d, ?_, ?_, fun n ↦ ⟨hproj n, hfin n⟩, ⟨e.symm⟩⟩
    · exact (P.isStrictlyGE_iff c).2 (fun n hn ↦ hsupport n (Or.inl hn))
    · exact (P.isStrictlyLE_iff d).2 (fun n hn ↦ hsupport n (Or.inr hn))
  obtain ⟨𝒰, hlocal, hstalk⟩ := connected_lisse_constant_models R X L hbounded hlisse x
  refine ⟨E, hperfect, 𝒰, hlocal, hstalk, ?_⟩
  intro W _ hW
  exact etale_constant_models_on_weaklyContractible R X L E 𝒰 hlocal W hW

end AlgebraicGeometry.Etale
