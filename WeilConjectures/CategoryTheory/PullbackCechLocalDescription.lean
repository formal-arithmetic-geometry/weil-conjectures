/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.CategoryTheory.GeneratingPullbackCharts
import WeilConjectures.CategoryTheory.CechModelPullbackOnChart
import WeilConjectures.CategoryTheory.AugmentedCechCoverCriterion
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.ProperBaseChange.RingedSliceExtensionTensorHomData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import Mathlib.CategoryTheory.Sites.LeftExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import Mathlib.Tactic.Convert

/-!
# Pullback of a local augmented extended Cech description

Source: Stacks Project, algebraization.tex, Tag 099E, together with
sites-modules.tex, Tags 03D7 and 03EL, and sites-cohomology.tex, Tags 06YY and 0G7E.
(blueprint: lem-weil-pbc-pullback-cech-local-description).
-/

@[expose] public section
set_option autoImplicit false

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option maxHeartbeats 800000 in
-- Explicit slice and derived-category comparison maps require substantial elaboration.
private theorem local_model_on_resolution
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{wY} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{wY} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O)
    (hK : HasLocalExtendedCechDescription O I ι K ε)
    (P : ringedSiteComplex O) (p : P ⟶ K) (hp : QuasiIso p)
    (U : C) (r : ℕ) (b : Fin r → O.obj.obj (Opposite.op U))
    (hb : IsRingedIdealGeneratingList O I ι U r b) :
    let R := SheafOfModules.overFunctor.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U
    let Rc := R.mapHomologicalComplex (.up ℤ)
    ∃ e : DerivedCategory.Q.obj
        (ringedExtendedCech (O.over U) r (fun i ↦ ringedSliceSection O U (b i))).1 ≅
          DerivedCategory.Q.obj (Rc.obj P),
      e.hom ≫ DerivedCategory.Q.map
        (Rc.map (p ≫ ε) ≫ (ringedRestrictionRingComplexIso O U).hom) =
          DerivedCategory.Q.map
            (ringedExtendedCech (O.over U) r (fun i ↦ ringedSliceSection O U (b i))).2 := by
  dsimp only
  let R : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) ⥤
      ringedSiteModules.{u}
        ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)) :=
    SheafOfModules.overFunctor.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U
  have : R.Additive := ringedOverFunctor_additive O U
  have : PreservesFiniteLimits R := ringedOverFunctor_preservesFiniteLimits O U
  have : PreservesFiniteColimits R := ringedOverFunctor_preservesFiniteColimits O U
  let Rc := R.mapHomologicalComplex (.up ℤ)
  have := hp
  have : QuasiIso (Rc.map p) := inferInstance
  have : IsIso (DerivedCategory.Q.map (Rc.map p)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  obtain ⟨e, he⟩ := hK U r b hb
  let β : DerivedCategory.Q ⋙ ringedDerivedRestriction O U ≅
      Rc ⋙ DerivedCategory.Q := R.mapDerivedCategoryFactors
  refine ⟨e ≪≫ β.app K ≪≫ (asIso (DerivedCategory.Q.map (Rc.map p))).symm, ?_⟩
  change (e.hom ≫ (β.app K).hom ≫ inv (DerivedCategory.Q.map (Rc.map p))) ≫ _ = _
  simp only [Functor.map_comp, Category.assoc]
  erw [IsIso.inv_hom_id_assoc]
  have hn := β.hom.naturality ε
  dsimp only [Functor.comp_map] at hn
  erw [← Category.assoc (β.app K).hom, ← hn]
  have hβring : (ringedDerivedRingRestrictionIso O U).hom =
      (β.app (ringedSiteRingComplex O)).hom ≫
        DerivedCategory.Q.map (ringedRestrictionRingComplexIso O U).hom := rfl
  erw [hβring] at he
  simp only [Category.assoc] at he ⊢
  convert! he using 1

set_option maxHeartbeats 800000 in
-- Check the naturality square through both presentations of each slice ring.
private theorem chart_augmentation_square
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RY : Sheaf J CommRingCat.{u}) (RX : Sheaf K CommRingCat.{u})
    (G : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⥤
      ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    [G.Additive]
    (u : G.obj (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ≅
      SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    (t : PullbackCechChart RY RX G u)
    (P : ringedSiteComplex RY) (ε : P ⟶ ringedSiteRingComplex RY) :
    let := t.additive
    let := ringedOverFunctor_additive RY t.V
    let := ringedOverFunctor_additive RX t.U
    let RYc := (SheafOfModules.overFunctor.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) t.V).mapHomologicalComplex
        (.up ℤ)
    let RXc := (SheafOfModules.overFunctor.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) t.U).mapHomologicalComplex
        (.up ℤ)
    let Fc := t.F.mapHomologicalComplex (.up ℤ)
    let Gc := G.mapHomologicalComplex (.up ℤ)
    let ψ := NatIso.mapHomologicalComplex t.comparison (.up ℤ)
    Fc.map (RYc.map ε ≫ (ringedRestrictionRingComplexIso RY t.V).hom) ≫
        (HomologicalComplex.singleMapHomologicalComplex t.F (.up ℤ) 0).hom.app
          (SheafOfModules.unit
            ((sheafCompose (J.over t.V) (forget₂ CommRingCat RingCat)).obj (RY.over t.V))) ≫
        (HomologicalComplex.single _ (.up ℤ) 0).map t.ringIso.hom =
      ψ.hom.app P ≫ RXc.map
        (Gc.map ε ≫
          (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app
            (SheafOfModules.unit
              ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ≫
          (HomologicalComplex.single _ (.up ℤ) 0).map u.hom) ≫
        (ringedRestrictionRingComplexIso RX t.U).hom := by
  let := t.additive
  let := ringedOverFunctor_additive RY t.V
  let := ringedOverFunctor_additive RX t.U
  dsimp only
  let ψ := NatIso.mapHomologicalComplex t.comparison (.up ℤ)
  have hring :
      (t.F.mapHomologicalComplex (.up ℤ)).map
          (ringedRestrictionRingComplexIso RY t.V).hom ≫
        (HomologicalComplex.singleMapHomologicalComplex t.F (.up ℤ) 0).hom.app
          (SheafOfModules.unit
            ((sheafCompose (J.over t.V) (forget₂ CommRingCat RingCat)).obj (RY.over t.V))) ≫
        (HomologicalComplex.single _ (.up ℤ) 0).map t.ringIso.hom =
      ψ.hom.app (ringedSiteRingComplex RY) ≫
        ((SheafOfModules.overFunctor.{u}
          ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)
            t.U).mapHomologicalComplex (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app
            (SheafOfModules.unit
              ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ≫
            (HomologicalComplex.single _ (.up ℤ) 0).map u.hom) ≫
        (ringedRestrictionRingComplexIso RX t.U).hom := by
    apply HomologicalComplex.to_single_hom_ext
    simp only [ringedRestrictionRingComplexIso, Functor.comp_obj, ringedOverRingIso,
      Functor.mapIso_refl, Iso.trans_refl, Iso.app_hom, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      eqToIso_refl, Iso.refl_hom, Functor.map_id, Iso.refl_inv, Category.id_comp,
      HomologicalComplex.single_map_f_self, ringedSiteRingComplex, Functor.map_comp,
      Category.assoc, NatIso.mapHomologicalComplex_hom_app_f, ψ]
    change t.F.map (𝟙 _) ≫ 𝟙 _ ≫ t.ringIso.hom ≫ 𝟙 _ =
      t.comparison.hom.app (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ≫
        (SheafOfModules.overFunctor.{u}
          ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) t.U).map (𝟙 _) ≫
        (SheafOfModules.overFunctor.{u}
          ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) t.U).map u.hom ≫
        (SheafOfModules.overFunctor.{u}
          ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) t.U).map (𝟙 _) ≫ 𝟙 _
    have ht := t.ring_compatibility
    change t.F.map (𝟙 _) ≫ t.ringIso.hom =
      t.comparison.hom.app (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ≫
        (SheafOfModules.overFunctor.{u}
          ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) t.U).map u.hom ≫ 𝟙 _ at ht
    simp only [Functor.map_id, Category.id_comp, Category.comp_id] at ht ⊢
    erw [Category.id_comp]
    exact ht
  simp only [Functor.map_comp, Category.assoc]
  erw [← ψ.hom.naturality_assoc ε]
  erw [hring]
  simp only [Functor.map_comp, Category.assoc]
  rfl

set_option maxHeartbeats 800000 in
-- Elaborating the slice and derived comparison maps requires additional heartbeats.
/-- The pulled-back flat resolution has every local augmented Cech model.

Source: Stacks Project, algebraization.tex, Tag 099E; sites-modules.tex, Tags 03D7 and 03EL;
sites-cohomology.tex, Tags 06YY and 0G7E.
(blueprint: lem-weil-pbc-pullback-cech-local-description).

The least-ideal hypothesis `hImage` is written out, so the statement records the
structural image condition rather than a stronger equality. `G` is any left adjoint of
`f.modules`, hence canonically the tensor pullback, and `u` its unit comparison.

Proof:
1. A finite ideal-generating cover of `IY`, refined by the sections of the inverse images
   of its associated representables, gives a small family of object-slice charts
   `h : X/U → Y/V` covering the source site. Each chart carries a module comparison
   `h^*(M|_V) ≅ (G M)|_U` normalized by `u`, a source list `b` generating
   `IY|_V` and a scalar-compatible list `c` generating `IX|_U`.
2. On a chart, restrict `p : P → KY` to `V`. Exact restriction preserves the
   quasi-isomorphism, K-flatness and termwise flatness. The supplied model `e` for `b`,
   the derived restriction comparison and the inverse of `Q(p|_V)` give an augmented model
   `Q C_b ≅ Q(P|_V)` for the augmentation `(p ; εY)|_V`; naturality proves its equation.
3. The augmented Cech pullback comparison on the chart transports this model through the
   chart's module pullback: `Q C_c ≅ Q(h^*(P|_V))`, with the pulled-back augmentation
   followed by the chart's rank-one comparison.
4. The chart comparison gives a chain isomorphism `h^*(P|_V) ≅ (G P)|_U`. Its ring
   compatibility is the augmentation square in degree zero; the other components of the
   ring target vanish. Composing with the derived restriction comparison for `RX` gives
   `Q C_c ≅ (Q A)|_U` carrying `δ|_U` to `ε_c`.
5. The charts cover the source site and their lists `c` generate `IX`. The augmented Cech
   cover criterion gives the required model on every source object and for every
   generating list `g`. -/
theorem pullback_cech_local_description
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RY : Sheaf J CommRingCat.{u}) (RX : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{wY} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))]
    [HasDerivedCategory.{wX} (ringedSiteModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))]
    [∀ U : C, HasDerivedCategory.{wY} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (RY.over U)))]
    [∀ U : D, HasDerivedCategory.{wX} (ringedSiteModules.{u}
      ((sheafCompose (K.over U) (forget₂ CommRingCat RingCat)).obj (RX.over U)))]
    (f : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (IY : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (ιY : IY ⟶ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    [Mono ιY] [IY.IsFiniteType]
    (IX : ringedSiteModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    (ιX : IX ⟶ SheafOfModules.unit
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    [Mono ιX] [IX.IsFiniteType]
    (hImage : ∀ (N : ringedSiteModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
      (j : N ⟶ SheafOfModules.unit
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)),
      Mono j →
      (∃ k : f.inverse.obj ((SheafOfModules.toSheaf
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⋙
          sheafCompose J (forget AddCommGrpCat)).obj IY) ⟶
          (SheafOfModules.toSheaf
            ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) ⋙
            sheafCompose K (forget AddCommGrpCat)).obj N,
        (k ≫ (SheafOfModules.toSheaf
            ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) ⋙
            sheafCompose K (forget AddCommGrpCat)).map j : _ ⟶
              (sheafCompose K (forget RingCat)).obj
                ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) =
          (f.inverse.map ((SheafOfModules.toSheaf
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⋙
            sheafCompose J (forget AddCommGrpCat)).map ιY) : _ ⟶
              f.inverse.obj ((sheafCompose J (forget RingCat)).obj
                ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))) ≫ f.ringMap) ↔
      ∃ a : IX ⟶ N, a ≫ j = ιX)
    (G : ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⥤
      ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    [G.PreservesZeroMorphisms]
    (hG : G ⊣ f.modules)
    (u : G.obj (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ≅
      SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    (KY : ringedSiteComplex RY) (εY : KY ⟶ ringedSiteRingComplex RY)
    (hεY : HasLocalExtendedCechDescription RY IY ιY KY εY)
    (P : ringedSiteComplex RY) (p : P ⟶ KY) (hp : QuasiIso p)
    (hP : P.IsKFlatIndependentCoefficients)
    (hPflat : ∀ n : ℤ, SheafOfModules.IsFlat (P.X n)) :
    let A := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
    let δ :=
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (p ≫ εY) ≫
        (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app
          (SheafOfModules.unit
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map u.hom
    HasLocalExtendedCechDescription RX IX ιX A δ := by
  classical
  let : G.Additive := hG.left_adjoint_additive
  dsimp only
  let Gc := G.mapHomologicalComplex (.up ℤ)
  let δ := Gc.map (p ≫ εY) ≫
    (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ≫
    (HomologicalComplex.single _ (.up ℤ) 0).map u.hom
  obtain ⟨B, t, hcover, hgen⟩ :=
    exists_generating_pullback_charts RY RX f IY ιY IX ιX hImage G hG u
  have hmodels : ∀ a : B, ∃ e : DerivedCategory.Q.obj
      (ringedExtendedCech (RX.over (t a).U) (t a).r
        (fun i ↦ ringedSliceSection RX (t a).U ((t a).c i))).1 ≅
        (ringedDerivedRestriction RX (t a).U).obj (DerivedCategory.Q.obj (Gc.obj P)),
      e.hom ≫ (ringedDerivedRestriction RX (t a).U).map (DerivedCategory.Q.map δ) ≫
        (ringedDerivedRingRestrictionIso RX (t a).U).hom =
          DerivedCategory.Q.map
            (ringedExtendedCech (RX.over (t a).U) (t a).r
              (fun i ↦ ringedSliceSection RX (t a).U ((t a).c i))).2 := by
    intro a
    let s := t a
    let := s.additive
    let := ringedOverFunctor_additive RY s.V
    let := ringedOverFunctor_additive RX s.U
    let R : ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⥤
        ringedSiteModules.{u}
          ((sheafCompose (J.over s.V) (forget₂ CommRingCat RingCat)).obj (RY.over s.V)) :=
      SheafOfModules.overFunctor.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) s.V
    let S : ringedSiteModules.{u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) ⥤
        ringedSiteModules.{u}
          ((sheafCompose (K.over s.U) (forget₂ CommRingCat RingCat)).obj (RX.over s.U)) :=
      SheafOfModules.overFunctor.{u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) s.U
    have : S.Additive := ringedOverFunctor_additive RX s.U
    have : PreservesFiniteLimits S := ringedOverFunctor_preservesFiniteLimits RX s.U
    have : PreservesFiniteColimits S := ringedOverFunctor_preservesFiniteColimits RX s.U
    let Rc := R.mapHomologicalComplex (.up ℤ)
    let ψ := NatIso.mapHomologicalComplex s.comparison (.up ℤ)
    let ε := Rc.map (p ≫ εY) ≫ (ringedRestrictionRingComplexIso RY s.V).hom
    obtain ⟨e, he⟩ := local_model_on_resolution RY IY ιY KY εY hεY P p hp
      s.V s.r s.b (hgen a).1
    have hPr : CochainComplex.IsKFlatIndependentCoefficients (R := RY.over s.V)
        (Rc.obj P) :=
      (SheafOfModules.ringedSite_restriction_exact_kflat J RY s.V).2.2 P hP
    have hPrflat : ∀ n : ℤ,
        SheafOfModules.IsFlat (R := RY.over s.V) ((Rc.obj P).X n) :=
      fun n ↦ SheafOfModules.isFlat_over (P.X n) s.V (hPflat n)
    obtain ⟨d, hd⟩ := cech_model_pullback_on_chart (RY.over s.V) (RX.over s.U)
      s.morphism s.F s.adjunction s.ringIso s.r
      (fun i ↦ ringedSliceSection RY s.V (s.b i))
      (fun i ↦ ringedSliceSection RX s.U (s.c i)) s.scalar_compatibility
      (Rc.obj P) ε hPr hPrflat e he
    let β : DerivedCategory.Q ⋙ ringedDerivedRestriction RX s.U ≅
        S.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := S.mapDerivedCategoryFactors
    refine ⟨d ≪≫ DerivedCategory.Q.mapIso (ψ.app P) ≪≫ (β.app (Gc.obj P)).symm, ?_⟩
    change (d.hom ≫ DerivedCategory.Q.map (ψ.hom.app P) ≫
      (β.app (Gc.obj P)).inv) ≫ _ ≫ _ = _
    have hn := β.hom.naturality δ
    dsimp only [Functor.comp_map] at hn
    have hβring : (ringedDerivedRingRestrictionIso RX s.U).hom =
        (β.app (ringedSiteRingComplex RX)).hom ≫
          DerivedCategory.Q.map (ringedRestrictionRingComplexIso RX s.U).hom := rfl
    erw [hβring]
    simp only [Category.assoc]
    erw [← Category.assoc ((ringedDerivedRestriction RX s.U).map
      (DerivedCategory.Q.map δ)) (β.app (ringedSiteRingComplex RX)).hom, hn]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_assoc]
    erw [← Functor.map_comp, ← Functor.map_comp]
    erw [← chart_augmentation_square RY RX G u s P (p ≫ εY)]
    exact hd
  choose e he using hmodels
  exact hasLocalExtendedCechDescription_of_cover RX IX ιX (Gc.obj P) δ B
    (fun a ↦ (t a).U)
    (fun V ↦ ⟨Sieve.ofObjects (fun a ↦ (t a).U) V, hcover V,
      fun W g hg ↦ hg⟩)
    (fun a ↦ (t a).r) (fun a ↦ (t a).c) (fun a ↦ (hgen a).2) e he


end CategoryTheory
