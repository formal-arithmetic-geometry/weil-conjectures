/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.Paper.OrdinaryImmersionChartModels
import all Sheaf.Paper.CompletedCoefficientRingedCoherence
import Sheaf.Paper.OrdinaryCompletedPullbackExact
import all Sheaf.Paper.OrdinaryCompletedChartComparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! Ordinary immersion and chart comparisons by exact localization.
Source: Stacks Tags 0D6D and 04IF.
(blueprint: lem-tw-ordinary-immersion-chart-comparison). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.SubterminalImageCalculus.smallSheafify
attribute [-instance] CategoryTheory.SubterminalImageCalculus.smallLocalCriterion

universe t u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OrdinaryImmersionChart

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local semireducible] Rings

private abbrev commPush {T W : Scheme.{t}} (g : T ⟶ W) :=
  (proEtaleBaseChange g).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
    (ProEt.topology W) (ProEt.topology T)

private def commDirect {T W : Scheme.{t}} (g : T ⟶ W) :=
  ((completedRingAdj.{t, u} g).homEquiv _ _) (completedRingMap l E g)

private theorem commDirect_comp {T W Z : Scheme.{t}} (h : T ⟶ W) (k : W ⟶ Z) :
    commDirect l E k ≫ (commPush.{t, u} k).map (commDirect l E h) ≫
      (completedDirectComp.{t, u} h k).hom.app
        (completedIntegralCommRingSheafUnrestricted l E T) = commDirect l E (h ≫ k) := by
  symm
  let a := completedRingAdj.{t, u} (h ≫ k)
  let b := (completedRingAdj.{t, u} k).comp (completedRingAdj.{t, u} h)
  change a.homEquiv _ _ (completedRingMap l E (h ≫ k)) = _
  rw [(completedRingMap_comp l E h k).1]
  change a.homEquiv _ _
    (((conjugateIsoEquiv a b).symm (completedDirectComp.{t, u} h k).symm).inv.app _ ≫
      _) = _
  rw [completed_mate, Adjunction.comp_homEquiv]
  change (completedRingAdj.{t, u} k).homEquiv _ _
    ((completedRingAdj.{t, u} h).homEquiv _ _
      ((completedRingPull.{t, u} h).map (completedRingMap l E k) ≫
        completedRingMap l E h)) ≫ _ = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  rfl

@[irreducible]
private def pushComp {T W Z : Scheme.{t}} (h : T ⟶ W) (k : W ⟶ Z) :
    push l E h ⋙ push l E k ≅ push l E (h ≫ k) := by
  letI := Functor.isContinuous_comp (proEtaleBaseChange k) (proEtaleBaseChange h)
    (ProEt.topology Z) (ProEt.topology W) (ProEt.topology T)
  refine SheafOfModules.pushforwardComp (directRingMap l E k) (directRingMap l E h) ≪≫ ?_
  apply SheafOfModules.pushforwardCongr₂
    (e := (MorphismProperty.Over.pullbackComp
      (P := @WeaklyEtale) (Q := ⊤) h k))
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext H
  exact congrArg (fun a ↦ (forget₂ CommRingCat RingCat).map (a.hom.app H))
    (commDirect_comp l E h k)

private theorem pushComp_hom_sections {T W Z : Scheme.{t}} (h : T ⟶ W) (k : W ⟶ Z)
    (N : Modules l E T) (H : Z.ProEt)
    (m : ((push l E h ⋙ push l E k).obj N).val.obj (op H)) :
    ((pushComp l E h k).hom.app N).val.app (op H) m =
      N.val.map ((MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) h k).hom.app H).op m := by
  unfold pushComp
  simp only [Iso.trans_hom, NatTrans.comp_app, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    SheafOfModules.pushforwardCongr₂, SheafOfModules.pushforwardNatIso_hom,
    SheafOfModules.pushforwardComp_hom_app_val_app,
    SheafOfModules.pushforwardCongr_hom_app_val_app,
    SheafOfModules.pushforwardNatTrans_app_val_app_apply]

private theorem pushComp_inv_sections {T W Z : Scheme.{t}} (h : T ⟶ W) (k : W ⟶ Z)
    (N : Modules l E T) (H : Z.ProEt)
    (m : ((push l E (h ≫ k)).obj N).val.obj (op H)) :
    ((pushComp l E h k).inv.app N).val.app (op H) m =
      N.val.map ((MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) h k).inv.app H).op m := by
  unfold pushComp
  simp only [Iso.trans_inv, NatTrans.comp_app, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    SheafOfModules.pushforwardCongr₂, SheafOfModules.pushforwardNatIso_inv,
    SheafOfModules.pushforwardComp_inv_app_val_app,
    SheafOfModules.pushforwardCongr_inv_app_val_app,
    SheafOfModules.pushforwardCongr_hom_app_val_app,
    SheafOfModules.pushforwardNatTrans_app_val_app_apply]


@[irreducible]
private def pushEq {T Z : Scheme.{t}} {h k : T ⟶ Z} (e : h = k) :
    push l E k ≅ push l E h := by
  apply SheafOfModules.pushforwardCongr₂
    (e := eqToIso (congrArg (fun g : T ⟶ Z ↦ proEtaleBaseChange g) e))
  subst k
  apply Sheaf.hom_ext
  ext H x
  simp
  rfl

private theorem pushEq_sections {T Z : Scheme.{t}} {h k : T ⟶ Z} (e : h = k)
    (N : Modules l E T) (H : Z.ProEt)
    (m : ((push l E k).obj N).val.obj (op H)) :
    ((pushEq l E e).hom.app N).val.app (op H) m =
      N.val.map ((eqToIso (congrArg (fun g : T ⟶ Z ↦ proEtaleBaseChange g) e)).hom.app H).op
        m := by
  unfold pushEq
  simp only [SheafOfModules.pushforwardCongr₂, Iso.trans_hom, NatTrans.comp_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    SheafOfModules.pushforwardCongr_hom_app_val_app,
    SheafOfModules.pushforwardNatIso_hom,
    SheafOfModules.pushforwardNatTrans_app_val_app_apply]

attribute [local irreducible] Rings directRingMap completedIntegralCommRingSheafUnrestricted
attribute [local implicit_reducible] MorphismProperty Scheme.ProEt
  Scheme.instCategoryProEt CategoryTheory.Category.opposite Quiver.opposite
  CategoryTheory.CategoryStruct.opposite

private theorem squareSiteIso_hom {A B C D : Scheme.{t}} (a : A ⟶ B) (b : B ⟶ D)
    (c : A ⟶ C) (d : C ⟶ D) (e : a ≫ b = c ≫ d) :
    (squareSiteIso a b c d e).hom =
      (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) a b).inv ≫
        (eqToIso (congrArg (fun g : A ⟶ D ↦ proEtaleBaseChange g) e)).hom ≫
          (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) c d).hom := rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem squareAbMap {A B C D : Scheme.{t}} (a : A ⟶ B) (b : B ⟶ D)
    (c : A ⟶ C) (d : C ⟶ D) (e : a ≫ b = c ≫ d)
    (N : A.ProEtᵒᵖ ⥤ Ab.{max u (t + 1)}) (H : D.ProEt) :
    N.map ((MorphismProperty.Over.pullbackComp
      (P := @WeaklyEtale) (Q := ⊤) c d).hom.app H).op ≫
      N.map ((eqToIso (congrArg (fun g : A ⟶ D ↦ proEtaleBaseChange g) e)).hom.app H).op ≫
        N.map ((MorphismProperty.Over.pullbackComp
          (P := @WeaklyEtale) (Q := ⊤) a b).inv.app H).op =
      N.map ((squareSiteIso a b c d e).hom.app H).op := by
  rw [squareSiteIso_hom]
  change _ = N.map (_ ≫ _ ≫ _).op
  erw [op_comp, op_comp, N.map_comp, N.map_comp]
  exact (Category.assoc (obj := Ab.{max u (t + 1)}) _ _ _).symm

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem squareAbApply {A B C D : Scheme.{t}} (a : A ⟶ B) (b : B ⟶ D)
    (c : A ⟶ C) (d : C ⟶ D) (e : a ≫ b = c ≫ d)
    (N : A.ProEtᵒᵖ ⥤ Ab.{max u (t + 1)}) (H : D.ProEt)
    (x : N.obj (op ((proEtaleBaseChange c).obj ((proEtaleBaseChange d).obj H)))) :
    N.map ((MorphismProperty.Over.pullbackComp
      (P := @WeaklyEtale) (Q := ⊤) a b).inv.app H).op
      (N.map ((eqToIso (congrArg (fun g : A ⟶ D ↦ proEtaleBaseChange g) e)).hom.app H).op
        (N.map ((MorphismProperty.Over.pullbackComp
          (P := @WeaklyEtale) (Q := ⊤) c d).hom.app H).op x)) =
      N.map ((squareSiteIso a b c d e).hom.app H).op x := by
  exact CategoryTheory.congr_fun (squareAbMap a b c d e N H) x

private theorem isoTriple_sections {A C : Type*} [Category A] [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat}
    {F₀ F₁ F₂ F₃ : A ⥤ SheafOfModules R}
    (a : F₀ ≅ F₁) (b : F₁ ≅ F₂) (c : F₂ ≅ F₃) (N : A) (H : Cᵒᵖ)
    (m : (F₀.obj N).val.obj H) :
    (((a ≪≫ b ≪≫ c).hom.app N).val.app H) m =
      (c.hom.app N).val.app H ((b.hom.app N).val.app H ((a.hom.app N).val.app H m)) := rfl

private theorem isoTriple_sections_eq {A C : Type*} [Category A] [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat}
    {F₀ F₁ F₂ F₃ : A ⥤ SheafOfModules R}
    (a : F₀ ≅ F₁) (b : F₁ ≅ F₂) (c : F₂ ≅ F₃) (N : A) (H : Cᵒᵖ)
    (a' : (F₀.obj N).val.obj H → (F₁.obj N).val.obj H)
    (b' : (F₁.obj N).val.obj H → (F₂.obj N).val.obj H)
    (c' : (F₂.obj N).val.obj H → (F₃.obj N).val.obj H)
    (z : (F₀.obj N).val.obj H → (F₃.obj N).val.obj H)
    (ha : ∀ x, (a.hom.app N).val.app H x = a' x)
    (hb : ∀ x, (b.hom.app N).val.app H x = b' x)
    (hc : ∀ x, (c.hom.app N).val.app H x = c' x)
    (hz : ∀ x, c' (b' (a' x)) = z x) (m : (F₀.obj N).val.obj H) :
    (((a ≪≫ b ≪≫ c).hom.app N).val.app H) m = z m := by
  rw [isoTriple_sections, hc, hb, ha, hz]

@[irreducible]
private def squareDirect {A B C D : Scheme.{t}} (a : A ⟶ B) (b : B ⟶ D)
    (c : A ⟶ C) (d : C ⟶ D) (e : a ≫ b = c ≫ d) :
    push l E c ⋙ push l E d ≅ push l E a ⋙ push l E b :=
  pushComp l E c d ≪≫ (pushEq l E e) ≪≫
    (pushComp l E a b).symm

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem squareDirect_sections {A B C D : Scheme.{t}} (a : A ⟶ B) (b : B ⟶ D)
    (c : A ⟶ C) (d : C ⟶ D) (e : a ≫ b = c ≫ d)
    (N : Modules l E A) (H : D.ProEt)
    (m : ((push l E c ⋙ push l E d).obj N).val.obj (op H)) :
    ((squareDirect l E a b c d e).hom.app N).val.app (op H) m =
      N.val.map ((squareSiteIso a b c d e).hom.app H).op m := by
  unfold squareDirect
  exact isoTriple_sections_eq (pushComp l E c d)
    (pushEq l E e) (pushComp l E a b).symm N (op H)
    _ _ _ _ (pushComp_hom_sections l E c d N H) (pushEq_sections l E e N H)
    (pushComp_inv_sections l E a b N H) (squareAbApply a b c d e N.val.presheaf H) m

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
@[irreducible]
private def squareModel {A B C D : Scheme.{t}} (a : A ⟶ B) (b : B ⟶ D)
    (c : A ⟶ C) (d : C ⟶ D) (e : a ≫ b = c ≫ d) : Square l E a b c d e where
  direct := squareDirect l E a b c d e
  sections := squareDirect_sections l E a b c d e
  ordinary := (conjugateIsoEquiv ((adj l E d).comp (adj l E c))
    ((adj l E b).comp (adj l E a))).symm (squareDirect l E a b c d e)
  mate := Equiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private instance pullColimits {T W : Scheme.{t}} (g : T ⟶ W) :
    PreservesFiniteColimits (pull l E g) := by
  have : PreservesColimitsOfSize.{0, 0} (pull l E g) :=
    (adj l E g).leftAdjoint_preservesColimits
  infer_instance

private def exactImage {T W : Scheme.{t}} (g : T ⟶ W)
    [PreservesFiniteLimits (pull l E g)] [PreservesFiniteColimits (pull l E g)] :
    Image l E g where
  functor := (pull l E g).mapDerivedCategory
  counit := (pull l E g).mapDerivedCategoryFactors.hom
  universal := Functor.isLeftDerivedFunctor_of_inverts _ _ _
  computes := fun _ _ ↦ inferInstance

section ExactSquare
universe a av b bv c cv d dv w
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{w} B]
  {C : Type c} [Category.{cv} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type d} [Category.{dv} D] [Abelian D] [HasDerivedCategory.{w} D]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [I.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]

@[irreducible]
private def derivedSquare (e : F ⋙ G ≅ H ⋙ I) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ I.mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso e

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exactSquareNormalization (e : F ⋙ G ≅ H ⋙ I)
    (P : CochainComplex A ℤ) :
    (derivedSquare F G H I e).hom.app (DerivedCategory.Q.obj P) ≫
        I.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app P) ≫
          I.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj P) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) := by
  unfold derivedSquare
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  erw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac,
    ← Functor.mapDerivedCategoryCompIso_hom_app_factors F G]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rfl
end ExactSquare

/-- Ordinary derived pullback commutes with immersion restriction and then with a
representable pro-etale chart, for all ordinary unbounded complexes.

Source: Stacks sites-cohomology.tex, Tag 0D6D, lemma-derived-pullback-composition;
sites-modules.tex, Tag 04IF, lemma-localize-morphism-ringed-topoi;
Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-tw-ordinary-immersion-chart-comparison).

Proof:
1. Standard coefficient quotients are finite. Profinite coefficient inverse image
makes each projection-defined c_g invertible. Completed coefficient ringed coherence
identifies its composition and slice structural maps, including every finite projection.
2. The base change of i is an immersion. Ringed-topos derived pullback supplies
ordinary K-flat models. Exact immersion restriction identifies Pi and Pj with the
ordinary restrictions on every complex. Apply the ordinary derived composition
comparisons to jf = if_S. Their ordinary direct-image mate is squareSiteIso;
localization on flat-term K-flat representatives gives immersion.normalization.
3. Base change sends U to V. Subcanonicity and site-representable-algebraic-pullback
identify the inverse image of h_U with h_V, with adjunct identity at id_U.
Localized-sheaves-over-representable identifies the element sites with the two
represented slice sites. Representable-slice-localized-ringed-morphism and completed
ringed coherence identify the slice morphism, including its structural map, with v.
On sections its direct-image comparison is completedRingSlicePointIso.
4. Sheaf-slice-derived-comparison gives chart.comparison; its ordinary mate is the
unit/direct-comparison/counit composite in Chart.mate. Exact restriction preserves
flat-term K-flat representatives, giving Chart.normalization. Restrict the first
comparison and follow it by the inverse slice comparison. This is Comparison.formula.
All maps are natural; neither completion nor geometric finiteness is used. -/
theorem ordinaryImmersionChartComparison {X Y S : Scheme.{t}}
    (f : X ⟶ Y) (i : S ⟶ Y) [IsImmersion i] (U : S.ProEt) :
    Nonempty (Comparison l E f i U) := by
  have := ordinaryCompletedPullbackExact l E f
  have := ordinaryCompletedPullbackExact l E i
  have := ordinaryCompletedPullbackExact l E (pullback.fst f i)
  have := ordinaryCompletedPullbackExact l E (pullback.snd f i)
  have := ordinaryCompletedPullbackExact l E
    (completedRingSliceArrow (pullback.snd f i) U)
  let Pf := exactImage l E f
  let Pi := exactImage l E i
  let Pj := exactImage l E (pullback.fst f i)
  let Ps := exactImage l E (pullback.snd f i)
  let Pv := exactImage l E (completedRingSliceArrow (pullback.snd f i) U)
  let sq := squareModel l E (pullback.fst f i) f (pullback.snd f i) i
    (pullback.condition (f := f) (g := i))
  let isq : ImmersionSquare l E f i Pf Pi Pj Ps := {
    iLimits := inferInstance
    iColimits := inferInstance
    jLimits := inferInstance
    jColimits := inferInstance
    iExact := fun Q ↦ by
      change IsIso ((pull l E i).mapDerivedCategoryFactors.hom.app Q)
      infer_instance
    jExact := fun Q ↦ by
      change IsIso ((pull l E (pullback.fst f i)).mapDerivedCategoryFactors.hom.app Q)
      infer_instance
    square := sq
    comparison := derivedSquare _ _ _ _ sq.ordinary
    normalization := fun Q _ ↦ exactSquareNormalization _ _ _ _ sq.ordinary Q }
  obtain ⟨o⟩ := ordinaryCompletedChartComparison l E (pullback.snd f i) U
  have hu := restrictExact l E U
  have hv := restrictExact l E ((proEtaleBaseChange (pullback.snd f i)).obj U)
  have := hu.1
  have := hu.2
  have := hv.1
  have := hv.2
  let ch : Chart l E (pullback.snd f i) U Ps Pv := {
    uLimits := hu.1
    uColimits := hu.2
    vLimits := hv.1
    vColimits := hv.2
    rU := ⟨(restrict l E U).mapDerivedCategory, (restrict l E U).mapDerivedCategoryFactors⟩
    rV := ⟨(restrict l E ((proEtaleBaseChange (pullback.snd f i)).obj U)).mapDerivedCategory,
      (restrict l E ((proEtaleBaseChange (pullback.snd f i)).obj U)).mapDerivedCategoryFactors⟩
    direct := o.direct
    sections := o.sections
    ordinary := o.ordinary
    mate := o.mate
    comparison := derivedSquare _ _ _ _ o.ordinary
    normalization := fun Q _ ↦ exactSquareNormalization _ _ _ _ o.ordinary Q }
  exact ⟨{
    Pf := Pf
    Pi := Pi
    Pj := Pj
    Ps := Ps
    Pv := Pv
    immersion := isq
    chart := ch
    comparison := isoWhiskerRight isq.comparison ch.rV.functor ≪≫
      Functor.associator Pi.functor Ps.functor ch.rV.functor ≪≫
        isoWhiskerLeft Pi.functor ch.comparison.symm ≪≫
          (Functor.associator Pi.functor ch.rU.functor Pv.functor).symm
    formula := rfl }⟩

end WeilConjectures.OrdinaryImmersionChart
