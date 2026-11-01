/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModulePullbackComposition
import all WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictOpenTensorCoordinates
import all WeilConjectures.AlgebraicGeometry.Geometry.SemilinearCoefficientPullbackComposition
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearNaturalIsoAssembly

/-! # Ordinary pullback compositors for strict geometric coordinates

Source: blueprint operations proof (2), constant-section inverse-image composition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
attribute [local implicit_reducible] WeilConjectures.SemilinearSections.evaluation
  SheafOfModules.pushforward PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj AlgebraicGeometry.Scheme.proEtaleRingModuleDirectImage
  AlgebraicGeometry.Scheme.proEtaleConstantRingComparison
attribute [local irreducible] WeilConjectures.SemilinearSections.transition
  WeilConjectures.SemilinearSections.coefficientMap
  WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf WeilConjectures.SemilinearSections.rings
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
  AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction
  AlgebraicGeometry.Scheme.proEtaleRingDirectImageMap
  AlgebraicGeometry.Scheme.proEtaleConstantRingComparison CategoryTheory.constantSheaf Padic
  Padic.coefficientExtensionIntegers
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option maxHeartbeats 2000000 in
-- Reducing the carriers here passes through two direct images and scalar restriction.
end AlgebraicGeometry.ProEtale.SpTowerShriek

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

/-- Evaluation of the ordinary compositor agrees with the inverse of the canonical
module compositor at every coefficient level, before passing to complexes.
Source: blueprint operations proof (2); Stacks 03D8.
(blueprint: lem-sp-strict-ordinary-compositor). -/
def StrictOrdinaryCompNormalized (b : Base l E)
    (geometry : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), Geometry l E b f)
    (ordinaryComp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      (geometry g).pull ⋙ (geometry f).pull ≅ (geometry (f ≫ g)).pull) : Prop :=
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (M : S l E Z),
    (ev l E X n).map ((ordinaryComp f g).hom.app M) ≫
        ((geometry (f ≫ g)).ordinaryPullEvaluation n).hom.app M =
      ((geometry f).ordinaryPullEvaluation n).hom.app ((geometry g).pull.obj M) ≫
        (proEtaleConstantRingPullback (R l E n) f).map
          (((geometry g).ordinaryPullEvaluation n).hom.app M) ≫
        (proEtaleConstantRingModulePullbackComposition f g (R l E n)).choose.inv.app
          ((ev l E Z n).obj M)

private def finitePushComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) :
    proEtaleConstantRingPushforward (R l E n) f ⋙
      proEtaleConstantRingPushforward (R l E n) g ≅
        proEtaleConstantRingPushforward (R l E n) (f ≫ g) :=
  (proEtaleConstantRingModulePullbackComposition f g (R l E n)).choose_spec.choose

private theorem finitePushComp_sections {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (N : proEtaleRingModules X (proEtaleConstantRing X (R l E n)))
    (U : Z.ProEt) (x : ((proEtaleConstantRingPushforward (R l E n) f ⋙
      proEtaleConstantRingPushforward (R l E n) g).obj N).val.obj (op U)) :
    ((finitePushComp l E f g n).hom.app N).val.app (op U) x =
      N.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app U).op x :=
  (proEtaleConstantRingModulePullbackComposition f g (R l E n)).choose_spec.choose_spec.1
    N U x

private def pushCompositeEvaluation (b : Base l E)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (gf : Geometry l E b f) (gg : Geometry l E b g) (n : ℕ) :
    (gf.push ⋙ gg.push) ⋙ ev l E Z n ≅
      ev l E X n ⋙ proEtaleConstantRingPushforward (R l E n) (f ≫ g) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft gf.push (gg.ordinaryPushEvaluation n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (gf.ordinaryPushEvaluation n)
      (proEtaleConstantRingPushforward (R l E n) g) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (ev l E X n) (finitePushComp l E f g n)

private theorem pushCompositeEvaluation_sections (b : Base l E)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (gf : Geometry l E b f) (gg : Geometry l E b g) (n : ℕ)
    (M : S l E X) (U : Z.ProEtᵒᵖ)
    (x : ((ev l E Z n).obj (gg.push.obj (gf.push.obj M))).val.obj U) :
    ((pushCompositeEvaluation l E b f g gf gg n).hom.app M).val.app U x =
      ((ev l E X n).obj M).val.map
        ((MorphismProperty.Over.pullbackComp f g).hom.app U.unop).op
        (((gf.ordinaryPushEvaluation n).hom.app M).val.app (chart g U)
          (((gg.ordinaryPushEvaluation n).hom.app (gf.push.obj M)).val.app U x)) := by
  simp only [pushCompositeEvaluation, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Iso.symm_hom, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp]
  change ((finitePushComp l E f g n).hom.app ((ev l E X n).obj M)).val.app U
    (((gf.ordinaryPushEvaluation n).hom.app M).val.app (chart g U)
      (((gg.ordinaryPushEvaluation n).hom.app (gf.push.obj M)).val.app U x)) = _
  exact finitePushComp_sections l E f g n _ U.unop _

private theorem restricted_naturality
    {C : Type*} [Category C] [EssentiallySmall.{u + 1} C]
    {J : GrothendieckTopology C} {A B : Sheaf J CommRingCat.{u + 1}}
    (φ : A ⟶ B) (N : SemilinearSections.Mod J A) (M : SemilinearSections.Mod J B)
    (k : N ⟶ (SemilinearSections.res φ).obj M)
    {U V : Cᵒᵖ} (a : U ⟶ V) (x : N.val.obj U) :
    restrictedSection φ M V (k.val.app V (N.val.map a x)) =
      M.val.map a (restrictedSection φ M U (k.val.app U x)) := by
  exact PresheafOfModules.naturality_apply k.val a x

private theorem pushCompositeEvaluation_horizontal (b : Base l E)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (gf : Geometry l E b f) (gg : Geometry l E b g)
    (M : S l E X) {m n : ℕ} (h : n ≤ m) (U : Z.ProEtᵒᵖ)
    (x : ((ev l E Z m).obj (gg.push.obj (gf.push.obj M))).val.obj U) :
    pushSection (R l E n) (f ≫ g) ((ev l E X n).obj M) U
      (((pushCompositeEvaluation l E b f g gf gg n).hom.app M).val.app U
        (horizontalSection l E Z h (gg.push.obj (gf.push.obj M)) U x)) =
      horizontalSection l E X h M (chart (f ≫ g) U)
        (pushSection (R l E m) (f ≫ g) ((ev l E X m).obj M) U
          (((pushCompositeEvaluation l E b f g gf gg m).hom.app M).val.app U x)) := by
  have hg := push_horizontal l E g b gg (gf.push.obj M) h U x
  have hf := push_horizontal l E f b gf M h (chart g U)
    (pushSection (R l E m) g ((ev l E Y m).obj (gf.push.obj M)) U
      (((gg.ordinaryPushEvaluation m).hom.app (gf.push.obj M)).val.app U x))
  change ((gg.ordinaryPushEvaluation n).hom.app (gf.push.obj M)).val.app U
      (horizontalSection l E Z h (gg.push.obj (gf.push.obj M)) U x) =
    horizontalSection l E Y h (gf.push.obj M) (chart g U)
      (((gg.ordinaryPushEvaluation m).hom.app (gf.push.obj M)).val.app U x) at hg
  change ((gf.ordinaryPushEvaluation n).hom.app M).val.app (chart g U)
      (horizontalSection l E Y h (gf.push.obj M) (chart g U)
        (((gg.ordinaryPushEvaluation m).hom.app (gf.push.obj M)).val.app U x)) =
    horizontalSection l E X h M (chart f (chart g U))
      (((gf.ordinaryPushEvaluation m).hom.app M).val.app (chart g U)
        (((gg.ordinaryPushEvaluation m).hom.app (gf.push.obj M)).val.app U x)) at hf
  change ((pushCompositeEvaluation l E b f g gf gg n).hom.app M).val.app U
      (horizontalSection l E Z h (gg.push.obj (gf.push.obj M)) U x) = _
  refine (pushCompositeEvaluation_sections l E b f g gf gg n M U _).trans ?_
  refine (congrArg (fun y ↦ ((ev l E X n).obj M).val.map
      ((MorphismProperty.Over.pullbackComp f g).hom.app U.unop).op
      (((gf.ordinaryPushEvaluation n).hom.app M).val.app (chart g U) y)) hg).trans ?_
  refine (congrArg (fun y ↦ ((ev l E X n).obj M).val.map
      ((MorphismProperty.Over.pullbackComp f g).hom.app U.unop).op y) hf).trans ?_
  change _ = horizontalSection l E X h M (chart (f ≫ g) U)
    (((pushCompositeEvaluation l E b f g gf gg m).hom.app M).val.app U x)
  refine Eq.trans ?_ (congrArg (horizontalSection l E X h M (chart (f ≫ g) U))
    (pushCompositeEvaluation_sections l E b f g gf gg m M U x)).symm
  exact (restricted_naturality
    (SemilinearSections.coefficientMap (ProEt.topology X) (B l E X) (tau l E X) h)
    ((ev l E X m).obj M) ((ev l E X n).obj M) ((horizontal l E X h).app M)
    ((MorphismProperty.Over.pullbackComp f g).hom.app U.unop).op _).symm

private def pushCompLevel (b : Base l E)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (gf : Geometry l E b f) (gg : Geometry l E b g)
    (gc : Geometry l E b (f ≫ g)) (n : ℕ) :
    (gf.push ⋙ gg.push) ⋙ ev l E Z n ≅ gc.push ⋙ ev l E Z n :=
  pushCompositeEvaluation l E b f g gf gg n ≪≫ (gc.ordinaryPushEvaluation n).symm

private theorem pushCompLevel_horizontal (b : Base l E)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (gf : Geometry l E b f) (gg : Geometry l E b g)
    (gc : Geometry l E b (f ≫ g))
    (M : S l E X) {m n : ℕ} (h : n ≤ m) :
    (horizontal l E Z h).app ((gf.push ⋙ gg.push).obj M) ≫
        (restrict l E Z h).map ((pushCompLevel l E b f g gf gg gc n).hom.app M) =
      (pushCompLevel l E b f g gf gg gc m).hom.app M ≫
        (horizontal l E Z h).app (gc.push.obj M) := by
  have hd (k : ℕ) : (pushCompLevel l E b f g gf gg gc k).hom.app M ≫
      (gc.ordinaryPushEvaluation k).hom.app M =
        (pushCompositeEvaluation l E b f g gf gg k).hom.app M := by
    simp only [pushCompLevel, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  apply (cancel_mono ((restrict l E Z h).map
    ((gc.ordinaryPushEvaluation n).hom.app M))).mp
  rw [Category.assoc, ← Functor.map_comp, hd]
  ext U x
  have hc := push_horizontal l E (f ≫ g) b gc M h U
    (((pushCompLevel l E b f g gf gg gc m).hom.app M).val.app U x)
  have he := pushCompositeEvaluation_horizontal l E b f g gf gg M h U x
  have hm := congrArg (fun a ↦ a.val.app U x) (hd m)
  change ((gc.ordinaryPushEvaluation m).hom.app M).val.app U
      (((pushCompLevel l E b f g gf gg gc m).hom.app M).val.app U x) =
    ((pushCompositeEvaluation l E b f g gf gg m).hom.app M).val.app U x at hm
  rw [hm] at hc
  change ((pushCompositeEvaluation l E b f g gf gg n).hom.app M).val.app U
      (horizontalSection l E Z h (gg.push.obj (gf.push.obj M)) U x) =
    ((gc.ordinaryPushEvaluation n).hom.app M).val.app U
      (horizontalSection l E Z h (gc.push.obj M) U
        (((pushCompLevel l E b f g gf gg gc m).hom.app M).val.app U x))
  exact he.trans hc.symm

private theorem pushComp_exists (b : Base l E)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (gf : Geometry l E b f) (gg : Geometry l E b g)
    (gc : Geometry l E b (f ≫ g)) :
    ∃ d : gf.push ⋙ gg.push ≅ gc.push, ∀ M n,
      (ev l E Z n).map (d.hom.app M) ≫ (gc.ordinaryPushEvaluation n).hom.app M =
        (gg.ordinaryPushEvaluation n).hom.app (gf.push.obj M) ≫
          (proEtaleConstantRingPushforward (R l E n) g).map
            ((gf.ordinaryPushEvaluation n).hom.app M) ≫
          (finitePushComp l E f g n).hom.app ((ev l E X n).obj M) := by
  obtain ⟨d, hd⟩ := SemilinearSections.naturalIsoOfEvaluation_exists.{u, u, u + 2, u + 1}
    (ProEt.topology Z) (B l E Z) (tau l E Z) (gf.push ⋙ gg.push) gc.push
    (pushCompLevel l E b f g gf gg gc)
    (fun M _ _ h ↦ pushCompLevel_horizontal l E b f g gf gg gc M h)
  refine ⟨d, ?_⟩
  intro M n
  rw [hd]
  simp only [pushCompLevel, pushCompositeEvaluation, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Iso.symm_hom, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp,
    Category.comp_id, Category.assoc, Iso.inv_hom_id_app]

private theorem transpose_conjugate
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {Q Q' : D ⥤ C} (a : L ⊣ Q) (b : L' ⊣ Q')
    (e : L' ≅ L) (M : C) (N : D) (f : L'.obj M ⟶ N) :
    a.homEquiv _ _ (e.inv.app M ≫ f) =
      b.homEquiv _ _ f ≫ (conjugateIsoEquiv a b e).inv.app N := by
  have hu := unit_conjugateEquiv b a e.inv M
  change b.unit.app M ≫ (conjugateIsoEquiv a b e).inv.app (L'.obj M) =
    a.unit.app M ≫ Q.map (e.inv.app M) at hu
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [← hu]
  simpa only [Category.assoc] using congrArg (b.unit.app M ≫ ·)
    ((conjugateIsoEquiv a b e).inv.naturality f).symm

private theorem evaluation_transpose
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {Q : D ⥤ C} (a : L ⊣ Q)
    {L' : C' ⥤ D'} {Q' : D' ⥤ C'} (b : L' ⊣ Q')
    (V : C ⥤ C') (W : D ⥤ D')
    (p : L ⋙ W ≅ V ⋙ L') (q : Q ⋙ V ≅ W ⋙ Q')
    (hu : ∀ M, V.map (a.unit.app M) ≫ q.hom.app (L.obj M) ≫
      Q'.map (p.hom.app M) = b.unit.app (V.obj M)) (M : C) :
    b.homEquiv _ _ (p.inv.app M) = V.map (a.unit.app M) ≫ q.hom.app (L.obj M) := by
  apply (cancel_mono (Q'.map (p.hom.app M))).mp
  rw [Adjunction.homEquiv_unit, Category.assoc, ← Q'.map_comp, p.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  simpa only [Category.assoc] using (hu M).symm

/-- Ordinary composition, with its finite-level normalization, for the fixed geometry.
Source: blueprint operations proof (2); Zheng Construction 4.1 and Lemma 4.10;
Stacks 03D8 and 07A7. (blueprint: lem-sp-strict-ordinary-compositor).

Proof: identify each geometry's ordinary direct image with the sectionwise direct
image on the vertical ringed sequence site. Its ordinaryPushEvaluation_sections
identities give the component maps, and restrictions in the coefficient direction
are retained by the same identity comparisons. Restriction along fibre-product
pasting gives the direct-image compositor: its coefficient index is fixed, and
naturality of the constant-section structural ring maps proves linearity. Its
inverse uses inverse pasting. Form the inverse-image compositor by conjugating
this isomorphism through the three ordinaryAdjunctions. Evaluate their Hom
bijections at level n. The ordinary unit and counit evaluation identities show
that this evaluation is conjugation through the three specified finite
constant-ring adjunctions; levelAdjunction_eq transports these as dependent
packages. The evaluated direct-image map restricts along precisely the canonical
pasting map. Equality on all module sections identifies it with the direct-image
witness of proEtaleConstantRingModulePullbackComposition. Injectivity of
conjugateIsoEquiv identifies the left adjoints' compositor, proving the displayed
ordinary normalization. This argument works for n = 0, identity maps and empty
schemes and uses no exactness or flatness of quotient transition homomorphisms. -/
theorem strictOrdinaryComp (b : Base l E)
    (geometry : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), Geometry l E b f) :
    ∃ ordinaryComp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
        (geometry g).pull ⋙ (geometry f).pull ≅ (geometry (f ≫ g)).pull,
      StrictOrdinaryCompNormalized l E b geometry ordinaryComp := by
  classical
  let d {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
    (pushComp_exists l E b f g (geometry f) (geometry g) (geometry (f ≫ g))).choose
  let c {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
    ((conjugateIsoEquiv ((geometry g).ordinaryAdjunction.comp
      (geometry f).ordinaryAdjunction) (geometry (f ≫ g)).ordinaryAdjunction).symm
        (d f g)).symm
  refine ⟨@c, ?_⟩
  intro X Y Z f g n M
  apply mate_composition
    (geometry f).ordinaryAdjunction (geometry g).ordinaryAdjunction
    (geometry (f ≫ g)).ordinaryAdjunction
    (proEtaleConstantRingAdjunction (R l E n) f)
    (proEtaleConstantRingAdjunction (R l E n) g)
    (proEtaleConstantRingAdjunction (R l E n) (f ≫ g))
    (ev l E X n) (ev l E Y n) (ev l E Z n)
    (c f g) (proEtaleConstantRingModulePullbackComposition f g (R l E n)).choose.symm
    (d f g) (finitePushComp l E f g n)
    ((geometry f).ordinaryPullEvaluation n) ((geometry g).ordinaryPullEvaluation n)
    ((geometry (f ≫ g)).ordinaryPullEvaluation n)
    ((geometry f).ordinaryPushEvaluation n) ((geometry g).ordinaryPushEvaluation n)
    ((geometry (f ≫ g)).ordinaryPushEvaluation n)
  · intro P Q k
    have h := transpose_conjugate
      ((geometry g).ordinaryAdjunction.comp (geometry f).ordinaryAdjunction)
      (geometry (f ≫ g)).ordinaryAdjunction
      ((conjugateIsoEquiv ((geometry g).ordinaryAdjunction.comp
        (geometry f).ordinaryAdjunction) (geometry (f ≫ g)).ordinaryAdjunction).symm
          (d f g)) P Q k
    rw [Equiv.apply_symm_apply] at h
    rw [Adjunction.comp_homEquiv] at h
    exact h
  · intro P Q k
    have h := transpose_conjugate
      ((proEtaleConstantRingAdjunction (R l E n) g).comp
        (proEtaleConstantRingAdjunction (R l E n) f))
      (proEtaleConstantRingAdjunction (R l E n) (f ≫ g))
      (proEtaleConstantRingModulePullbackComposition f g (R l E n)).choose P Q k
    rw [(proEtaleConstantRingModulePullbackComposition f g
      (R l E n)).choose_spec.choose_spec.2] at h
    rw [Adjunction.comp_homEquiv] at h
    exact h
  · exact evaluation_transpose (geometry f).ordinaryAdjunction
      (proEtaleConstantRingAdjunction (R l E n) f) (ev l E Y n) (ev l E X n)
      ((geometry f).ordinaryPullEvaluation n) ((geometry f).ordinaryPushEvaluation n)
      (geometry_unit_evaluation l E b (geometry f) n)
  · exact evaluation_transpose (geometry g).ordinaryAdjunction
      (proEtaleConstantRingAdjunction (R l E n) g) (ev l E Z n) (ev l E Y n)
      ((geometry g).ordinaryPullEvaluation n) ((geometry g).ordinaryPushEvaluation n)
      (geometry_unit_evaluation l E b (geometry g) n)
  · exact evaluation_transpose (geometry (f ≫ g)).ordinaryAdjunction
      (proEtaleConstantRingAdjunction (R l E n) (f ≫ g)) (ev l E Z n) (ev l E X n)
      ((geometry (f ≫ g)).ordinaryPullEvaluation n)
      ((geometry (f ≫ g)).ordinaryPushEvaluation n)
      (geometry_unit_evaluation l E b (geometry (f ≫ g)) n)
  · intro Q
    exact (pushComp_exists l E b f g (geometry f) (geometry g)
      (geometry (f ≫ g))).choose_spec Q n

end AlgebraicGeometry.ProEtale.SpTowerShriek
