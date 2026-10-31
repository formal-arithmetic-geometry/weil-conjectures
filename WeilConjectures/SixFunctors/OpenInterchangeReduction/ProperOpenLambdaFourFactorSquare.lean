/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenInterchangeReduction.OpenInterchangeReductionData
import all WeilConjectures.SixFunctors.GeneratorReduction.GeneratorKind.TensorAdjunctionReductionSquares
import all WeilConjectures.SixFunctors.GeneratorReduction.OpenReconstructionEffectivity

/-! # Four-factor ordinary proper/open lambda square

This module isolates the component square for the prescribed four-factor
proper/open lambda.  The recursive word comparison is supplied by the caller.
(blueprint: lem-sf-proper-open-lambda-four-factor-square)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

universe u s
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneratorReduction

namespace WeilConjectures.OpenInterchangeReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The ordinary proper-image reduction mate used by the four-factor expansion. -/
def ordinaryPushReductionK5 (o : IntegralSystemRealization.Operations l E)
    (m : IntegralSystemRealization.RealizationModel l E o) {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    IntegralSystemRealization.ringedPush l E f ⋙
        (IntegralSystemRealization.calculus l E Y).reduction ⟶
      (IntegralSystemRealization.calculus l E X).reduction ⋙
        IntegralSystemRealization.Operations.push l E o f :=
  (mateEquiv (IntegralSystemRealization.ringedAdj l E f) (o.direct f).adj
    (m.reductionPull f).inv).natTrans

/-- The source map obtained by expanding the pull, proper, open three-factor
part of the ordinary comparison, with an arbitrary child comparison `f`. -/
def properOpenLambdaFourFactorSource
    {S : Type s} (W : S → Scheme.{u}) {a b c d : S}
    (o : Operations l E) (k : W a ⟶ W b) (r : W a ⟶ W c)
    (p : W b ⟶ W d) (j : W c ⟶ W d)
    (hk : IsOpenImmersion k) (hki : QuasiCompact k)
    (hjo : IsOpenImmersion j) (hji : QuasiCompact j)
    (hr : IsProper r) (hp : IsProper p)
    (M : DerivedCategory (scalarReductionSource l E (W a)))
    (N : coefficientSequenceDerived l E (W a))
    (f : (IntegralSystemRealization.calculus l E (W a)).reduction.obj M ⟶ N) :
    (IntegralSystemRealization.calculus l E (W c)).reduction.obj
        ((IntegralSystemRealization.ringedPull l E j).obj
          ((IntegralSystemRealization.ringedPush l E p).obj
            ((IntegralSystemRealization.ringedOpen l E k).obj M))) ⟶
      (IntegralSystemRealization.pull l E j).obj
        ((IntegralSystemRealization.Operations.push l E o.system p).obj
          ((IntegralSystemRealization.Operations.shriek l E o.system k).obj N)) := by
  letI := hk
  letI := hki
  letI := hjo
  letI := hji
  letI := hr
  letI := hp
  exact
    (o.realization.reductionPull j).hom.app
        ((IntegralSystemRealization.ringedPush l E p).obj
          ((IntegralSystemRealization.ringedOpen l E k).obj M)) ≫
      (IntegralSystemRealization.pull l E j).map
        ((ordinaryPushReductionK5 l E o.system o.realization p).app
          ((IntegralSystemRealization.ringedOpen l E k).obj M)) ≫
      (IntegralSystemRealization.pull l E j).map
        ((IntegralSystemRealization.Operations.push l E o.system p).map
          (inverseOrZero ((o.realization.openReduction l E k).app M))) ≫
      (IntegralSystemRealization.pull l E j).map
        ((IntegralSystemRealization.Operations.push l E o.system p).map
          ((IntegralSystemRealization.Operations.shriek l E o.system k).map f))

/-- The target map obtained by expanding the ordinary proper factor, with an
arbitrary child comparison `f`. -/
def properOpenLambdaFourFactorTarget
    {S : Type s} (W : S → Scheme.{u}) {a c : S}
    (o : Operations l E) (r : W a ⟶ W c)
    (hr : IsProper r) (M : DerivedCategory (scalarReductionSource l E (W a)))
    (N : coefficientSequenceDerived l E (W a))
    (f : (IntegralSystemRealization.calculus l E (W a)).reduction.obj M ⟶ N) :
    (IntegralSystemRealization.calculus l E (W c)).reduction.obj
        ((IntegralSystemRealization.ringedPush l E r).obj M) ⟶
      (IntegralSystemRealization.Operations.push l E o.system r).obj N := by
  letI := hr
  exact (ordinaryPushReductionK5 l E o.system o.realization r).app M ≫
    (IntegralSystemRealization.Operations.push l E o.system r).map f

-- The older ambient-model calculation only uses these five pieces of data.
-- Keeping this interface private avoids assuming its unrelated reconstruction fields.
namespace FourFactorProof
open IntegralSystemRealization CategoryTheory.Limits Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [local implicit_reducible] TwoSquare
  SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  integralOperationsCommHasDerivedCategory
  PurCompactSupport.completed coefficientSequenceHasDerived scalarReductionSourceDerived
  integralTowerHasDerivedCategory integralCompletedRingHasDerivedCategory
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory pullbackTensorCalculus
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  proEtaleCanonicalTensorComparison ringedPullComp
  ringedRestrictFactor restrictFactor properOpenLambda ringedProperOpenLambda
  ringedOpenComp Compositors.openComp openCongr ringedOpenCongr

private def ordinaryPushReduction (o : IntegralSystemRealization.Operations l E)
    (m : RealizationModel l E o) {U V : Scheme.{u}} (f : U ⟶ V) :=
  ordinaryPushReductionK5 l E o m f

private theorem inverse_square {C D : Type*} [Category C] [Category D]
    (R : C ⥤ D) {K H : C} {M N : D} (r : K ≅ H) (s : M ≅ N)
    (q : R.obj K ⟶ M) (t : R.obj H ⟶ N)
    (h : q ≫ s.hom = R.map r.hom ≫ t) :
    t ≫ s.inv = R.map r.inv ≫ q := by
  apply (cancel_epi (R.map r.hom)).1
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [← R.map_comp_assoc, Iso.hom_inv_id, R.map_id, Category.id_comp]

private theorem inverse_mate_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {P : A ⥤ B} {Q : B ⥤ A} {F : C ⥤ D} {G : D ⥤ C}
    {R : A ⥤ C} {T : B ⥤ D} (a : P ⊣ Q) (b : F ⊣ G)
    (δ : Q ⋙ R ⟶ T ⋙ G) {X : A} {Y : B} {M : C} {N : D}
    [IsIso (((mateEquiv a b).symm δ).natTrans.app X)]
    (q : R.obj X ⟶ M) (t : T.obj Y ⟶ N)
    (α : P.obj X ⟶ Y) (β : F.obj M ⟶ N)
    (h : q ≫ (b.homEquiv _ _) β =
      R.map ((a.homEquiv _ _) α) ≫ δ.app Y ≫ G.map t) :
    inv (((mateEquiv a b).symm δ).natTrans.app X) ≫ F.map q ≫ β = T.map α ≫ t := by
  apply (cancel_epi (((mateEquiv a b).symm δ).natTrans.app X)).1
  simp only [IsIso.hom_inv_id_assoc]
  apply (b.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  change q ≫ (b.homEquiv _ _) β =
    b.unit.app (R.obj X) ≫ G.map
      (((mateEquiv a b).symm δ).natTrans.app X ≫ T.map α ≫ t)
  rw [G.map_comp, G.map_comp]
  rw [← reassoc_of% (unit_mateEquiv_symm a b δ X)]
  have hn := δ.naturality α
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, ← R.map_comp_assoc]
  exact h

private theorem left_mate_compositor_square
    {A₀ A₁ A₂ N₀ N₁ N₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category N₀] [Category N₁] [Category N₂]
    {P : A₀ ⥤ A₁} {Q : A₁ ⥤ A₀} {P' : A₁ ⥤ A₂} {Q' : A₂ ⥤ A₁}
    {P'' : A₀ ⥤ A₂} {Q'' : A₂ ⥤ A₀}
    {F : N₀ ⥤ N₁} {G : N₁ ⥤ N₀} {F' : N₁ ⥤ N₂} {G' : N₂ ⥤ N₁}
    {F'' : N₀ ⥤ N₂} {G'' : N₂ ⥤ N₀}
    {R₀ : A₀ ⥤ N₀} {R₁ : A₁ ⥤ N₁} {R₂ : A₂ ⥤ N₂}
    (a : P ⊣ Q) (a' : P' ⊣ Q') (a'' : P'' ⊣ Q'')
    (b : F ⊣ G) (b' : F' ⊣ G') (b'' : F'' ⊣ G'')
    (χ : R₀ ⋙ F ⟶ P ⋙ R₁) (χ' : R₁ ⋙ F' ⟶ P' ⋙ R₂)
    (χ'' : R₀ ⋙ F'' ⟶ P'' ⋙ R₂)
    (α : P'' ⟶ P ⋙ P') (β : F'' ⟶ F ⋙ F')
    (h : ∀ X : A₂,
      (mateEquiv a b χ).natTrans.app (Q'.obj X) ≫
          G.map ((mateEquiv a' b' χ').natTrans.app X) ≫
          (conjugateEquiv (b.comp b') b'' β).app (R₂.obj X) =
        R₀.map ((conjugateEquiv (a.comp a') a'' α).app X) ≫
          (mateEquiv a'' b'' χ'').natTrans.app X) :
    (TwoSquare.vComp χ χ').whiskerRight β =
      (TwoSquare.mk _ _ _ _ χ'').whiskerLeft α := by
  apply (mateEquiv (a.comp a') b'').injective
  rw [mateEquiv_conjugateEquiv_vcomp (a.comp a') (b.comp b') b'',
    conjugateEquiv_mateEquiv_vcomp (a.comp a') a'' b'', mateEquiv_hcomp a b a' b']
  apply NatTrans.ext
  funext X
  simpa only [TwoSquare.hComp, TwoSquare.whiskerBottom, TwoSquare.whiskerTop,
    TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id, Functor.comp_obj, Category.assoc] using h X

private theorem pull_comp_inverse (o : IntegralSystemRealization.Operations l E)
    (m : RealizationModel l E o)
    (c : Compositors l E o) {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W)
    (L : Integral l E W) :
    (m.reductionPull f).hom.app ((ringedPull l E g).obj L) ≫
        (pull l E f).map ((m.reductionPull g).hom.app L) ≫
        (c.pullComp f g).inv.app ((calculus l E W).reduction.obj L) =
      (calculus l E U).reduction.map ((ringedPullComp l E f g).inv.app L) ≫
        (m.reductionPull (f ≫ g)).hom.app L := by
  apply (cancel_epi ((calculus l E U).reduction.map
    ((ringedPullComp l E f g).hom.app L))).1
  simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [reassoc_of% (GeneratorReduction.canonicalReductionPullComposition l E o m c f g L)]
  simp only [Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]

private theorem pull_congr_nat (o : IntegralSystemRealization.Operations l E)
    (m : RealizationModel l E o)
    {U V : Scheme.{u}} {f g : U ⟶ V} (w : f = g) :
    (m.reductionPull f).hom ≫ Functor.whiskerLeft (calculus l E V).reduction
        (eqToIso (congrArg (pull l E) w.symm)).inv =
      Functor.whiskerRight (eqToIso (congrArg (ringedPull l E) w.symm)).inv
        (calculus l E U).reduction ≫ (m.reductionPull g).hom := by
  subst g
  simp only [eqToIso_refl, Iso.refl_inv, Functor.whiskerLeft_id', Functor.whiskerRight_id',
    Category.comp_id, Category.id_comp]

private theorem paste_three {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {A₀ A₁ A₂ A₃ : C} {B₀ B₁ B₂ B₃ : D}
    (q₀ : R.obj A₀ ⟶ B₀) (q₁ : R.obj A₁ ⟶ B₁)
    (q₂ : R.obj A₂ ⟶ B₂) (q₃ : R.obj A₃ ⟶ B₃)
    (r₀ : A₀ ⟶ A₁) (r₁ : A₁ ⟶ A₂) (r₂ : A₂ ⟶ A₃)
    (s₀ : B₀ ⟶ B₁) (s₁ : B₁ ⟶ B₂) (s₂ : B₂ ⟶ B₃)
    (h₀ : q₀ ≫ s₀ = R.map r₀ ≫ q₁)
    (h₁ : q₁ ≫ s₁ = R.map r₁ ≫ q₂)
    (h₂ : q₂ ≫ s₂ = R.map r₂ ≫ q₃) :
    q₀ ≫ s₀ ≫ s₁ ≫ s₂ = R.map (r₀ ≫ r₁ ≫ r₂) ≫ q₃ := by
  rw [reassoc_of% h₀, reassoc_of% h₁, h₂]
  simp only [R.map_comp, Category.assoc]

private theorem paste_iso_square
    {C C' D : Type*} [Category C] [Category C'] [Category D]
    (R : C ⥤ D) (S : C' ⥤ D)
    {A₀ A₁ A₂ A₃ : C} {B₀ B₁ B₂ B₃ : C'}
    (q₀ : R.obj A₀ ⟶ S.obj B₀) (q₁ : R.obj A₁ ⟶ S.obj B₁)
    (q₂ : R.obj A₂ ⟶ S.obj B₂) (q₃ : R.obj A₃ ⟶ S.obj B₃)
    (r₀ : A₁ ≅ A₀) (r₁ : A₂ ≅ A₁) (r₂ : A₂ ≅ A₃)
    (s₀ : B₁ ≅ B₀) (s₁ : B₂ ≅ B₁) (s₂ : B₂ ≅ B₃)
    (h₀ : q₀ ≫ S.map s₀.inv = R.map r₀.inv ≫ q₁)
    (h₁ : q₁ ≫ S.map s₁.inv = R.map r₁.inv ≫ q₂)
    (h₂ : q₂ ≫ S.map s₂.hom = R.map r₂.hom ≫ q₃) :
    q₀ ≫ S.map (s₂.symm ≪≫ s₁ ≪≫ s₀).inv =
      R.map (r₂.symm ≪≫ r₁ ≪≫ r₀).inv ≫ q₃ := by
  simpa only [Iso.trans_inv, Iso.symm_inv, S.map_comp, Category.assoc] using
    paste_three R q₀ q₁ q₂ q₃ r₀.inv r₁.inv r₂.hom
      (S.map s₀.inv) (S.map s₁.inv) (S.map s₂.hom) h₀ h₁ h₂

private theorem pull_comp_nat (o : IntegralSystemRealization.Operations l E)
    (m : RealizationModel l E o)
    (c : Compositors l E o) {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W) :
    (Functor.whiskerLeft (ringedPull l E g) (m.reductionPull f).hom ≫
        Functor.whiskerRight (m.reductionPull g).hom (pull l E f)) ≫
        Functor.whiskerLeft (calculus l E W).reduction (c.pullComp f g).inv =
      Functor.whiskerRight (ringedPullComp l E f g).inv (calculus l E U).reduction ≫
        (m.reductionPull (f ≫ g)).hom := by
  apply NatTrans.ext
  funext A
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Category.assoc] using! pull_comp_inverse l E o m c f g A

private theorem pull_comp_nat_forward (o : IntegralSystemRealization.Operations l E)
    (m : RealizationModel l E o)
    (c : Compositors l E o) {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W) :
    (m.reductionPull (f ≫ g)).hom ≫
        Functor.whiskerLeft (calculus l E W).reduction (c.pullComp f g).hom =
      Functor.whiskerRight (ringedPullComp l E f g).hom (calculus l E U).reduction ≫
        Functor.whiskerLeft (ringedPull l E g) (m.reductionPull f).hom ≫
        Functor.whiskerRight (m.reductionPull g).hom (pull l E f) := by
  apply NatTrans.ext
  funext A
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Category.assoc] using!
      (GeneratorReduction.canonicalReductionPullComposition l E o m c f g A).symm

private theorem pull_square_nat (o : IntegralSystemRealization.Operations l E)
    (m : RealizationModel l E o)
    (c : Compositors l E o) {U' U V' V : Scheme.{u}}
    (v : U' ⟶ U) (j' : U' ⟶ V') (j : U ⟶ V) (g : V' ⟶ V)
    (w : v ≫ j = j' ≫ g) :
    (Functor.whiskerLeft (ringedPull l E j) (m.reductionPull v).hom ≫
        Functor.whiskerRight (m.reductionPull j).hom (pull l E v)) ≫
        Functor.whiskerLeft (calculus l E V).reduction (c.square l E v j' j g w).inv =
      Functor.whiskerRight (ringedSquare l E v j' j g w).inv (calculus l E U').reduction ≫
        (Functor.whiskerLeft (ringedPull l E g) (m.reductionPull j').hom ≫
          Functor.whiskerRight (m.reductionPull g).hom (pull l E j')) := by
  let R := (Functor.whiskeringRight (Integral l E V) (Integral l E U')
    (System l E U')).obj (calculus l E U').reduction
  let S := (Functor.whiskeringLeft (Integral l E V) (System l E V)
    (System l E U')).obj (calculus l E V).reduction
  let q₀ : (ringedPull l E j ⋙ ringedPull l E v) ⋙ (calculus l E U').reduction ⟶
      (calculus l E V).reduction ⋙ (pull l E j ⋙ pull l E v) :=
    Functor.whiskerLeft (ringedPull l E j) (m.reductionPull v).hom ≫
      Functor.whiskerRight (m.reductionPull j).hom (pull l E v)
  let q₃ : (ringedPull l E g ⋙ ringedPull l E j') ⋙ (calculus l E U').reduction ⟶
      (calculus l E V).reduction ⋙ (pull l E g ⋙ pull l E j') :=
    Functor.whiskerLeft (ringedPull l E g) (m.reductionPull j').hom ≫
      Functor.whiskerRight (m.reductionPull g).hom (pull l E j')
  have h := paste_iso_square R S q₀ (m.reductionPull (v ≫ j)).hom
    (m.reductionPull (j' ≫ g)).hom q₃
    (ringedPullComp l E v j)
    (eqToIso (congrArg (ringedPull l E) w.symm))
    (ringedPullComp l E j' g)
    (c.pullComp v j)
    (eqToIso (congrArg (pull l E) w.symm))
    (c.pullComp j' g)
    (by
      dsimp only [R, S, q₀, Functor.whiskeringRight_obj_map, Functor.whiskeringLeft_obj_map]
      exact pull_comp_nat l E o m c v j)
    (by
      dsimp only [R, S, Functor.whiskeringRight_obj_map, Functor.whiskeringLeft_obj_map]
      exact pull_congr_nat l E o m w)
    (by
      dsimp only [R, S, q₃, Functor.whiskeringRight_obj_map, Functor.whiskeringLeft_obj_map]
      exact pull_comp_nat_forward l E o m c j' g)
  simpa only [Compositors.square, ringedSquare, R, S, q₀, q₃,
    Functor.whiskeringRight_obj_map, Functor.whiskeringLeft_obj_map] using! h

attribute [local irreducible] ringedSquare Compositors.square

private theorem whisker_square_app
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Type*}
    [Category A₀] [Category A₁] [Category A₂] [Category A₃]
    [Category B₀] [Category B₁] [Category B₂] [Category B₃]
    {R₀ : A₀ ⥤ B₀} {R₁ : A₁ ⥤ B₁} {R₂ : A₂ ⥤ B₂} {R₃ : A₃ ⥤ B₃}
    {Pj : A₀ ⥤ A₁} {Pv : A₁ ⥤ A₃} {Pg : A₀ ⥤ A₂} {Pj' : A₂ ⥤ A₃}
    {Sj : B₀ ⥤ B₁} {Sv : B₁ ⥤ B₃} {Sg : B₀ ⥤ B₂} {Sj' : B₂ ⥤ B₃}
    (δj : Pj ⋙ R₁ ⟶ R₀ ⋙ Sj) (δv : Pv ⋙ R₃ ⟶ R₁ ⋙ Sv)
    (δg : Pg ⋙ R₂ ⟶ R₀ ⋙ Sg) (δj' : Pj' ⋙ R₃ ⟶ R₂ ⋙ Sj')
    (r : Pj ⋙ Pv ⟶ Pg ⋙ Pj') (s : Sj ⋙ Sv ⟶ Sg ⋙ Sj')
    (h : (Functor.whiskerLeft Pj δv ≫ Functor.whiskerRight δj Sv) ≫
        Functor.whiskerLeft R₀ s = Functor.whiskerRight r R₃ ≫
          (Functor.whiskerLeft Pg δj' ≫ Functor.whiskerRight δg Sj')) (L : A₀) :
    δv.app (Pj.obj L) ≫ Sv.map (δj.app L) ≫ s.app (R₀.obj L) =
      R₃.map (r.app L) ≫ δj'.app (Pg.obj L) ≫ Sj'.map (δg.app L) := by
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using congrArg (fun τ ↦ τ.app L) h

private theorem beta_mate_square
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {RA : A ⥤ A'} {RB : B ⥤ B'} {RC : C ⥤ C'} {RD : D ⥤ D'}
    {J : A ⥤ B} {P : B ⥤ A} {J' : C ⥤ D} {P' : D ⥤ C}
    {F : A' ⥤ B'} {G : B' ⥤ A'} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    {V : A ⥤ C} {W : B ⥤ D} {V' : A' ⥤ C'} {W' : B' ⥤ D'}
    (a : J ⊣ P) (a' : J' ⊣ P') (b : F ⊣ G) (b' : F' ⊣ G')
    (δj : P ⋙ RA ⟶ RB ⋙ G) (δj' : P' ⋙ RC ⟶ RD ⋙ G')
    (δv : V ⋙ RC ⟶ RA ⋙ V') (δg : W ⋙ RD ⟶ RB ⋙ W')
    (r : W ⋙ P' ≅ P ⋙ V) (s : W' ⋙ G' ≅ G ⋙ V')
    (α : J ⋙ W ≅ V ⋙ J') (β : F ⋙ W' ≅ V' ⋙ F')
    (hr : ∀ L, (a'.homEquiv _ _) (α.inv.app L) =
      V.map (a.unit.app L) ≫ r.inv.app (J.obj L))
    (hs : ∀ M, (b'.homEquiv _ _) (β.inv.app M) =
      V'.map (b.unit.app M) ≫ s.inv.app (F.obj M))
    (h : (Functor.whiskerLeft P δv ≫ Functor.whiskerRight δj V') ≫
        Functor.whiskerLeft RB s.inv = Functor.whiskerRight r.inv RC ≫
          (Functor.whiskerLeft W δj' ≫ Functor.whiskerRight δg G'))
    {L : A} {M : A'} (q : RA.obj L ⟶ M) (qJ : RB.obj (J.obj L) ⟶ F.obj M)
    [IsIso (((mateEquiv a' b').symm δj').natTrans.app (V.obj L))]
    (hu : q ≫ b.unit.app M = RA.map (a.unit.app L) ≫
      δj.app (J.obj L) ≫ G.map qJ) :
    inv (((mateEquiv a' b').symm δj').natTrans.app (V.obj L)) ≫
        F'.map (δv.app L ≫ V'.map q) ≫ β.inv.app M =
      RD.map (α.inv.app L) ≫ δg.app (J.obj L) ≫ W'.map qJ := by
  apply inverse_mate_square a' b' δj'
  rw [hr, hs]
  simp only [Functor.map_comp, Category.assoc]
  rw [← V'.map_comp_assoc, hu]
  simp only [Functor.map_comp, Category.assoc]
  have hn := δv.naturality (a.unit.app L)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  have hn' := s.inv.naturality qJ
  dsimp only [Functor.comp_map] at hn'
  rw [hn', reassoc_of% (whisker_square_app δj δv δg δj' r.inv s.inv h (J.obj L))]
  rfl

private theorem ordinaryProperOpenConjugateSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {P P' : A ⥤ B} {Q Q' : B ⥤ A} {F F' : C ⥤ D} {G G' : D ⥤ C}
    {R : A ⥤ C} {T : B ⥤ D}
    (a : P ⊣ Q) (a' : P' ⊣ Q') (b : F ⊣ G) (b' : F' ⊣ G')
    (χ : R ⋙ F ⟶ P ⋙ T) (χ' : R ⋙ F' ⟶ P' ⋙ T)
    (α : P' ⟶ P) (β : F' ⟶ F)
    (h : (TwoSquare.mk _ _ _ _ χ).whiskerRight β =
      (TwoSquare.mk _ _ _ _ χ').whiskerLeft α) (X : B) :
    (mateEquiv a b χ).natTrans.app X ≫
        (conjugateEquiv b b' β).app (T.obj X) =
      R.map ((conjugateEquiv a a' α).app X) ≫
        (mateEquiv a' b' χ').natTrans.app X := by
  have hh := congrArg (mateEquiv a b') h
  rw [mateEquiv_conjugateEquiv_vcomp a b b',
    conjugateEquiv_mateEquiv_vcomp a a' b'] at hh
  have hx := congrArg (fun t ↦ t.natTrans.app X) hh
  simpa only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop,
    TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Functor.comp_obj] using hx

private theorem composite_mate_app
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {P : A ⥤ B} {Q : B ⥤ A} {P' : B ⥤ C} {Q' : C ⥤ B}
    {L : D ⥤ E} {R : E ⥤ D} {L' : E ⥤ F} {R' : F ⥤ E}
    {U : A ⥤ D} {V : B ⥤ E} {W : C ⥤ F}
    (a : P ⊣ Q) (a' : P' ⊣ Q') (b : L ⊣ R) (b' : L' ⊣ R')
    (χ : U ⋙ L ⟶ P ⋙ V) (χ' : V ⋙ L' ⟶ P' ⋙ W) (X : C) :
    (mateEquiv (a.comp a') (b.comp b') (TwoSquare.vComp χ χ')).natTrans.app X =
      (mateEquiv a b χ).natTrans.app (Q'.obj X) ≫
        R.map ((mateEquiv a' b' χ').natTrans.app X) := by
  rw [mateEquiv_hcomp]
  simp only [TwoSquare.hComp, TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]

private theorem map_coefficient_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {R : A ⥤ B} {T : C ⥤ D} {F : A ⥤ C} {G : B ⥤ D}
    (δ : F ⋙ T ⟶ R ⋙ G) {L L' : A} {M M' : B}
    (q : R.obj L ⟶ M) (q' : R.obj L' ⟶ M')
    (α : L ⟶ L') (β : M ⟶ M') (h : q ≫ β = R.map α ≫ q') :
    δ.app L ≫ G.map q ≫ G.map β =
      T.map (F.map α) ≫ δ.app L' ≫ G.map q' := by
  have hn := δ.naturality α
  dsimp only [Functor.comp_map] at hn
  rw [← G.map_comp, h, G.map_comp, ← Category.assoc, ← hn]
  exact Category.assoc _ _ _

private theorem paste_five {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {A₀ A₁ A₂ A₃ A₄ A₅ : C} {B₀ B₁ B₂ B₃ B₄ B₅ : D}
    (q₀ : R.obj A₀ ⟶ B₀) (q₁ : R.obj A₁ ⟶ B₁)
    (q₂ : R.obj A₂ ⟶ B₂) (q₃ : R.obj A₃ ⟶ B₃)
    (q₄ : R.obj A₄ ⟶ B₄) (q₅ : R.obj A₅ ⟶ B₅)
    (r₀ : A₀ ⟶ A₁) (r₁ : A₁ ⟶ A₂) (r₂ : A₂ ⟶ A₃)
    (r₃ : A₃ ⟶ A₄) (r₄ : A₄ ⟶ A₅)
    (s₀ : B₀ ⟶ B₁) (s₁ : B₁ ⟶ B₂) (s₂ : B₂ ⟶ B₃)
    (s₃ : B₃ ⟶ B₄) (s₄ : B₄ ⟶ B₅)
    (h₀ : q₀ ≫ s₀ = R.map r₀ ≫ q₁) (h₁ : q₁ ≫ s₁ = R.map r₁ ≫ q₂)
    (h₂ : q₂ ≫ s₂ = R.map r₂ ≫ q₃) (h₃ : q₃ ≫ s₃ = R.map r₃ ≫ q₄)
    (h₄ : q₄ ≫ s₄ = R.map r₄ ≫ q₅) :
    q₀ ≫ s₀ ≫ s₁ ≫ s₂ ≫ s₃ ≫ s₄ = R.map (r₀ ≫ r₁ ≫ r₂ ≫ r₃ ≫ r₄) ≫ q₅ := by
  rw [reassoc_of% h₀, reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]
  simp only [R.map_comp, Category.assoc]

@[irreducible] private def restrictionIso
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {J : B ⥤ C} {K : A ⥤ C} (P : C ⥤ B)
    (cr : F ⋙ J ≅ K) (ur : 𝟭 B ≅ J ⋙ P) : K ⋙ P ≅ F :=
  Functor.isoWhiskerRight cr.symm P ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F ur.symm ≪≫ Functor.rightUnitor _

private theorem inverse_unit_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasZeroMorphisms D]
    {P : A ⥤ B} {Q : B ⥤ A} {F : C ⥤ D} {G : D ⥤ C}
    {R : A ⥤ C} {T : B ⥤ D} (a : P ⊣ Q) (b : F ⊣ G)
    (χ : Q ⋙ R ⟶ T ⋙ G) (ur : 𝟭 A ≅ P ⋙ Q) (us : 𝟭 C ≅ F ⋙ G)
    (X : A) (δ : T.obj (P.obj X) ⟶ F.obj (R.obj X))
    [IsIso (((mateEquiv a b).symm χ).natTrans.app X)]
    (hur : ur.hom.app X = a.unit.app X)
    (hus : us.hom.app (R.obj X) = b.unit.app (R.obj X))
    (hδ : δ = GeneratorReduction.inverseOrZero
      (((mateEquiv a b).symm χ).natTrans.app X)) :
    χ.app (P.obj X) ≫ G.map δ ≫ us.inv.app (R.obj X) = R.map (ur.inv.app X) := by
  have hu := GeneratorReduction.inverse_mate_unit_square a b χ (𝟙 (R.obj X))
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at hu
  have hx := inverse_square R (ur.app X) (us.app (R.obj X)) (𝟙 _)
    (χ.app (P.obj X) ≫ G.map δ) (by
      simp only [Iso.app_hom, Category.id_comp, hur, hus, hδ]
      exact hu)
  simpa only [Iso.app_inv, Category.comp_id, Category.assoc] using hx

private theorem trans_iso_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (R : A ⥤ B) (T : C ⥤ D)
    {F₀ F₁ F₂ : C ⥤ A} {G₀ G₁ G₂ : D ⥤ B}
    (r : F₀ ≅ F₁) (r' : F₁ ≅ F₂) (s : G₀ ≅ G₁) (s' : G₁ ≅ G₂)
    (L : C) (q₀ : R.obj (F₀.obj L) ⟶ G₀.obj (T.obj L))
    (q₁ : R.obj (F₁.obj L) ⟶ G₁.obj (T.obj L))
    (q₂ : R.obj (F₂.obj L) ⟶ G₂.obj (T.obj L))
    (h : q₀ ≫ s.hom.app (T.obj L) = R.map (r.hom.app L) ≫ q₁)
    (h' : q₁ ≫ s'.hom.app (T.obj L) = R.map (r'.hom.app L) ≫ q₂) :
    q₀ ≫ (s ≪≫ s').hom.app (T.obj L) = R.map ((r ≪≫ r').hom.app L) ≫ q₂ := by
  simp only [Iso.trans_hom, NatTrans.comp_app]
  rw [reassoc_of% h, h', ← R.map_comp_assoc]

@[irreducible] private def openR (o : IntegralSystemRealization.Operations l E)
    (m : RealizationModel l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    ringedOpen l E j ⋙ (calculus l E V).reduction ⟶
      (calculus l E U).reduction ⋙ IntegralSystemRealization.Operations.shriek l E o j :=
  (NatIso.ofComponents (fun L ↦
    @asIso _ _ _ _ ((m.openReduction l E j).app L)
      (GeneratorReduction.fixedOpenReduction_isIso l E o m j L))
    (fun f ↦ (m.openReduction l E j).naturality f)).inv

private theorem openR_app (o : IntegralSystemRealization.Operations l E)
    (m : RealizationModel l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] (L : Integral l E U) :
    (openR l E o m j).app L =
      GeneratorReduction.inverseOrZero ((m.openReduction l E j).app L) := by
  have := GeneratorReduction.fixedOpenReduction_isIso l E o m j L
  rw [GeneratorReduction.inverseOrZero_eq_inv, openR]
  rfl

private structure Models (o : IntegralSystemRealization.Operations l E) where
  compositors : Compositors l E o
  openComparisons : OpenComparisons l E o compositors
  realizationModel : RealizationModel l E o
  ringedModels : RingedModels l E
  ringedOpenComparisons : RingedOpenComparisons l E ringedModels

private theorem open_beta_inverse_square_of_data
    (o : IntegralSystemRealization.Operations l E) (a : Models l E o)
    {U' U V' V : Scheme.{u}} (v : U' ⟶ U) (j' : U' ⟶ V') (j : U ⟶ V) (g : V' ⟶ V)
    [IsOpenImmersion j] [IsOpenImmersion j']
    (r : ringedPull l E g ⋙ ringedPull l E j' ≅ ringedPull l E j ⋙ ringedPull l E v)
    (s : pull l E g ⋙ pull l E j' ≅ pull l E j ⋙ pull l E v)
    (α : ringedOpen l E j ⋙ ringedPull l E g ≅ ringedPull l E v ⋙ ringedOpen l E j')
    (β : IntegralSystemRealization.Operations.shriek l E o j ⋙ pull l E g ≅
      pull l E v ⋙ IntegralSystemRealization.Operations.shriek l E o j')
    (hr : ∀ L : Integral l E U,
      ((ringedOpenAdj l E j').homEquiv _ _) (α.inv.app L) =
        (ringedPull l E v).map ((ringedOpenAdj l E j).unit.app L) ≫
          r.inv.app ((ringedOpen l E j).obj L))
    (hs : ∀ M : System l E U,
      ((o.extension j').adj.homEquiv _ _) (β.inv.app M) =
        (pull l E v).map ((o.extension j).adj.unit.app M) ≫
          s.inv.app ((IntegralSystemRealization.Operations.shriek l E o j).obj M))
    (hn : (Functor.whiskerLeft (ringedPull l E j)
        (a.realizationModel.reductionPull v).hom ≫
        Functor.whiskerRight (a.realizationModel.reductionPull j).hom (pull l E v)) ≫
        Functor.whiskerLeft (calculus l E V).reduction s.inv =
      Functor.whiskerRight r.inv (calculus l E U').reduction ≫
        (Functor.whiskerLeft (ringedPull l E g) (a.realizationModel.reductionPull j').hom ≫
          Functor.whiskerRight (a.realizationModel.reductionPull g).hom (pull l E j')))
    (L : Integral l E U) (M : System l E U)
    (q : (calculus l E U).reduction.obj L ⟶ M)
    (qJ : (calculus l E V).reduction.obj ((ringedOpen l E j).obj L) ⟶
      (IntegralSystemRealization.Operations.shriek l E o j).obj M)
    [IsIso (((mateEquiv (ringedOpenAdj l E j') (o.extension j').adj).symm
      (a.realizationModel.reductionPull j').hom).natTrans.app ((ringedPull l E v).obj L))]
    (hu : q ≫ (o.extension j).adj.unit.app M =
      (calculus l E U).reduction.map ((ringedOpenAdj l E j).unit.app L) ≫
        (a.realizationModel.reductionPull j).hom.app ((ringedOpen l E j).obj L) ≫
        (pull l E j).map qJ) :
    inv (((mateEquiv (ringedOpenAdj l E j') (o.extension j').adj).symm
        (a.realizationModel.reductionPull j').hom).natTrans.app
          ((ringedPull l E v).obj L)) ≫
      (IntegralSystemRealization.Operations.shriek l E o j').map
        ((a.realizationModel.reductionPull v).hom.app L ≫ (pull l E v).map q) ≫
      β.inv.app M =
    (calculus l E V').reduction.map (α.inv.app L) ≫
      (a.realizationModel.reductionPull g).hom.app ((ringedOpen l E j).obj L) ≫
      (pull l E g).map qJ := by
  exact beta_mate_square
    (A := Integral l E U) (B := Integral l E V)
    (C := Integral l E U') (D := Integral l E V')
    (A' := System l E U) (B' := System l E V)
    (C' := System l E U') (D' := System l E V')
    (RA := (calculus l E U).reduction) (RB := (calculus l E V).reduction)
    (RC := (calculus l E U').reduction) (RD := (calculus l E V').reduction)
    (J := ringedOpen l E j) (P := ringedPull l E j)
    (J' := ringedOpen l E j') (P' := ringedPull l E j')
    (F := IntegralSystemRealization.Operations.shriek l E o j) (G := pull l E j)
    (F' := IntegralSystemRealization.Operations.shriek l E o j') (G' := pull l E j')
    (V := ringedPull l E v) (W := ringedPull l E g)
    (V' := pull l E v) (W' := pull l E g)
    (ringedOpenAdj l E j) (ringedOpenAdj l E j') (o.extension j).adj (o.extension j').adj
    (a.realizationModel.reductionPull j).hom (a.realizationModel.reductionPull j').hom
    (a.realizationModel.reductionPull v).hom (a.realizationModel.reductionPull g).hom
    r s α β hr hs hn q qJ hu

private theorem open_beta_inverse_square
    (o : IntegralSystemRealization.Operations l E) (a : Models l E o)
    {U' U V' V : Scheme.{u}} (v : U' ⟶ U) (j' : U' ⟶ V') (j : U ⟶ V) (g : V' ⟶ V)
    [IsOpenImmersion j] [IsOpenImmersion j']
    (w : v ≫ j = j' ≫ g) (sq : IsPullback v j' j g)
    (L : Integral l E U) (M : System l E U)
    (q : (calculus l E U).reduction.obj L ⟶ M)
    (qJ : (calculus l E V).reduction.obj ((ringedOpen l E j).obj L) ⟶
      (IntegralSystemRealization.Operations.shriek l E o j).obj M)
    [IsIso (((mateEquiv (ringedOpenAdj l E j') (o.extension j').adj).symm
      (a.realizationModel.reductionPull j').hom).natTrans.app ((ringedPull l E v).obj L))]
    (hu : q ≫ (o.extension j).adj.unit.app M =
      (calculus l E U).reduction.map ((ringedOpenAdj l E j).unit.app L) ≫
        (a.realizationModel.reductionPull j).hom.app ((ringedOpen l E j).obj L) ≫
        (pull l E j).map qJ) :
    inv (((mateEquiv (ringedOpenAdj l E j') (o.extension j').adj).symm
        (a.realizationModel.reductionPull j').hom).natTrans.app
          ((ringedPull l E v).obj L)) ≫
      (IntegralSystemRealization.Operations.shriek l E o j').map
        ((a.realizationModel.reductionPull v).hom.app L ≫ (pull l E v).map q) ≫
      (a.openComparisons.beta v j' j g w sq).inv.app M =
    (calculus l E V').reduction.map ((a.ringedOpenComparisons.beta v j' j g w sq).inv.app L) ≫
      (a.realizationModel.reductionPull g).hom.app ((ringedOpen l E j).obj L) ≫
      (pull l E g).map qJ := by
  exact open_beta_inverse_square_of_data l E o a
    (U' := U') (U := U) (V' := V') (V := V) v j' j g
    (ringedSquare l E v j' j g w) (a.compositors.square l E v j' j g w)
    (a.ringedOpenComparisons.beta v j' j g w sq)
    (a.openComparisons.beta v j' j g w sq)
    (a.ringedOpenComparisons.beta_transpose v j' j g w sq)
    (a.openComparisons.beta_transpose v j' j g w sq)
    (pull_square_nat l E o a.realizationModel a.compositors v j' j g w) L M q qJ hu

private theorem open_comp_coefficient_square
    (o : IntegralSystemRealization.Operations l E) (a : Models l E o)
    {U V W : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ W)
    [IsOpenImmersion j] [IsOpenImmersion k] (L : Integral l E U) :
    (openR l E o a.realizationModel k).app ((ringedOpen l E j).obj L) ≫
        (IntegralSystemRealization.Operations.shriek l E o k).map ((openR l E o a.realizationModel
          j).app L) ≫
        (a.compositors.openComp l E j k).hom.app ((calculus l E U).reduction.obj L) =
      (calculus l E W).reduction.map ((ringedOpenComp l E j k).hom.app L) ≫
        (openR l E o a.realizationModel (j ≫ k)).app L := by
  have hh := left_mate_compositor_square
    (ringedOpenAdj l E j) (ringedOpenAdj l E k) (ringedOpenAdj l E (j ≫ k))
    (o.extension j).adj (o.extension k).adj (o.extension (j ≫ k)).adj
    (a.realizationModel.openReduction l E j) (a.realizationModel.openReduction l E k)
    (a.realizationModel.openReduction l E (j ≫ k))
    (ringedOpenComp l E j k).inv (a.compositors.openComp l E j k).inv (by
      intro M
      simp only [RealizationModel.openReduction, ringedOpenAdj, ringedOpenComp,
        Compositors.openComp, Equiv.apply_symm_apply,
        Adjunction.conjugateEquiv_leftAdjointCompIso_inv, Iso.symm_hom]
      simpa only [TwoSquare.natTrans] using!
        pull_comp_inverse l E o a.realizationModel a.compositors j k M)
  have hx := congrArg (fun v ↦ v.natTrans.app L) hh
  dsimp only [TwoSquare.vComp, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
    TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app] at hx
  simp only [Category.id_comp, Category.comp_id, Functor.comp_obj] at hx
  have hj : ∀ M, IsIso ((a.realizationModel.openReduction l E j).app M) :=
    fun M ↦ GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel j M
  have hk : ∀ M, IsIso ((a.realizationModel.openReduction l E k).app M) :=
    fun M ↦ GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel k M
  have hjk : ∀ M, IsIso ((a.realizationModel.openReduction l E (j ≫ k)).app M) :=
    fun M ↦ GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel _ M
  have hi := congrArg (fun f ↦ GeneratorReduction.inverseOrZero f) hx
  simp only [GeneratorReduction.inverseOrZero_eq_inv, IsIso.inv_comp,
    ← CategoryTheory.Functor.map_inv, NatIso.inv_inv_app, Category.assoc] at hi
  simpa only [openR_app, GeneratorReduction.inverseOrZero_eq_inv, Category.assoc] using! hi

private theorem open_congr_coefficient_square
    (o : IntegralSystemRealization.Operations l E) (a : Models l E o)
    {U V : Scheme.{u}} {j k : U ⟶ V} [IsOpenImmersion j] [IsOpenImmersion k]
    (h : j = k) (L : Integral l E U) :
    (openR l E o a.realizationModel j).app L ≫
        (openCongr l E o h).hom.app ((calculus l E U).reduction.obj L) =
      (calculus l E V).reduction.map ((ringedOpenCongr l E h).hom.app L) ≫
        (openR l E o a.realizationModel k).app L := by
  subst k
  have hr : ringedOpenCongr l E (rfl : j = j) = Iso.refl _ := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply ((ringedOpenAdj l E j).homEquiv _ _).injective
    simp [ringedOpenCongr, Adjunction.leftAdjointUniq,
      conjugateIsoEquiv, Adjunction.homEquiv_unit]
  have hs : openCongr l E o (rfl : j = j) = Iso.refl _ := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply ((o.extension j).adj.homEquiv _ _).injective
    simp [openCongr, Adjunction.leftAdjointUniq,
      conjugateIsoEquiv, Adjunction.homEquiv_unit]
  rw [hr, hs]
  simp only [Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact Category.comp_id _

private theorem clopen_component
    (o : IntegralSystemRealization.Operations l E) (a : Models l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] [IsClosedImmersion j]
    (L : Integral l E U) (M : System l E U)
    (q : (calculus l E U).reduction.obj L ⟶ M) :
    (GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E j).app L) ≫
        (IntegralSystemRealization.Operations.shriek l E o j).map q) ≫
        (a.openComparisons.clopen j).hom.app M =
      (calculus l E V).reduction.map ((a.ringedOpenComparisons.clopen j).hom.app L) ≫
        (ordinaryPushReduction l E o a.realizationModel j).app L ≫
        (IntegralSystemRealization.Operations.push l E o j).map q := by
  have : IsIso ((ringedOpenAdj l E j).unit.app L) :=
    a.ringedOpenComparisons.unitIso j L
  have : IsIso ((o.extension j).adj.unit.app M) :=
    a.openComparisons.unitIso j M
  have hi : IsIso ((a.realizationModel.openReduction l E j).app L) :=
    GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel j L
  change IsIso (((mateEquiv (ringedOpenAdj l E j) (o.extension j).adj).symm
    (a.realizationModel.reductionPull j).hom).natTrans.app L) at hi
  have hu := GeneratorReduction.inverse_mate_unit_square (ringedOpenAdj l E j)
    (o.extension j).adj (a.realizationModel.reductionPull j).hom q
  have hc := GeneratorReduction.mate_counit_square (ringedAdj l E j)
    (o.direct j).adj (a.realizationModel.reductionPull j).symm q
  apply ((o.direct j).adj.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm]
  erw [a.openComparisons.clopen_transpose j M,
    Equiv.symm_apply_apply]
  change (pull l E j).map
      (GeneratorReduction.inverseOrZero
        ((a.realizationModel.openReduction l E j).app L) ≫
        (IntegralSystemRealization.Operations.shriek l E o j).map q) ≫
      inv ((o.extension j).adj.unit.app M) = _
  apply (cancel_epi ((calculus l E _).reduction.map
    ((ringedOpenAdj l E j).unit.app L) ≫
      (a.realizationModel.reductionPull j).hom.app ((ringedOpen l E j).obj L))).1
  simp only [Category.assoc]
  erw [← reassoc_of% hu]
  erw [IsIso.hom_inv_id, Category.comp_id]
  rw [Adjunction.homEquiv_counit]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := (a.realizationModel.reductionPull j).hom.naturality
    ((a.ringedOpenComparisons.clopen j).hom.app L)
  dsimp only [Functor.comp_map] at hn
  erw [← reassoc_of% hn]
  have hc' :
      (a.realizationModel.reductionPull j).hom.app ((ringedPush l E j).obj L) ≫
        (pull l E j).map ((ordinaryPushReduction l E o a.realizationModel j).app L) ≫
        (pull l E j).map ((IntegralSystemRealization.Operations.push l E o j).map q) ≫
        (o.direct j).adj.counit.app M =
      (calculus l E _).reduction.map ((ringedAdj l E j).counit.app L) ≫ q := by
    simpa only [ordinaryPushReduction, Iso.symm_inv, Iso.symm_hom,
      CategoryTheory.Functor.map_comp, Category.assoc] using! hc
  erw [hc']
  have hr := ((ringedAdj l E j).homEquiv _ _).symm_apply_apply
    (inv ((ringedOpenAdj l E j).unit.app L))
  rw [← a.ringedOpenComparisons.clopen_transpose j L] at hr
  change (ringedPull l E j).map
    ((a.ringedOpenComparisons.clopen j).hom.app L) ≫
      (ringedAdj l E j).counit.app L = _ at hr
  simp only [← CategoryTheory.Functor.map_comp_assoc, hr,
    IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem clopen_coefficient_square
    (o : IntegralSystemRealization.Operations l E) (a : Models l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] [IsClosedImmersion j]
    (L : Integral l E U) :
    (openR l E o a.realizationModel j).app L ≫
        (a.openComparisons.clopen j).hom.app ((calculus l E U).reduction.obj L) =
      (calculus l E V).reduction.map ((a.ringedOpenComparisons.clopen j).hom.app L) ≫
        (ordinaryPushReduction l E o a.realizationModel j).app L := by
  have h := clopen_component l E o a j L ((calculus l E U).reduction.obj L) (𝟙 _)
  rw [openR_app]
  simp only [CategoryTheory.Functor.map_id] at h
  calc
    _ = (GeneratorReduction.inverseOrZero
        ((a.realizationModel.openReduction l E j).app L) ≫ 𝟙 _) ≫
        (a.openComparisons.clopen j).hom.app ((calculus l E U).reduction.obj L) :=
      congrArg (fun f ↦ f ≫ (a.openComparisons.clopen j).hom.app
        ((calculus l E U).reduction.obj L)) (Category.comp_id _).symm
    _ = _ := h
    _ = _ := congrArg
      (fun q ↦ (calculus l E V).reduction.map
        ((a.ringedOpenComparisons.clopen j).hom.app L) ≫ q) (Category.comp_id _)

private theorem push_comp_coefficient_square
    (o : IntegralSystemRealization.Operations l E) (a : Models l E o)
    {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W)
    [IsProper f] [IsProper g] (L : Integral l E U) :
    (ordinaryPushReduction l E o a.realizationModel g).app ((ringedPush l E f).obj L) ≫
        (IntegralSystemRealization.Operations.push l E o g).map
          ((ordinaryPushReduction l E o a.realizationModel f).app L) ≫
        (a.compositors.pushComp l E f g).hom.app ((calculus l E U).reduction.obj L) =
      (calculus l E W).reduction.map ((ringedPushComp l E f g).hom.app L) ≫
        (ordinaryPushReduction l E o a.realizationModel (f ≫ g)).app L := by
  have h :
      (TwoSquare.vComp (a.realizationModel.reductionPull g).inv
        (a.realizationModel.reductionPull f).inv).whiskerRight
          (a.compositors.pullComp f g).hom =
      (TwoSquare.mk _ _ _ _ (a.realizationModel.reductionPull (f ≫ g)).inv).whiskerLeft
        (ringedPullComp l E f g).hom := by
    apply NatTrans.ext
    funext L
    dsimp only [TwoSquare.vComp, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
      TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id, Functor.comp_obj]
    apply (cancel_epi ((a.realizationModel.reductionPull
      (f ≫ g)).hom.app L)).1
    simp only [Iso.hom_inv_id_app_assoc]
    erw [← reassoc_of% (GeneratorReduction.canonicalReductionPullComposition l E
      o a.realizationModel a.compositors f g L)]
    simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
    exact Category.comp_id _
  have hm := GeneratorReduction.mate_compositor_square
    (ringedAdj l E g) (ringedAdj l E f)
    (ringedAdj l E (f ≫ g))
    (o.direct g).adj (o.direct f).adj (o.direct (f ≫ g)).adj
    (a.realizationModel.reductionPull g).inv
    (a.realizationModel.reductionPull f).inv
    (a.realizationModel.reductionPull (f ≫ g)).inv
    (ringedPullComp l E f g).hom
    (a.compositors.pullComp f g).hom h L
  simpa only [ordinaryPushReduction, Compositors.pushComp, ringedPushComp,
    TwoSquare.natTrans] using! hm

private theorem push_congr_coefficient_square
    (o : IntegralSystemRealization.Operations l E) (a : Models l E o)
    {U V : Scheme.{u}} {f g : U ⟶ V} (h : f = g) (L : Integral l E U) :
    (ordinaryPushReduction l E o a.realizationModel f).app L ≫
        (eqToIso (congrArg (IntegralSystemRealization.Operations.push l E o) h)).hom.app
          ((calculus l E U).reduction.obj L) =
      (calculus l E V).reduction.map
          ((eqToIso (congrArg (ringedPush l E) h)).hom.app L) ≫
        (ordinaryPushReduction l E o a.realizationModel g).app L := by
  subst g
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact Category.comp_id _

private theorem unit_inverse_coefficient_square
    (o : IntegralSystemRealization.Operations l E) (a : Models l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] (L : Integral l E U) :
    (a.realizationModel.reductionPull j).hom.app ((ringedOpen l E j).obj L) ≫
        (pull l E j).map ((openR l E o a.realizationModel j).app L) ≫
        (a.openComparisons.unit l E o a.compositors j).inv.app
          ((calculus l E U).reduction.obj L) =
      (calculus l E U).reduction.map
        ((a.ringedOpenComparisons.unit l E a.ringedModels j).inv.app L) := by
  have hi : IsIso (((mateEquiv (ringedOpenAdj l E j) (o.extension j).adj).symm
    (a.realizationModel.reductionPull j).hom).natTrans.app L) :=
    GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel j L
  exact inverse_unit_square (ringedOpenAdj l E j) (o.extension j).adj
    (a.realizationModel.reductionPull j).hom
    (a.ringedOpenComparisons.unit l E a.ringedModels j)
    (a.openComparisons.unit l E o a.compositors j) L
    ((openR l E o a.realizationModel j).app L) (by rfl) (by rfl)
    (by rw [openR_app]; rfl)


attribute [local irreducible] RingedOpenComparisons.unit OpenComparisons.unit

private theorem open_restriction_coefficient_square
    (o : IntegralSystemRealization.Operations l E) (a : Models l E o)
    {U P V : Scheme.{u}} (s : U ⟶ P) (b : P ⟶ V) (k : U ⟶ V)
    [IsOpenImmersion s] [IsOpenImmersion b] [IsOpenImmersion k]
    (h : s ≫ b = k) (L : Integral l E U) :
    (a.realizationModel.reductionPull b).hom.app ((ringedOpen l E k).obj L) ≫
        (pull l E b).map ((openR l E o a.realizationModel k).app L) ≫
        (restrictionIso (F := IntegralSystemRealization.Operations.shriek l E o s)
          (J := IntegralSystemRealization.Operations.shriek l E o b) (K :=
            IntegralSystemRealization.Operations.shriek l E o k)
          (pull l E b) (a.compositors.openComp l E s b ≪≫ openCongr l E o h)
          (a.openComparisons.unit l E o a.compositors b)).hom.app
            ((calculus l E U).reduction.obj L) =
      (calculus l E P).reduction.map
          ((restrictionIso (F := ringedOpen l E s) (J := ringedOpen l E b)
            (K := ringedOpen l E k) (ringedPull l E b)
            (ringedOpenComp l E s b ≪≫ ringedOpenCongr l E h)
            (a.ringedOpenComparisons.unit l E a.ringedModels b)).hom.app L) ≫
        (openR l E o a.realizationModel s).app L := by
  let cr := ringedOpenComp l E s b ≪≫ ringedOpenCongr l E h
  let cs := a.compositors.openComp l E s b ≪≫ openCongr l E o h
  let δ := (openR l E o a.realizationModel b).app ((ringedOpen l E s).obj L) ≫
    (IntegralSystemRealization.Operations.shriek l E o b).map ((openR l E o a.realizationModel
      s).app L)
  have hc := trans_iso_square (calculus l E V).reduction (calculus l E U).reduction
    (ringedOpenComp l E s b) (ringedOpenCongr l E h)
    (a.compositors.openComp l E s b) (openCongr l E o h)
    L δ ((openR l E o a.realizationModel (s ≫ b)).app L)
    ((openR l E o a.realizationModel k).app L)
    ((Category.assoc _ _ _).trans (open_comp_coefficient_square l E o a s b L))
    (open_congr_coefficient_square l E o a h L)
  have hc' := inverse_square (calculus l E V).reduction (cr.app L)
    (cs.app ((calculus l E U).reduction.obj L)) δ
    ((openR l E o a.realizationModel k).app L) hc
  have hn := (a.realizationModel.reductionPull b).hom.naturality (cr.inv.app L)
  have hn' := (a.openComparisons.unit l E o a.compositors b).inv.naturality
    ((openR l E o a.realizationModel s).app L)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at hn hn'
  simp only [restrictionIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.rightUnitor_hom_app,
    Iso.symm_hom, Functor.map_comp, Category.id_comp,
    Category.comp_id, Functor.comp_obj, Functor.id_obj, Category.assoc]
  rw [← (pull l E b).map_comp_assoc]
  rw [show (openR l E o a.realizationModel k).app L ≫
      cs.inv.app ((calculus l E U).reduction.obj L) =
      (calculus l E V).reduction.map (cr.inv.app L) ≫
        (openR l E o a.realizationModel b).app ((ringedOpen l E s).obj L) ≫
        (IntegralSystemRealization.Operations.shriek l E o b).map ((openR l E o a.realizationModel
          s).app L) by
    simpa only [Iso.app_inv, δ, Category.assoc] using hc']
  simp only [(pull l E b).map_comp, Category.assoc]
  rw [← reassoc_of% hn, hn',
    reassoc_of% (unit_inverse_coefficient_square l E o a b ((ringedOpen l E s).obj L))]

private abbrev functorSource {A B : Type*} [Category A] [Category B] (_ : A ⥤ B) := A
private abbrev functorTarget {A B : Type*} [Category A] [Category B] (_ : A ⥤ B) := B

private abbrev nativeIntegral (W : Scheme.{u}) :=
  functorSource ((calculus l E W).reduction)
private abbrev nativeSystem (W : Scheme.{u}) :=
  functorTarget ((calculus l E W).reduction)

-- Fix the category's own quiver when stating normalized component boundaries.
private abbrev systemHom (W : Scheme.{u}) (A B : System l E W) :=
  @Quiver.Hom _ (inferInstance : Category (System l E W)).toQuiver A B

private theorem cartesian_coefficient_square
    (o : IntegralSystemRealization.Operations l E) (a : Models l E o)
    {V W Z : Scheme.{u}} (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion i]
    (L : Integral l E V) :
    (a.realizationModel.reductionPull i).hom.app ((ringedPush l E p).obj L) ≫
        (pull l E i).map ((ordinaryPushReduction l E o a.realizationModel p).app L) ≫
        (cartesianConjugate l E o a.compositors a.openComparisons p i).hom.app
          ((calculus l E V).reduction.obj L) =
      (calculus l E W).reduction.map
          ((ringedCartesianConjugate l E a.ringedModels a.ringedOpenComparisons p i).hom.app L) ≫
        (ordinaryPushReduction l E o a.realizationModel (pullback.snd p i)).app
          ((ringedPull l E (pullback.fst p i)).obj L) ≫
        (IntegralSystemRealization.Operations.push l E o (pullback.snd p i)).map
          ((a.realizationModel.reductionPull (pullback.fst p i)).hom.app L) := by
  let q := pullback.snd p i
  let b := pullback.fst p i
  let χ₁ := TwoSquare.vComp (a.realizationModel.openReduction l E i)
    (a.realizationModel.reductionPull p).inv
  let χ₂ := TwoSquare.vComp (a.realizationModel.reductionPull q).inv
    (a.realizationModel.openReduction l E b)
  let α := (a.ringedOpenComparisons.beta q b i p
    pullback.condition.symm (IsPullback.of_hasPullback p i).flip).inv
  let β := (a.openComparisons.beta q b i p
    pullback.condition.symm (IsPullback.of_hasPullback p i).flip).inv
  have h : χ₁.whiskerRight β = χ₂.whiskerLeft α := by
    apply NatTrans.ext
    funext M
    have hi : IsIso ((a.realizationModel.openReduction l E i).app M) :=
      GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel i M
    have hi' : IsIso (((mateEquiv (ringedOpenAdj l E i) (o.extension i).adj).symm
        (a.realizationModel.reductionPull i).hom).natTrans.app M) := hi
    have hb : IsIso ((a.realizationModel.openReduction l E b).app
        ((ringedPull l E q).obj M)) :=
      GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel b _
    have hb' : IsIso (((mateEquiv (ringedOpenAdj l E b) (o.extension b).adj).symm
        (a.realizationModel.reductionPull b).hom).natTrans.app
          ((ringedPull l E q).obj M)) := hb
    let ζ₁ := (a.realizationModel.reductionPull p).hom.app ((ringedOpen l E i).obj M) ≫
      (pull l E p).map (inv ((a.realizationModel.openReduction l E i).app M))
    let ζ₂ := inv ((a.realizationModel.openReduction l E b).app
        ((ringedPull l E q).obj M)) ≫
      (IntegralSystemRealization.Operations.shriek l E o b).map ((a.realizationModel.reductionPull
        q).hom.app M)
    have hu := GeneratorReduction.inverse_mate_unit_square (ringedOpenAdj l E i)
      (o.extension i).adj (a.realizationModel.reductionPull i).hom
      (𝟙 ((calculus l E W).reduction.obj M))
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at hu
    have hs := open_beta_inverse_square l E o a q b i p
      pullback.condition.symm (IsPullback.of_hasPullback p i).flip M
      ((calculus l E W).reduction.obj M) (𝟙 _)
      (GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E i).app M))
      (by simpa only [CategoryTheory.Functor.map_id, Category.comp_id,
        RealizationModel.openReduction, ringedOpenAdj, TwoSquare.natTrans,
        IntegralSystemRealization.Operations.shriek, Category.comp_id] using! hu)
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at hs
    erw [GeneratorReduction.inverseOrZero_eq_inv] at hs
    have hs' : ζ₂ ≫ β.app ((calculus l E W).reduction.obj M) =
        (calculus l E V).reduction.map (α.app M) ≫ ζ₁ := by
      simpa only [ζ₁, ζ₂, α, β, ringedOpenAdj, RealizationModel.openReduction,
        TwoSquare.natTrans, IntegralSystemRealization.Operations.shriek,
        GeneratorReduction.inverseOrZero_eq_inv, CategoryTheory.Functor.map_id,
        Category.comp_id, Category.assoc] using! hs
    have hx := GeneratorReduction.inverse_square
      ((calculus l E V).reduction.map (α.app M))
      (β.app ((calculus l E W).reduction.obj M)) ζ₂ ζ₁ hs'.symm
    simpa only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
      TwoSquare.mk, TwoSquare.natTrans, χ₁, χ₂, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, ζ₁, ζ₂, GeneratorReduction.inverseOrZero_eq_inv,
      IsIso.inv_comp, ← CategoryTheory.Functor.map_inv, NatIso.inv_hom_app, IsIso.inv_inv,
      Category.id_comp, Category.comp_id, Functor.comp_obj, Category.assoc] using! hx
  have hm := ordinaryProperOpenConjugateSquare
    ((ringedOpenAdj l E i).comp (ringedAdj l E p))
    ((ringedAdj l E q).comp (ringedOpenAdj l E b))
    ((o.extension i).adj.comp (o.direct p).adj)
    ((o.direct q).adj.comp (o.extension b).adj) χ₁.natTrans χ₂.natTrans α β h L
  simp only [χ₁, χ₂, composite_mate_app] at hm
  simpa only [cartesianConjugate, ringedCartesianConjugate, conjugateIsoEquiv,
    ordinaryPushReduction, RealizationModel.openReduction, Equiv.apply_symm_apply,
    TwoSquare.natTrans, ringedOpenAdj, α, β, q, b, Category.assoc] using! hm

attribute [local irreducible] ringedCartesianConjugate ringedPushComp cartesianConjugate
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  Functor.leftAdjoint

attribute [local irreducible] getLimitCone limit.cone getColimitCocone colimit.cocone
  sheafificationAdjunction presheafToSheaf eqToIso eqToHom

@[irreducible] private def lambdaIso
    {A B C D E' : Type*} [Category A] [Category B] [Category C] [Category D] [Category E']
    (K : A ⥤ B) (P : B ⥤ C) (I : C ⥤ D) (J : B ⥤ E') (Q : E' ⥤ D)
    (S T : A ⥤ E') (F G : A ⥤ D)
    (c : P ⋙ I ≅ J ⋙ Q) (r : K ⋙ J ≅ S) (d : S ≅ T)
    (p : T ⋙ Q ≅ F) (e : F ≅ G) : (K ⋙ P) ⋙ I ≅ G :=
  Functor.associator K P I ≪≫ Functor.isoWhiskerLeft K c ≪≫
    (Functor.associator K J Q).symm ≪≫ Functor.isoWhiskerRight r Q ≪≫
    Functor.isoWhiskerRight d Q ≪≫ p ≪≫ e

private theorem lambda_components
    {A B C D E' : Type*} [Category A] [Category B] [Category C] [Category D] [Category E']
    (K : A ⥤ B) (P : B ⥤ C) (I : C ⥤ D) (J : B ⥤ E') (Q : E' ⥤ D)
    (S T : A ⥤ E') (F G : A ⥤ D)
    (c : P ⋙ I ≅ J ⋙ Q) (r : K ⋙ J ≅ S) (d : S ≅ T)
    (p : T ⋙ Q ≅ F) (e : F ≅ G) (X : A) :
    (lambdaIso K P I J Q S T F G c r d p e).hom.app X =
      c.hom.app (K.obj X) ≫ Q.map (r.hom.app X) ≫ Q.map (d.hom.app X) ≫
        p.hom.app X ≫ e.hom.app X := by
  unfold lambdaIso
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    Category.id_comp]

private theorem lambda_components_of_eq
    {A B C D E' : Type*} [Category A] [Category B] [Category C] [Category D] [Category E']
    (K : A ⥤ B) (P : B ⥤ C) (I : C ⥤ D) (J : B ⥤ E') (Q : E' ⥤ D)
    (S T : A ⥤ E') (F G : A ⥤ D)
    (c : P ⋙ I ≅ J ⋙ Q) (r : K ⋙ J ≅ S) (d : S ≅ T)
    (p : T ⋙ Q ≅ F) (e : F ≅ G) (e₀ : (K ⋙ P) ⋙ I ≅ G)
    (he : e₀ = lambdaIso K P I J Q S T F G c r d p e) (X : A) :
    e₀.hom.app X =
      c.hom.app (K.obj X) ≫ Q.map (r.hom.app X) ≫ Q.map (d.hom.app X) ≫
        p.hom.app X ≫ e.hom.app X := by
  rw [he]
  exact lambda_components K P I J Q S T F G c r d p e X

private theorem lambda_square
    {A B C D H A' B' C' D' H' : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category H]
    [Category A'] [Category B'] [Category C'] [Category D'] [Category H']
    (R : D ⥤ D') (T₀ : A ⥤ A')
    (K : A ⥤ B) (P : B ⥤ C) (I : C ⥤ D) (J : B ⥤ H) (Q : H ⥤ D)
    (S T : A ⥤ H) (F G : A ⥤ D)
    (c : P ⋙ I ≅ J ⋙ Q) (r : K ⋙ J ≅ S) (d : S ≅ T)
    (p : T ⋙ Q ≅ F) (e : F ≅ G)
    (K' : A' ⥤ B') (P' : B' ⥤ C') (I' : C' ⥤ D') (J' : B' ⥤ H')
    (Q' : H' ⥤ D') (S' T' : A' ⥤ H') (F' G' : A' ⥤ D')
    (c' : P' ⋙ I' ≅ J' ⋙ Q') (r' : K' ⋙ J' ≅ S') (d' : S' ≅ T')
    (p' : T' ⋙ Q' ≅ F') (e' : F' ≅ G')
    (lamR : (K ⋙ P) ⋙ I ≅ G) (lamS : (K' ⋙ P') ⋙ I' ≅ G')
    (hr : lamR = lambdaIso K P I J Q S T F G c r d p e)
    (hs : lamS = lambdaIso K' P' I' J' Q' S' T' F' G' c' r' d' p' e')
    (X : A)
    (q₀ : R.obj (I.obj (P.obj (K.obj X))) ⟶ I'.obj (P'.obj (K'.obj (T₀.obj X))))
    (q₅ : R.obj (G.obj X) ⟶ G'.obj (T₀.obj X))
    (h : q₀ ≫ c'.hom.app (K'.obj (T₀.obj X)) ≫ Q'.map (r'.hom.app (T₀.obj X)) ≫
          Q'.map (d'.hom.app (T₀.obj X)) ≫ p'.hom.app (T₀.obj X) ≫
          e'.hom.app (T₀.obj X) =
        R.map (c.hom.app (K.obj X) ≫ Q.map (r.hom.app X) ≫ Q.map (d.hom.app X) ≫
          p.hom.app X ≫ e.hom.app X) ≫ q₅) :
    q₀ ≫ lamS.hom.app (T₀.obj X) = R.map (lamR.hom.app X) ≫ q₅ := by
  have hsys := lambda_components_of_eq K' P' I' J' Q' S' T' F' G'
    c' r' d' p' e' lamS hs (T₀.obj X)
  have hring := lambda_components_of_eq K P I J Q S T F G c r d p e lamR hr X
  rw [hsys, hring]
  exact h

private theorem ringed_lambda_iso
    (o : IntegralSystemRealization.Operations l E) (a : Models l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
        ringedProperOpenLambda l E a.ringedModels a.ringedOpenComparisons k r p i h =
          lambdaIso (ringedOpen l E k) (ringedPush l E p) (ringedPull l E i)
      (ringedPull l E (pullback.fst p i)) (ringedPush l E (pullback.snd p i))
      (ringedOpen l E (ProEtale.StrictTower.squareLift k r p i h))
      (ringedPush l E (ProEtale.StrictTower.squareLift k r p i h))
      (ringedPush l E ((ProEtale.StrictTower.squareLift k r p i h) ≫ pullback.snd p i))
      (ringedPush l E r)
      (ringedCartesianConjugate l E a.ringedModels a.ringedOpenComparisons p i)
      (ringedRestrictFactor l E a.ringedModels a.ringedOpenComparisons k r p i h)
      (a.ringedOpenComparisons.clopen (ProEtale.StrictTower.squareLift k r p i h))
      (ringedPushComp l E (ProEtale.StrictTower.squareLift k r p i h) (pullback.snd p i))
      (eqToIso (congrArg (ringedPush l E) (pullback.lift_snd k r h)))
    := by
  unfold ringedProperOpenLambda lambdaIso
  rfl

@[irreducible] private def initialCoefficient
    (o : IntegralSystemRealization.Operations l E) (a : Models l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] (L : Integral l E U) : systemHom l E W
        ((calculus l E W).reduction.obj
          ((ringedPull l E i).obj ((ringedPush l E p).obj ((ringedOpen l E k).obj L))))
        ((pull l E i).obj ((IntegralSystemRealization.Operations.push l E o p).obj
          ((IntegralSystemRealization.Operations.shriek l E o k).obj ((calculus l E
            U).reduction.obj L)))) :=
      ((a.realizationModel.reductionPull i).hom.app
          ((ringedPush l E p).obj ((ringedOpen l E k).obj L)) ≫
        (pull l E i).map
          ((ordinaryPushReduction l E o a.realizationModel p).app ((ringedOpen l E k).obj L) ≫
            (IntegralSystemRealization.Operations.push l E o p).map ((openR l E o
              a.realizationModel k).app L)))

@[irreducible] private def finalCoefficient
    (o : IntegralSystemRealization.Operations l E) (m : RealizationModel l E o)
    {U W : Scheme.{u}} (r : U ⟶ W) (L : Integral l E U) : systemHom l E W
        ((calculus l E W).reduction.obj ((ringedPush l E r).obj L))
        ((IntegralSystemRealization.Operations.push l E o r).obj ((calculus l E U).reduction.obj
          L)) :=
      (ordinaryPushReduction l E o m r).app L

private theorem raw_lambda_coefficient_square
    (o : IntegralSystemRealization.Operations l E) (a : Models l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (L : Integral l E U) :
    let s := ProEtale.StrictTower.squareLift k r p i h
    let q := pullback.snd p i
    let δ₀ := initialCoefficient l E o a k p i L
    let δ₅ := finalCoefficient l E o a.realizationModel r L
    δ₀ ≫
        ((cartesianConjugate l E o a.compositors a.openComparisons p i).hom.app
            ((IntegralSystemRealization.Operations.shriek l E o k).obj ((calculus l E
              U).reduction.obj L)) ≫
          (IntegralSystemRealization.Operations.push l E o q).map
            ((restrictFactor l E o a.compositors a.openComparisons k r p i h).hom.app
              ((calculus l E U).reduction.obj L)) ≫
          (IntegralSystemRealization.Operations.push l E o q).map
            ((a.openComparisons.clopen s).hom.app ((calculus l E U).reduction.obj L)) ≫
          (a.compositors.pushComp l E s q).hom.app ((calculus l E U).reduction.obj L) ≫
          (eqToIso (congrArg (IntegralSystemRealization.Operations.push l E o) (pullback.lift_snd
            k r h))).hom.app
            ((calculus l E U).reduction.obj L)) =
      (calculus l E W).reduction.map
          ((ringedCartesianConjugate l E a.ringedModels a.ringedOpenComparisons p i).hom.app
            ((ringedOpen l E k).obj L) ≫
          (ringedPush l E q).map
            ((ringedRestrictFactor l E a.ringedModels a.ringedOpenComparisons k r p i h).hom.app
              L) ≫
          (ringedPush l E q).map ((a.ringedOpenComparisons.clopen s).hom.app L) ≫
          (ringedPushComp l E s q).hom.app L ≫
          (eqToIso (congrArg (ringedPush l E) (pullback.lift_snd k r h))).hom.app L
          ) ≫
        δ₅ := by
  let s := ProEtale.StrictTower.squareLift k r p i h
  let b := pullback.fst p i
  let q := pullback.snd p i
  let δ₀ := (a.realizationModel.reductionPull i).hom.app
      ((ringedPush l E p).obj ((ringedOpen l E k).obj L)) ≫
    (pull l E i).map
      ((ordinaryPushReduction l E o a.realizationModel p).app ((ringedOpen l E k).obj L) ≫
        (IntegralSystemRealization.Operations.push l E o p).map ((openR l E o a.realizationModel
          k).app L))
  let δ₁ := (ordinaryPushReduction l E o a.realizationModel q).app
      ((ringedPull l E b).obj ((ringedOpen l E k).obj L)) ≫
    (IntegralSystemRealization.Operations.push l E o q).map
      ((a.realizationModel.reductionPull b).hom.app ((ringedOpen l E k).obj L) ≫
        (pull l E b).map ((openR l E o a.realizationModel k).app L))
  let δ₂ := (ordinaryPushReduction l E o a.realizationModel q).app
      ((ringedOpen l E s).obj L) ≫
    (IntegralSystemRealization.Operations.push l E o q).map ((openR l E o a.realizationModel
      s).app L)
  let δ₃ := (ordinaryPushReduction l E o a.realizationModel q).app
      ((ringedPush l E s).obj L) ≫
    (IntegralSystemRealization.Operations.push l E o q).map
      ((ordinaryPushReduction l E o a.realizationModel s).app L)
  let δ₄ := (ordinaryPushReduction l E o a.realizationModel (s ≫ q)).app L
  let δ₅ := (ordinaryPushReduction l E o a.realizationModel r).app L
  have h₀ : δ₀ ≫ (cartesianConjugate l E o a.compositors a.openComparisons p i).hom.app
        ((IntegralSystemRealization.Operations.shriek l E o k).obj ((calculus l E U).reduction.obj
          L)) =
      (calculus l E W).reduction.map
          ((ringedCartesianConjugate l E a.ringedModels a.ringedOpenComparisons p i).hom.app
            ((ringedOpen l E k).obj L)) ≫ δ₁ := by
    have hc := cartesian_coefficient_square l E o a p i ((ringedOpen l E k).obj L)
    have hn := (cartesianConjugate l E o a.compositors a.openComparisons p i).hom.naturality
      ((openR l E o a.realizationModel k).app L)
    dsimp only [Functor.comp_map] at hn
    simp only [δ₀, δ₁, CategoryTheory.Functor.map_comp, Category.assoc]
    erw [hn, reassoc_of% hc]
  have h₁ := map_coefficient_square
    (ordinaryPushReduction l E o a.realizationModel q)
    ((a.realizationModel.reductionPull b).hom.app ((ringedOpen l E k).obj L) ≫
      (pull l E b).map ((openR l E o a.realizationModel k).app L))
    ((openR l E o a.realizationModel s).app L)
    ((ringedRestrictFactor l E a.ringedModels a.ringedOpenComparisons k r p i h).hom.app L)
    ((restrictFactor l E o a.compositors a.openComparisons k r p i h).hom.app
      ((calculus l E U).reduction.obj L))
    (by
      have hr := open_restriction_coefficient_square l E o a s b k
        (pullback.lift_fst k r h) L
      have hs : restrictFactor l E o a.compositors a.openComparisons k r p i h =
          restrictionIso (F := IntegralSystemRealization.Operations.shriek l E o s)
            (J := IntegralSystemRealization.Operations.shriek l E o b) (K :=
              IntegralSystemRealization.Operations.shriek l E o k)
            (pull l E b) (a.compositors.openComp l E s b ≪≫ openCongr l E o
              (pullback.lift_fst k r h)) (a.openComparisons.unit l E o a.compositors b) := by
        unfold restrictFactor restrictionIso
        rfl
      have ht : ringedRestrictFactor l E a.ringedModels a.ringedOpenComparisons k r p i h =
          restrictionIso (F := ringedOpen l E s) (J := ringedOpen l E b)
            (K := ringedOpen l E k) (ringedPull l E b)
            (ringedOpenComp l E s b ≪≫ ringedOpenCongr l E (pullback.lift_fst k r h))
            (a.ringedOpenComparisons.unit l E a.ringedModels b) := by
        unfold ringedRestrictFactor restrictionIso
        rfl
      erw [hs, ht]
      exact (Category.assoc _ _ _).trans hr)
  have h₂ := map_coefficient_square
    (ordinaryPushReduction l E o a.realizationModel q)
    ((openR l E o a.realizationModel s).app L)
    ((ordinaryPushReduction l E o a.realizationModel s).app L)
    ((a.ringedOpenComparisons.clopen s).hom.app L)
    ((a.openComparisons.clopen s).hom.app ((calculus l E U).reduction.obj L))
    (clopen_coefficient_square l E o a s L)
  have h₃ := push_comp_coefficient_square l E o a s q L
  have h₄ := push_congr_coefficient_square l E o a (pullback.lift_snd k r h) L
  have ht := paste_five (calculus l E W).reduction δ₀ δ₁ δ₂ δ₃ δ₄ δ₅
    ((ringedCartesianConjugate l E a.ringedModels a.ringedOpenComparisons p i).hom.app
      ((ringedOpen l E k).obj L))
    ((ringedPush l E q).map
      ((ringedRestrictFactor l E a.ringedModels a.ringedOpenComparisons k r p i h).hom.app L))
    ((ringedPush l E q).map ((a.ringedOpenComparisons.clopen s).hom.app L))
    ((ringedPushComp l E s q).hom.app L)
    ((eqToIso (congrArg (ringedPush l E) (pullback.lift_snd k r h))).hom.app L)
    ((cartesianConjugate l E o a.compositors a.openComparisons p i).hom.app
      ((IntegralSystemRealization.Operations.shriek l E o k).obj ((calculus l E U).reduction.obj
        L)))
    ((IntegralSystemRealization.Operations.push l E o q).map
      ((restrictFactor l E o a.compositors a.openComparisons k r p i h).hom.app
        ((calculus l E U).reduction.obj L)))
    ((IntegralSystemRealization.Operations.push l E o q).map
      ((a.openComparisons.clopen s).hom.app ((calculus l E U).reduction.obj L)))
    ((a.compositors.pushComp l E s q).hom.app ((calculus l E U).reduction.obj L))
    ((eqToIso (congrArg (IntegralSystemRealization.Operations.push l E o) (pullback.lift_snd k r
      h))).hom.app
      ((calculus l E U).reduction.obj L)) h₀
    (by simpa only [δ₁, δ₂, Category.assoc] using! h₁)
    (by simpa only [δ₂, δ₃, Category.assoc] using! h₂)
    (by simpa only [δ₃, δ₄, Category.assoc] using! h₃) h₄
  simpa only [initialCoefficient, finalCoefficient] using! ht

-- Infer the dependent function type from the abstract application. An explicit
-- normalized type would force conversion of entire chosen derived categories.
set_option linter.defProp false in
@[irreducible] private def lambda_from_raw
    (o : IntegralSystemRealization.Operations l E) (a : Models l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (L : Integral l E U) :=
  let s := ProEtale.StrictTower.squareLift k r p i h
  let b := pullback.fst p i
  let q := pullback.snd p i
  let hs : properOpenLambda l E o a.compositors a.openComparisons k r p i h =
      lambdaIso (IntegralSystemRealization.Operations.shriek l E o k)
        (IntegralSystemRealization.Operations.push l E o p)
        (pull l E i) (pull l E b) (IntegralSystemRealization.Operations.push l E o q)
        (IntegralSystemRealization.Operations.shriek l E o s)
          (IntegralSystemRealization.Operations.push l E o s)
        (IntegralSystemRealization.Operations.push l E o (s ≫ q))
          (IntegralSystemRealization.Operations.push l E o r)
        (cartesianConjugate l E o a.compositors a.openComparisons p i)
        (restrictFactor l E o a.compositors a.openComparisons k r p i h)
        (a.openComparisons.clopen s) (a.compositors.pushComp l E s q)
        (eqToIso (congrArg (IntegralSystemRealization.Operations.push l E o) (pullback.lift_snd k
          r h))) := by
    unfold properOpenLambda lambdaIso
    rfl
  lambda_square
    (A := nativeIntegral l E U) (B := nativeIntegral l E V)
    (C := nativeIntegral l E Z) (D := nativeIntegral l E W)
    (H := nativeIntegral l E (pullback p i))
    (A' := nativeSystem l E U) (B' := nativeSystem l E V)
    (C' := nativeSystem l E Z) (D' := nativeSystem l E W)
    (H' := nativeSystem l E (pullback p i))
    (calculus l E W).reduction (calculus l E U).reduction
    (ringedOpen l E k) (ringedPush l E p) (ringedPull l E i)
    (ringedPull l E b) (ringedPush l E q) (ringedOpen l E s) (ringedPush l E s)
    (ringedPush l E (s ≫ q)) (ringedPush l E r)
    (ringedCartesianConjugate l E a.ringedModels a.ringedOpenComparisons p i)
    (ringedRestrictFactor l E a.ringedModels a.ringedOpenComparisons k r p i h)
    (a.ringedOpenComparisons.clopen s) (ringedPushComp l E s q)
    (eqToIso (congrArg (ringedPush l E) (pullback.lift_snd k r h)))
    (IntegralSystemRealization.Operations.shriek l E o k)
      (IntegralSystemRealization.Operations.push l E o p) (pull l E i)
    (pull l E b) (IntegralSystemRealization.Operations.push l E o q)
    (IntegralSystemRealization.Operations.shriek l E o s)
      (IntegralSystemRealization.Operations.push l E o s)
    (IntegralSystemRealization.Operations.push l E o (s ≫ q))
      (IntegralSystemRealization.Operations.push l E o r)
    (cartesianConjugate l E o a.compositors a.openComparisons p i)
    (restrictFactor l E o a.compositors a.openComparisons k r p i h)
    (a.openComparisons.clopen s) (a.compositors.pushComp l E s q)
    (eqToIso (congrArg (IntegralSystemRealization.Operations.push l E o) (pullback.lift_snd k r h)))
    (ringedProperOpenLambda l E a.ringedModels a.ringedOpenComparisons k r p i h)
    (properOpenLambda l E o a.compositors a.openComparisons k r p i h)
    (ringed_lambda_iso l E o a k r p i h) hs
    L
    (initialCoefficient l E o a k p i L)
    (finalCoefficient l E o a.realizationModel r L)

-- Normalize composition evaluation before constructing congruence proofs.
private meta def compProjection (x : Lean.Expr) :
    Lean.MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let args := x.getAppArgs
  if x.isAppOf ``Functor.obj && args.size ≥ 2 then
    let f := args[args.size - 2]!
    if f.isAppOf ``Functor.comp then
      let fs := f.getAppArgs
      let h ← Lean.Meta.mkAppM ``Functor.comp_obj
        #[fs[fs.size - 2]!, fs[fs.size - 1]!, args[args.size - 1]!]
      let rhs := (← Lean.Meta.inferType h).getAppArgs.back!
      return some (rhs, ← Lean.Meta.mkHEqOfEq h)
  return none

-- Reify congruence between definitionally equal presentations into explicit HEq proofs.
-- This keeps the kernel from unfolding chosen derived categories while comparing
-- compound functor expressions. The reflexivity leaves and the resulting casts are
-- all checked by the kernel; this procedure adds no mathematical assumption.
private meta partial def typeCongruence (x y : Lean.Expr) : Lean.MetaM Lean.Expr := do
  if x == y then return ← Lean.Meta.mkHEqRefl x
  if let some (x', h) ← compProjection x then
    return ← Lean.Meta.mkAppM ``HEq.trans #[h, ← typeCongruence x' y]
  if let some (y', h) ← compProjection y then
    return ← Lean.Meta.mkAppM ``HEq.trans
      #[← typeCongruence x y', ← Lean.Meta.mkAppM ``HEq.symm #[h]]
  if (← Lean.Meta.isProof x) && (← Lean.Meta.isProof y) then
    return ← Lean.Meta.mkAppM ``proof_irrel_heq #[x, y]
  if x.getAppFn == y.getAppFn && x.isApp && x.getAppNumArgs == y.getAppNumArgs then
    let xs := x.getAppArgs
    let ys := y.getAppArgs
    let thm ← Lean.Meta.mkHCongrWithArity x.getAppFn xs.size
    let mut args := #[]
    for a in xs, b in ys, kind in thm.argKinds do
      let h ← typeCongruence a b
      match kind with
      | .eq =>
        let h ← Lean.Meta.mkEqOfHEq h
        args := args ++ #[a, b, h]
      | .heq => args := args ++ #[a, b, h]
      | _ => throwError "Unexpected congruence argument"
    let h := Lean.mkAppN thm.proof args
    if (← Lean.Meta.inferType h).isHEq then return h
    return ← Lean.Meta.mkHEqOfEq h
  return ← Lean.Meta.mkHEqRefl x

private theorem lambda_coefficient_square
    (o : IntegralSystemRealization.Operations l E) (a : Models l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (L : Integral l E U) :
    let δ₀ := initialCoefficient l E o a k p i L
    let δ₅ := finalCoefficient l E o a.realizationModel r L
    δ₀ ≫
        (properOpenLambda l E o a.compositors a.openComparisons k r p i h).hom.app
          ((calculus l E U).reduction.obj L) =
      (calculus l E W).reduction.map
          ((ringedProperOpenLambda l E a.ringedModels a.ringedOpenComparisons
            k r p i h).hom.app L) ≫
        δ₅ := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let args ← #[`l, `E, `o, `a, `k, `r, `p, `i, `h, `L].mapM fun n ↦
      Lean.Elab.Term.elabTerm (Lean.mkIdent n) none
    let f ← Lean.Meta.mkAppM ``lambda_from_raw args
    let raw ← Lean.Meta.mkAppM ``raw_lambda_coefficient_square args
    let ft ← Lean.Meta.whnf (← Lean.Meta.inferType f)
    let rt ← Lean.Meta.whnf (← Lean.Meta.inferType raw)
    let e ← Lean.Meta.mkEqOfHEq (← typeCongruence rt ft.bindingDomain!)
    let raw' ← Lean.Meta.mkAppM ``Eq.mp #[e, raw]
    let result := Lean.mkApp f raw'
    let out ← Lean.Meta.whnf (← Lean.Meta.inferType result)
    let goal ← Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget)
    let e ← Lean.Meta.mkEqOfHEq (← typeCongruence out goal)
    let result ← Lean.Meta.mkAppM ``Eq.mp #[e, result]
    Lean.Elab.Tactic.closeMainGoal `exact result

end FourFactorProof

/-- The ordinary square for the four prescribed lambda factors, before a finite
word is substituted for the child object.  It is strictly the component step:
the caller supplies the child comparison `f`, while this statement contains no
recursive `Word` comparison.  The proof expands the cartesian, restriction,
clopen and compositor factors and pastes their four component squares.
Source: `fix-prop-coherence.proof.md`, proper/open lambda coefficient-square
expansion.
(blueprint: lem-sf-proper-open-lambda-four-factor-square) -/
theorem properOpenLambdaFourFactorSquare
    {D : FiniteFieldDatum.{u}} (Cf : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic Cf.l) E]
    [FiniteDimensional (Padic Cf.l) E] (o : Operations Cf.l E)
    {S : Type s} (W : S → Scheme.{u})
    {a b c d : S}
    (k : W a ⟶ W b) (r : W a ⟶ W c) (p : W b ⟶ W d) (j : W c ⟶ W d)
    (h : k ≫ p = r ≫ j) (hk : IsOpenImmersion k) (hki : QuasiCompact k)
    (hjo : IsOpenImmersion j) (hji : QuasiCompact j)
    (hr : IsProper r) (hp : IsProper p)
    (M : DerivedCategory (scalarReductionSource Cf.l E (W a)))
    (N : coefficientSequenceDerived Cf.l E (W a))
    (f : (IntegralSystemRealization.calculus Cf.l E (W a)).reduction.obj M ⟶ N) :
    properOpenLambdaFourFactorSource Cf.l E W o k r p j hk hki hjo hji hr hp M N f ≫
        (IntegralSystemRealization.properOpenLambda Cf.l E o.system o.composition o.opens
          k r p j h).hom.app N =
      (IntegralSystemRealization.calculus Cf.l E (W c)).reduction.map
          ((IntegralSystemRealization.ringedProperOpenLambda Cf.l E o.ringed
            o.ringedOpens k r p j h).hom.app M) ≫
        properOpenLambdaFourFactorTarget Cf.l E W o r hr M N f := by
  letI := hk
  letI := hki
  letI := hjo
  letI := hji
  letI := hr
  letI := hp
  let a : FourFactorProof.Models Cf.l E o.system := {
    compositors := o.composition
    openComparisons := o.opens
    realizationModel := o.realization
    ringedModels := o.ringed
    ringedOpenComparisons := o.ringedOpens }
  have hs := FourFactorProof.lambda_coefficient_square Cf.l E o.system a k r p j h M
  have hn := (IntegralSystemRealization.properOpenLambda Cf.l E
    o.system o.composition o.opens k r p j h).hom.naturality f
  dsimp only [Functor.comp_map] at hn
  have hs' := congrArg (fun t ↦ t ≫
    (IntegralSystemRealization.Operations.push Cf.l E o.system r).map f) hs
  simp only [FourFactorProof.initialCoefficient, FourFactorProof.finalCoefficient,
    a, Category.assoc] at hs'
  simp only [properOpenLambdaFourFactorSource, properOpenLambdaFourFactorTarget,
    ← Category.assoc]
  rw [Category.assoc, Category.assoc, Category.assoc, hn]
  simpa only [ordinaryPushReductionK5, FourFactorProof.ordinaryPushReduction,
    FourFactorProof.openR_app, Functor.map_comp, Category.assoc] using! hs'

end WeilConjectures.OpenInterchangeReduction
