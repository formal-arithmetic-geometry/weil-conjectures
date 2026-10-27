/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Paper.CanonicalTateNaturalityLaws
import Sheaf.SecSmoothPurity.CochainCoefficientArrows

/-! # Canonical Tate naturality: OrdinaryNaturality

Source: current blueprint, def-pur-tate-datum, canonical root-arrow comparisons.
Existing declarations are retained in this compilation subdivision.
(blueprint: def-pur-canonical-tate-ordinary-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u v a b c d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures.CanonicalTate
open FrobeniusCoefficientTwists

attribute [local instance 5000] integralTowerHasDerivedCategory scalarReductionTargetDerived
attribute [local irreducible] HasDerivedCategory.standard
  integralPull finitePull rationalPull commonPull
  integralProduct finiteProduct rationalProduct commonProduct
  proEtaleRingModulePullback proEtaleRingModuleAdjunction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
/-- Base-change compositor around the actual commuting scheme square.
Source: blueprint root comparison composition
(blueprint: def-pur-canonical-tate-ordinary-naturality). -/
def siteSquare {X Y : Scheme.{u}} (w : X ⟶ Y) (g : Y ⟶ Y) (g' : X ⟶ X)
    (h : g' ≫ w = w ≫ g) :
    proEtaleBaseChange g ⋙ proEtaleBaseChange w ≅
      proEtaleBaseChange w ⋙ proEtaleBaseChange g' :=
  (MorphismProperty.Over.pullbackComp w g).symm ≪≫
    eqToIso (congrArg proEtaleBaseChange h.symm) ≪≫
    MorphismProperty.Over.pullbackComp g' w

private def ordinaryAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f)

section OrdinaryCoefficientSquare

private theorem siteSquare_eq {X Y : Scheme.{u}} (w : X ⟶ Y)
    (g : Y ⟶ Y) (g' : X ⟶ X) (h : g' ≫ w = w ≫ g) :
    siteSquare w g g' h =
      (MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) w g).symm ≪≫
      eqToIso (congrArg proEtaleBaseChange h.symm) ≪≫
      MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g' w := rfl

-- These isomorphisms are used through their categorical API, not their fibre-product data.
attribute [local irreducible] siteSquare MorphismProperty.Over.pullbackComp

variable (R : PurCompactSupport.Coefficients.{u})
  (hc : ∀ {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W),
    R.pull (f ≫ g) = proEtaleRingCompositeCoefficients f g
      (R.ring W) (R.ring V) (R.ring U) (R.pull g) (R.pull f))

private abbrev ordinaryPush {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  proEtaleRingModuleDirectImage f (R.ring Y)
    (R.ring X) (R.pull f)

private theorem presheafIso_cancel {C : Type a} [Category.{b} C]
    {S : Cᵒᵖ ⥤ RingCat.{c}} (N : PresheafOfModules.{d} S)
    {V W : C} (e : V ≅ W) (x : N.obj (op V)) :
    N.map e.hom.op (N.map e.inv.op x) = x := by
  rw [← N.map_comp_apply, ← op_comp, Iso.hom_inv_id]
  exact congrArg (fun t ↦ t.hom x) (N.presheaf.map_id _)

private theorem moduleIso_cancel {X : Scheme.{u}}
    {M N : pbcModules X (R.ring X)} (e : M ≅ N) (V : X.ProEt)
    (x : M.val.obj (op V)) :
    e.inv.val.app (op V) (e.hom.val.app (op V) x) = x := by
  change (e.hom ≫ e.inv).val.app (op V) x = x
  rw [e.hom_inv_id]
  rfl

private theorem ordinaryPushComp_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (d : ordinaryPush R f ⋙ ordinaryPush R g ≅ ordinaryPush R k)
    (c : proEtaleBaseChange k ≅ proEtaleBaseChange g ⋙ proEtaleBaseChange f)
    (hd : ∀ (N : pbcModules X (R.ring X)) (V : Z.ProEt)
      (x : N.val.obj (op ((proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj V)))),
      (d.hom.app N).val.app (op V) x =
        N.val.map (c.hom.app V).op x)
    (N : pbcModules X (R.ring X)) (V : Z.ProEt)
    (x : N.val.obj (op ((proEtaleBaseChange k).obj V))) :
    (d.inv.app N).val.app (op V) x =
      N.val.map (c.inv.app V).op x := by
  have hi := congrArg
    (fun z ↦ (d.inv.app N).val.app (op V) z)
    (hd N V
      (N.val.map (c.inv.app V).op x))
  have hs : N.val.map (c.hom.app V).op
      (N.val.map (c.inv.app V).op x) = x :=
    presheafIso_cancel N.val
      (c.app V) x
  rw [hs] at hi
  have hm : (d.inv.app N).val.app (op V)
      ((d.hom.app N).val.app (op V)
        (N.val.map (c.inv.app V).op x)) =
      N.val.map (c.inv.app V).op x :=
    moduleIso_cancel R (d.app N) V _
  rw [hm] at hi
  exact hi.symm

private theorem doubleIso_section {X Y : Scheme.{u}}
    {F₀ F₁ F₂ : pbcModules X (R.ring X) ⥤ pbcModules Y (R.ring Y)}
    (a : F₀ ≅ F₁) (b : F₁ ≅ F₂) (N : pbcModules X (R.ring X)) (V : Y.ProEt)
    (x : (F₀.obj N).val.obj (op V)) :
    ((a ≪≫ b).hom.app N).val.app (op V) x =
      (b.hom.app N).val.app (op V) ((a.hom.app N).val.app (op V) x) := rfl

private theorem doubleSiteIso_map {X Y : Scheme.{u}}
    {F₀ F₁ F₂ : Y.ProEt ⥤ X.ProEt} (a : F₀ ≅ F₁) (b : F₁ ≅ F₂)
    (N : pbcModules X (R.ring X)) (V : Y.ProEt) (x : N.val.obj (op (F₂.obj V))) :
    N.val.map ((a ≪≫ b).hom.app V).op x =
      N.val.map (a.hom.app V).op (N.val.map (b.hom.app V).op x) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, op_comp, PresheafOfModules.map_comp_apply]

private theorem square_of_comparators {X Y : Scheme.{u}} (w : X ⟶ Y)
    (g : Y ⟶ Y) (g' : X ⟶ X) (k₁ k₂ : X ⟶ Y) (h : k₁ = k₂)
    (a : ordinaryPush R g' ⋙ ordinaryPush R w ≅ ordinaryPush R k₁)
    (b : ordinaryPush R w ⋙ ordinaryPush R g ≅ ordinaryPush R k₂)
    (α : proEtaleBaseChange k₁ ≅ proEtaleBaseChange w ⋙ proEtaleBaseChange g')
    (β : proEtaleBaseChange k₂ ≅ proEtaleBaseChange g ⋙ proEtaleBaseChange w)
    (ha : ∀ (N : pbcModules X (R.ring X)) (V : Y.ProEt)
      (x : N.val.obj (op ((proEtaleBaseChange g').obj ((proEtaleBaseChange w).obj V)))),
      (a.hom.app N).val.app (op V) x = N.val.map (α.hom.app V).op x)
    (hb : ∀ (N : pbcModules X (R.ring X)) (V : Y.ProEt)
      (x : N.val.obj (op ((proEtaleBaseChange w).obj ((proEtaleBaseChange g).obj V)))),
      (b.hom.app N).val.app (op V) x = N.val.map (β.hom.app V).op x) :
    ∀ (N : pbcModules X (R.ring X)) (V : Y.ProEt)
      (x : N.val.obj (op ((proEtaleBaseChange g').obj ((proEtaleBaseChange w).obj V)))),
      ((a ≪≫ eqToIso (congrArg (ordinaryPush R) h) ≪≫ b.symm).hom.app N).val.app
        (op V) x = N.val.map
          ((β.symm ≪≫ eqToIso (congrArg proEtaleBaseChange h.symm) ≪≫ α).hom.app V).op x := by
  subst k₂
  simp only [eqToIso_refl, Iso.refl_trans]
  intro N V x
  calc
    _ = (b.inv.app N).val.app (op V) ((a.hom.app N).val.app (op V) x) :=
      doubleIso_section R a b.symm N V x
    _ = (b.inv.app N).val.app (op V) (N.val.map (α.hom.app V).op x) :=
      congrArg (fun z ↦ (b.inv.app N).val.app (op V) z) (ha N V x)
    _ = N.val.map (β.inv.app V).op (N.val.map (α.hom.app V).op x) :=
      ordinaryPushComp_inv R w g k₁ b β hb N V _
    _ = _ := (doubleSiteIso_map R β.symm α N V x).symm

private theorem isoMap_congr {X Y : Scheme.{u}} {F₀ F₁ : Y.ProEt ⥤ X.ProEt}
    {a b : F₀ ≅ F₁} (h : a = b) (N : pbcModules X (R.ring X)) (V : Y.ProEt)
    (x : N.val.obj (op (F₁.obj V))) :
    N.val.map (a.hom.app V).op x = N.val.map (b.hom.app V).op x :=
  congrArg (fun t : F₀ ≅ F₁ ↦ N.val.map (t.hom.app V).op x) h

private theorem square_exists_of_comparators {X Y : Scheme.{u}} (w : X ⟶ Y)
    (g : Y ⟶ Y) (g' : X ⟶ X) (k₁ k₂ : X ⟶ Y) (h : k₁ = k₂)
    (a : ordinaryPush R g' ⋙ ordinaryPush R w ≅ ordinaryPush R k₁)
    (b : ordinaryPush R w ⋙ ordinaryPush R g ≅ ordinaryPush R k₂)
    (α : proEtaleBaseChange k₁ ≅ proEtaleBaseChange w ⋙ proEtaleBaseChange g')
    (β : proEtaleBaseChange k₂ ≅ proEtaleBaseChange g ⋙ proEtaleBaseChange w)
    (ha : ∀ (N : pbcModules X (R.ring X)) (V : Y.ProEt)
      (x : N.val.obj (op ((proEtaleBaseChange g').obj ((proEtaleBaseChange w).obj V)))),
      (a.hom.app N).val.app (op V) x = N.val.map (α.hom.app V).op x)
    (hb : ∀ (N : pbcModules X (R.ring X)) (V : Y.ProEt)
      (x : N.val.obj (op ((proEtaleBaseChange w).obj ((proEtaleBaseChange g).obj V)))),
      (b.hom.app N).val.app (op V) x = N.val.map (β.hom.app V).op x)
    (c : proEtaleBaseChange g ⋙ proEtaleBaseChange w ≅
      proEtaleBaseChange w ⋙ proEtaleBaseChange g')
    (hs : c = β.symm ≪≫ eqToIso (congrArg proEtaleBaseChange h.symm) ≪≫ α) :
    ∃ d : ordinaryPush R g' ⋙ ordinaryPush R w ≅ ordinaryPush R w ⋙ ordinaryPush R g,
      ∀ (N : pbcModules X (R.ring X)) (V : Y.ProEt)
        (x : N.val.obj (op ((proEtaleBaseChange g').obj ((proEtaleBaseChange w).obj V)))),
        (d.hom.app N).val.app (op V) x = N.val.map (c.hom.app V).op x := by
  refine ⟨a ≪≫ eqToIso (congrArg (ordinaryPush R) h) ≪≫ b.symm, ?_⟩
  intro N V x
  exact (square_of_comparators R w g g' k₁ k₂ h a b α β ha hb N V x).trans
    (isoMap_congr R hs.symm N V x)

private theorem coefficientDirectSquare_exists (R : PurCompactSupport.Coefficients.{u})
    (hc : ∀ {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W),
      R.pull (f ≫ g) = proEtaleRingCompositeCoefficients f g
        (R.ring W) (R.ring V) (R.ring U) (R.pull g) (R.pull f))
    {X Y : Scheme.{u}} (w : X ⟶ Y) (g : Y ⟶ Y) (g' : X ⟶ X)
    (h : g' ≫ w = w ≫ g) :
    ∃ d : ordinaryPush R g' ⋙ ordinaryPush R w ≅ ordinaryPush R w ⋙ ordinaryPush R g,
      ∀ (N : pbcModules X (R.ring X)) (V : Y.ProEt)
        (x : N.val.obj (op ((proEtaleBaseChange g').obj ((proEtaleBaseChange w).obj V)))),
        (d.hom.app N).val.app (op V) x =
          N.val.map ((siteSquare w g g' h).hom.app V).op x := by
  obtain ⟨a, ha, _⟩ := PurCompactSupport.modulePushComposition_existsUnique R g' w (hc g' w)
  obtain ⟨b, hb, _⟩ := PurCompactSupport.modulePushComposition_existsUnique R w g (hc w g)
  exact square_exists_of_comparators R w g g' (g' ≫ w) (w ≫ g) h a b
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g' w)
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) w g)
    ha hb (siteSquare w g g' h) (siteSquare_eq w g g' h)

private theorem conjugateIso_unit_existsUnique
    {C : Type a} [Category.{b} C] {D : Type c} [Category.{d} D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (d : R₂ ≅ R₁) :
    ∃! e : L₁ ≅ L₂, ∀ M,
      adj₁.unit.app M ≫ R₁.map (e.hom.app M) =
        adj₂.unit.app M ≫ d.hom.app (L₂.obj M) := by
  let e := (conjugateIsoEquiv adj₂ adj₁).symm d
  have he : ∀ M, adj₁.unit.app M ≫ R₁.map (e.hom.app M) =
      adj₂.unit.app M ≫ d.hom.app (L₂.obj M) :=
    fun M ↦ (unit_conjugateEquiv_symm adj₂ adj₁ d.hom M).symm
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (adj₁.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact (he' M).trans (he M).symm

-- Keep the left adjoints abstract in the section calculation: their concrete objects
-- involve sheafified tensors, but only the adjunction unit is used here.
private def coefficientSection (R : PurCompactSupport.Coefficients.{u})
    (L : ∀ {U V : Scheme.{u}} (_f : U ⟶ V),
      pbcModules V (R.ring V) ⥤ pbcModules U (R.ring U))
    (adj : ∀ {U V : Scheme.{u}} (f : U ⟶ V), L f ⊣ ordinaryPush R f)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : pbcModules Y (R.ring Y)) (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((L f).obj M).val.obj (op ((proEtaleBaseChange f).obj V)) :=
  ((adj f).unit.app M).val.app (op V) x

private theorem coefficientSquare_existsUnique (R : PurCompactSupport.Coefficients.{u})
    (L : ∀ {U V : Scheme.{u}} (_f : U ⟶ V),
      pbcModules V (R.ring V) ⥤ pbcModules U (R.ring U))
    (adj : ∀ {U V : Scheme.{u}} (f : U ⟶ V), L f ⊣ ordinaryPush R f)
    {X Y : Scheme.{u}} (w : X ⟶ Y)
    (g : Y ⟶ Y) (g' : X ⟶ X) (h : g' ≫ w = w ≫ g)
    (d : ordinaryPush R g' ⋙ ordinaryPush R w ≅ ordinaryPush R w ⋙ ordinaryPush R g)
    (hd : ∀ (N : pbcModules X (R.ring X)) (V : Y.ProEt)
      (x : N.val.obj (op ((proEtaleBaseChange g').obj ((proEtaleBaseChange w).obj V)))),
      (d.hom.app N).val.app (op V) x =
        N.val.map ((siteSquare w g g' h).hom.app V).op x) :
    ∃! e : L g ⋙ L w ≅
        L w ⋙ L g',
      ∀ (M : pbcModules Y (R.ring Y)) (V : Y.ProEt) (x : M.val.obj (op V)),
        (e.hom.app M).val.app (op ((proEtaleBaseChange w).obj
            ((proEtaleBaseChange g).obj V)))
          (coefficientSection R L adj w ((L g).obj M)
            ((proEtaleBaseChange g).obj V) (coefficientSection R L adj g M V x)) =
        ((L g').obj ((L w).obj M)).val.map
          ((siteSquare w g g' h).hom.app V).op
          (coefficientSection R L adj g' ((L w).obj M)
            ((proEtaleBaseChange w).obj V) (coefficientSection R L adj w M V x)) := by
  let adjA := (adj g).comp (adj w)
  let adjB := (adj w).comp (adj g')
  obtain ⟨e, heunit, _⟩ := conjugateIso_unit_existsUnique adjA adjB d
  have he : ∀ (M : pbcModules Y (R.ring Y)) (V : Y.ProEt) (x : M.val.obj (op V)),
      (e.hom.app M).val.app (op ((proEtaleBaseChange w).obj
          ((proEtaleBaseChange g).obj V)))
        (coefficientSection R L adj w ((L g).obj M)
          ((proEtaleBaseChange g).obj V) (coefficientSection R L adj g M V x)) =
      ((L g').obj ((L w).obj M)).val.map
        ((siteSquare w g g' h).hom.app V).op
        (coefficientSection R L adj g' ((L w).obj M)
          ((proEtaleBaseChange w).obj V) (coefficientSection R L adj w M V x)) := by
    intro M V x
    have hu := congrArg (fun z ↦ z.val.app (op V) x)
      (heunit M).symm
    change (d.hom.app ((L g').obj ((L w).obj M))).val.app
      (op V) (coefficientSection R L adj g' ((L w).obj M)
        ((proEtaleBaseChange w).obj V) (coefficientSection R L adj w M V x)) =
      (e.hom.app M).val.app (op ((proEtaleBaseChange w).obj
        ((proEtaleBaseChange g).obj V)))
        (coefficientSection R L adj w ((L g).obj M)
          ((proEtaleBaseChange g).obj V) (coefficientSection R L adj g M V x)) at hu
    exact hu.symm.trans (hd _ V _)
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (adjA.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  exact (he' M V.unop x).trans (he M V.unop x).symm

end OrdinaryCoefficientSquare

/-- The ordinary completed-module square with its double-unit normalization.
Source: blueprint naturality before strict quotient realization
(blueprint: def-pur-canonical-tate-ordinary-naturality).
Proof: conjugate the base-change direct-image compositor under the two composite
module adjunctions. The equality of completed coefficient maps follows by every
finite projection. On a section the resulting map is the indicated double unit,
transported through the site square. The adjunction bijection proves uniqueness. -/
theorem ordinarySquare_existsUnique {X Y : Scheme.{u}} (w : X ⟶ Y)
    (g : Y ⟶ Y) (g' : X ⟶ X) (h : g' ≫ w = w ≫ g) :
    ∃! e : modulePull l E g ⋙ modulePull l E w ≅ modulePull l E w ⋙ modulePull l E g',
      ∀ (M : integralTowerModules l E Y) (V : Y.ProEt) (x : M.val.obj (op V)),
        (e.hom.app M).val.app (op ((proEtaleBaseChange w).obj
            ((proEtaleBaseChange g).obj V)))
          (moduleSection l E w ((modulePull l E g).obj M)
            ((proEtaleBaseChange g).obj V) (moduleSection l E g M V x)) =
        ((modulePull l E g').obj ((modulePull l E w).obj M)).val.map
          ((siteSquare w g g' h).hom.app V).op
          (moduleSection l E g' ((modulePull l E w).obj M)
            ((proEtaleBaseChange w).obj V) (moduleSection l E w M V x)) := by
  obtain ⟨d, hd⟩ := coefficientDirectSquare_exists (PurCompactSupport.completed l E)
    (PurCompactSupport.completedPull_comp l E) w g g' h
  exact coefficientSquare_existsUnique (R := PurCompactSupport.completed l E)
    (L := fun f ↦ modulePull l E f) (adj := fun f ↦ ordinaryAdj l E f) w g g' h d hd

/-- The ordinary square selected by its full adjunction-unit characterization.
Source: blueprint root comparison composition
(blueprint: def-pur-canonical-tate-ordinary-naturality). -/
def ordinarySquare {X Y : Scheme.{u}} (w : X ⟶ Y) (g : Y ⟶ Y) (g' : X ⟶ X)
    (h : g' ≫ w = w ≫ g) :=
  (ordinarySquare_existsUnique l E w g g' h).exists.choose

/-- Ordinary inverse image on actual complexes, before quotient and Roos realization.
Source: blueprint strict integral systems
(blueprint: def-pur-canonical-tate-ordinary-naturality). -/
def ordinaryComplexPull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  letI := proEtaleRingModulePullback_additive f
    ((PurCompactSupport.completed l E).ring Y) ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull f)
  (modulePull l E f).mapHomologicalComplex (.up ℤ)

/-- The unshifted line comparison as an actual chain map on ordinary inverse image.
Source: blueprint strict root-generator maps
(blueprint: def-pur-canonical-tate-ordinary-naturality). -/
def ordinaryComplexLine {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (r : ℕ) :
    (ordinaryComplexPull l E f).obj (integralComplex l E Y r) ≅
      integralComplex l E X r :=
  ((HomologicalComplex.singleMapHomologicalComplex (modulePull l E f) (.up ℤ) 0).app
      (positiveLine l E Y r)) ≪≫
    (HomologicalComplex.single _ (.up ℤ) 0).mapIso (sfOrientationIntegralLineMaps l E f r)

/-- The commuting square on actual complexes.
Source: blueprint strict systems before derived limit
(blueprint: def-pur-canonical-tate-ordinary-naturality). -/
def ordinaryComplexSquare {X Y : Scheme.{u}} (w : X ⟶ Y) (g : Y ⟶ Y) (g' : X ⟶ X)
    (h : g' ≫ w = w ≫ g) :=
  letI := proEtaleRingModulePullback_additive g
    ((PurCompactSupport.completed l E).ring Y) ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).pull g)
  letI := proEtaleRingModulePullback_additive w
    ((PurCompactSupport.completed l E).ring Y) ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull w)
  letI := proEtaleRingModulePullback_additive g'
    ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull g')
  (Functor.mapHomologicalComplexCompIso
    (Iso.refl (modulePull l E g ⋙ modulePull l E w)) (.up ℤ)).symm ≪≫
  NatIso.mapHomologicalComplex (ordinarySquare l E w g g' h) (.up ℤ) ≪≫
  Functor.mapHomologicalComplexCompIso
    (Iso.refl (modulePull l E w ⋙ modulePull l E g')) (.up ℤ)

/-- The actual total-tensor inverse-image comparison before completion.
Source: Stacks 07A4, blueprint tensor generator calculation
(blueprint: def-pur-canonical-tate-ordinary-naturality). -/
def ordinaryComplexMu {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : CochainComplex (integralTowerModules l E Y) ℤ) :
    (ordinaryComplexPull l E f).obj
        ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y)
          (completedIntegralCommRingSheafUnrestricted l E Y)).obj (M, N)) ≅
      (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l E X)).obj
          ((ordinaryComplexPull l E f).obj M, (ordinaryComplexPull l E f).obj N) :=
  (proEtaleTensorPullbackTotalIso f ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f)
    M N).symm

/-- The three equations after an actual functor on the target category.
Source: blueprint equations on whole strict quotient systems
(blueprint: def-pur-canonical-tate-ordinary-naturality). -/
def ImageGeometricLaws {C : Type a} [Category.{b} C] {D : Type c} [Category.{d} D]
    {S : Type a} [Category.{b} S] (F : D ⥤ S)
    (G : C ⥤ C) (G' : D ⥤ D) (W : C ⥤ D) (tensor : D × D ⥤ D)
    (T : ℕ → C) (T' : ℕ → D) (tau : ∀ r, G.obj (T r) ≅ T r)
    (tau' : ∀ r, G'.obj (T' r) ≅ T' r) (t : ∀ r, W.obj (T r) ≅ T' r)
    (comparison : ∀ r, W.obj (G.obj (T r)) ≅ G'.obj (W.obj (T r)))
    (alpha : ∀ r s, tensor.obj (T' r, T' s) ≅ T' (r + s))
    (mu : ∀ M N, G'.obj (tensor.obj (M, N)) ≅ tensor.obj (G'.obj M, G'.obj N)) : Prop :=
  (∀ r, F.map (W.map (tau r).hom ≫ (t r).hom) =
    F.map ((comparison r).hom ≫ G'.map (t r).hom ≫ (tau' r).hom)) ∧
  (∀ r s, F.map ((mu (T' r) (T' s)).hom ≫ tensor.map
    (Prod.mkHom (tau' r).hom (tau' s).hom) ≫ (alpha r s).hom) =
    F.map (G'.map (alpha r s).hom ≫ (tau' (r + s)).hom)) ∧
  ∀ r s, F.map ((mu (T' r) (W.obj (T s))).hom ≫
    tensor.map (Prod.mkHom (tau' r).hom
      ((comparison s).inv ≫ W.map (tau s).hom)) ≫
    tensor.map (Prod.mkHom (𝟙 (T' r)) (t s).hom) ≫ (alpha r s).hom) =
    F.map (G'.map (tensor.map (Prod.mkHom (𝟙 (T' r)) (t s).hom) ≫
      (alpha r s).hom) ≫ (tau' (r + s)).hom)

/-- The geometric identities on whole strict quotient complexes, with all transitions.
Source: blueprint strict quotient-system identities before functorial derived limit
(blueprint: def-pur-canonical-tate-ordinary-naturality). -/
def strictGeometricLaws {X Y : Scheme.{u}} (w : X ⟶ Y) (g : Y ⟶ Y) (g' : X ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (h : g' ≫ w = w ≫ g) : Prop :=
  ImageGeometricLaws ((pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ))
    (ordinaryComplexPull l E g) (ordinaryComplexPull l E g') (ordinaryComplexPull l E w)
    (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l E X))
    (integralComplex l E Y) (integralComplex l E X)
    (ordinaryComplexLine l E g) (ordinaryComplexLine l E g') (ordinaryComplexLine l E w)
    (fun r ↦ (ordinaryComplexSquare l E w g g' h).app (integralComplex l E Y r))
    (integralProductComplex l E X) (ordinaryComplexMu l E g')

/-- Pull one finite root section using the prescribed inverse-image adjunct.
Source: Stacks 03PK, blueprint compatible roots-of-unity systems
(blueprint: def-pur-canonical-tate-ordinary-naturality). -/
def finiteRootSection {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℕ) (V : Y.ProEt)
    (x : (proEtaleRootsOfUnitySheaf Y N).obj.obj (op V)) :
    (proEtaleRootsOfUnitySheaf X N).obj.obj (op ((proEtaleBaseChange f).obj V)) :=
  (proEtaleRootsOfUnityInverseImageMap f N).hom.app
      (op ((proEtaleBaseChange f).obj V))
    (((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
      (proEtaleRootsOfUnitySheaf Y N)).hom.app (op V) x)

/-- Naturality of every level of the actual compatible root inverse systems.
The maps are the recorded inverse-image comparisons, with their power transitions.
Source: blueprint root composition before taking the inverse limit
(blueprint: def-pur-canonical-tate-ordinary-naturality). -/
def rootTowerLaws {X Y : Scheme.{u}} (w : X ⟶ Y) (g : Y ⟶ Y) (g' : X ⟶ X)
    (h : g' ≫ w = w ≫ g) : Prop :=
  ∀ (j : ℕ) (V : Y.ProEt)
    (x : (proEtaleRootsOfUnitySheaf Y (l ^ j)).obj.obj (op V)),
    finiteRootSection w (l ^ j) ((proEtaleBaseChange g).obj V)
      (finiteRootSection g (l ^ j) V x) =
    (proEtaleRootsOfUnitySheaf X (l ^ j)).obj.map
      ((siteSquare w g g' h).hom.app V).op
      (finiteRootSection g' (l ^ j) ((proEtaleBaseChange w).obj V)
        (finiteRootSection w (l ^ j) V x))

end WeilConjectures.CanonicalTate
