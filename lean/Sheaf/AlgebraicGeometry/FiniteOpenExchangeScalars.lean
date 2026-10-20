/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Functor.OfSequence
import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import all Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-!
# Finite open exchange and coefficient restriction

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/
lem-cbc-completed-extension-zero-comparison.proof.md, finite exchange before derived limits;
Stacks Project, Tag 03DI, direct-sum adjunction construction
(blueprint: lem-cbc-finite-open-exchange-scalars).

We use the recorded constant-ring module coordinates and the recorded inverse open-unit
transpose. All complex functors below are termwise, before derived localization.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare

namespace AlgebraicGeometry.ProEtale.StrictTower.FiniteOpenScalars

attribute [local irreducible] Functor.leftAdjoint

private theorem mate_unit_counit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') {G : A ⥤ C} {H : B ⥤ D}
    (p : G ⋙ L' ⟶ L ⋙ H) (d : R ⋙ G ⟶ H ⋙ R')
    (h : (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ p)).natTrans = d) :
    (∀ M : A, G.map (adj.unit.app M) ≫ d.app (L.obj M) =
      adj'.unit.app (G.obj M) ≫ R'.map (p.app M)) ∧
    (∀ N : B, p.app (R.obj N) ≫ H.map (adj.counit.app N) =
      L'.map (d.app N) ≫ adj'.counit.app (H.obj N)) := by
  constructor
  · intro M
    have hu := unit_mateEquiv adj adj' (TwoSquare.mk _ _ _ _ p) M
    change G.map (adj.unit.app M) ≫
      ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ p)).natTrans).app _ =
        adj'.unit.app _ ≫ R'.map (p.app M) at hu
    simpa only [h] using hu
  · intro N
    have hc := mateEquiv_counit adj adj' (TwoSquare.mk _ _ _ _ p) N
    change L'.map
      ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ p)).natTrans.app N) ≫
        adj'.counit.app _ = p.app _ ≫ H.map (adj.counit.app N) at hc
    simpa only [h] using hc.symm

private theorem mate_unit_counit_iso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') {G : A ⥤ C} {H : B ⥤ D}
    (p : G ⋙ L' ⟶ L ⋙ H) (d : R ⋙ G ≅ H ⋙ R')
    (h : (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ p)).natTrans = d.hom) :
    (∀ M : A, adj'.unit.app (G.obj M) ≫ R'.map (p.app M) ≫
        d.inv.app (L.obj M) = G.map (adj.unit.app M)) ∧
    (∀ N : B, p.app (R.obj N) ≫ H.map (adj.counit.app N) =
      L'.map (d.hom.app N) ≫ adj'.counit.app (H.obj N)) := by
  have hh := mate_unit_counit adj adj' p d.hom h
  refine ⟨?_, hh.2⟩
  intro M
  rw [← Category.assoc, ← hh.1 M, Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

private theorem sequence_iso
    {C : Type*} [Category C] {X Y : ℕ → C}
    (s : ∀ n, X (n + 1) ⟶ X n) (t : ∀ n, Y (n + 1) ⟶ Y n)
    (e : ∀ n, X n ≅ Y n)
    (h : ∀ n, s n ≫ (e n).hom = (e (n + 1)).hom ≫ t n) :
    ∃ z : Functor.ofOpSequence s ≅ Functor.ofOpSequence t,
      (∀ n, z.hom.app (Opposite.op n) = (e n).hom) ∧
      (∀ n, z.inv.app (Opposite.op n) = (e n).inv) := by
  let f : Functor.ofOpSequence s ⟶ Functor.ofOpSequence t :=
    NatTrans.ofOpSequence (fun n ↦ (e n).hom) (by
      intro n
      simpa only [Functor.ofOpSequence_map_homOfLE_succ] using h n)
  let g : Functor.ofOpSequence t ⟶ Functor.ofOpSequence s :=
    NatTrans.ofOpSequence (fun n ↦ (e n).inv) (by
      intro n
      simp only [Functor.ofOpSequence_map_homOfLE_succ]
      apply (cancel_epi (e (n + 1)).hom).mp
      rw [← Category.assoc, ← h n]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
        Iso.hom_inv_id_assoc])
  refine ⟨⟨f, g, ?_, ?_⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  · ext n
    exact (e n.unop).hom_inv_id
  · ext n
    exact (e n.unop).inv_hom_id

variable {B C : Type (u + 1)} [CommRing B] [CommRing C]

/-- The map of constant coefficient sheaves induced by a ring homomorphism.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
abbrev coefficientMap (a : B →+* C) (X : Scheme.{u}) :
    coefficients B X ⟶ coefficients C X :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom a)

/-- The underlying ring sheaf of the recorded commutative constant coefficients.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
abbrev ringCoefficients (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients A X)

/-- The same coefficient homomorphism after forgetting commutativity.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
abbrev ringCoefficientMap (a : B →+* C) (X : Scheme.{u}) :
    ringCoefficients B X ⟶ ringCoefficients C X :=
  (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (coefficientMap a X)

/-- The recorded restriction of scalars, leaving the abelian sheaf unchanged.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
abbrev res (a : B →+* C) (X : Scheme.{u}) : Modules C X ⥤ Modules B X :=
  Scheme.proEtaleRingRestrictScalars (coefficientMap a X)

/-- The constant-preserving coefficient maps commute with a coefficient homomorphism.
Source: Stacks Tags 03D2 and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: transpose under the ring-sheaf adjunction. Both maps send each constant b to
the constant section a(b). The constant-presheaf sheafification property gives equality. -/
theorem coefficientSquare (a : B →+* C) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (constantRingIso B f).hom ≫ coefficientMap a Y =
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (coefficientMap a X) ≫
        (constantRingIso C f).hom := by
  exact (Scheme.proEtaleConstantInverseImageMap_naturality f (CommRingCat.ofHom a)).symm

/-- Canonical pullback/scalar identification, the mate of identity on direct-image sections.
Source: Stacks Tags 03D2 and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def pullRes (a : B →+* C) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    res a X ⋙ modulePullback B f ≅ modulePullback C f ⋙ res a Y :=
  @asIso _ _ _ _ (Scheme.proEtaleRingRestrictionPullbackInv f
    (coefficients B X) (coefficients C X) (coefficients B Y) (coefficients C Y)
    (coefficientMap a X) (coefficientMap a Y) (constantRingIso B f) (constantRingIso C f)
    (coefficientSquare a f))
    (Scheme.proEtaleRingRestrictionPullbackInv_isIso f
      (coefficients B X) (coefficients C X) (coefficients B Y) (coefficients C Y)
      (coefficientMap a X) (coefficientMap a Y) (constantRingIso B f) (constantRingIso C f)
      (coefficientSquare a f))

/-- Canonical direct-image/scalar identification, identity on every section.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def pushRes (a : B →+* C) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    moduleDirectImage C f ⋙ res a X ≅ res a Y ⋙ moduleDirectImage B f :=
  Scheme.proEtaleRingRestrictionDirectImage f
    (coefficients B X) (coefficients C X) (coefficients B Y) (coefficients C Y)
    (coefficientMap a X) (coefficientMap a Y) (constantRingIso B f) (constantRingIso C f)
    (coefficientSquare a f)

set_option backward.isDefEq.respectTransparency false in
private theorem pullRes_mate (a : B →+* C) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (mateEquiv (Scheme.proEtaleRingModuleAdjunction f
        (coefficients C X) (coefficients C Y) (constantRingIso C f))
      (Scheme.proEtaleRingModuleAdjunction f
        (coefficients B X) (coefficients B Y) (constantRingIso B f))
      (TwoSquare.mk _ _ _ _ (pullRes a f).hom)).natTrans = (pushRes a f).hom := by
  simpa only [pullRes, pushRes, asIso_hom] using
    (Scheme.restrictionPullback_mate f
      (coefficients B X) (coefficients C X) (coefficients B Y) (coefficients C Y)
      (coefficientMap a X) (coefficientMap a Y) (constantRingIso B f) (constantRingIso C f)
      (coefficientSquare a f))

attribute [local irreducible] Scheme.proEtaleRingModuleAdjunction Scheme.proEtaleRingModulePullback
 Scheme.proEtaleRingRestrictionPullbackApp

attribute [local irreducible] pullRes pushRes moduleGComp moduleRComp

set_option backward.isDefEq.respectTransparency false in
private theorem pullRes_compositor (a : B →+* C)
    {Z Y X : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X) :
    Functor.whiskerLeft (res a X) (moduleGComp B f g).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (pullRes a g).hom (modulePullback B f) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (modulePullback C g) (pullRes a f).hom ≫
        (Functor.associator _ _ _).inv =
      (pullRes a (f ≫ g)).hom ≫
        Functor.whiskerRight (moduleGComp C f g).hom (res a Z) := by
  let adj (A : Type (u + 1)) [CommRing A] {V W : Scheme.{u}} (k : V ⟶ W) :=
    Scheme.proEtaleRingModuleAdjunction k
      (coefficients A W) (coefficients A V) (constantRingIso A k)
  let s := TwoSquare.mk _ _ _ _ (pullRes a g).hom
  let t := TwoSquare.mk _ _ _ _ (pullRes a f).hom
  let q := TwoSquare.mk _ _ _ _ (pullRes a (f ≫ g)).hom
  have h₁ := mateEquiv_conjugateEquiv_vcomp
    ((adj C g).comp (adj C f)) ((adj B g).comp (adj B f)) (adj B (f ≫ g))
    (s ≫ᵥ t) (moduleGComp B f g).hom
  have h₂ := conjugateEquiv_mateEquiv_vcomp
    ((adj C g).comp (adj C f)) (adj C (f ≫ g)) (adj B (f ≫ g))
    (moduleGComp C f g).hom q
  have hc A [CommRing A] :
      conjugateEquiv ((adj A g).comp (adj A f)) (adj A (f ≫ g))
        (moduleGComp A f g).hom = (moduleRComp A f g).hom := by
    unfold moduleGComp
    exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _
  have hmate : (mateEquiv (adj C g) (adj B g) s).natTrans = (pushRes a g).hom :=
    pullRes_mate a g
  have hmate' : (mateEquiv (adj C f) (adj B f) t).natTrans = (pushRes a f).hom :=
    pullRes_mate a f
  have hmate'' : (mateEquiv (adj C (f ≫ g)) (adj B (f ≫ g)) q).natTrans =
      (pushRes a (f ≫ g)).hom := pullRes_mate a (f ≫ g)
  apply congrArg TwoSquare.natTrans
    ((mateEquiv ((adj C g).comp (adj C f)) (adj B (f ≫ g))).injective ?_)
  change (mateEquiv ((adj C g).comp (adj C f)) (adj B (f ≫ g)))
      ((s ≫ᵥ t).whiskerRight (moduleGComp B f g).hom) =
    (mateEquiv ((adj C g).comp (adj C f)) (adj B (f ≫ g)))
      (q.whiskerLeft (moduleGComp C f g).hom)
  rw [h₁, h₂, mateEquiv_hcomp]
  apply TwoSquare.ext
  intro M
  simp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, hc, hmate, hmate', hmate'']
  change (pushRes a g).hom.app ((moduleDirectImage C f).obj M) ≫
      (moduleDirectImage B g).map ((pushRes a f).hom.app M) ≫
      (moduleRComp B f g).hom.app ((res a Z).obj M) =
    (res a X).map ((moduleRComp C f g).hom.app M) ≫
      (pushRes a (f ≫ g)).hom.app M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext m
  have hd (A : Type (u + 1)) [CommRing A] (N : Modules A Z)
      (n : ((moduleDirectImage A f ⋙ moduleDirectImage A g).obj N).val.obj W) :
      ((moduleRComp A f g).hom.app N).val.app W n =
        N.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app W.unop).op n :=
    by
      unfold moduleRComp
      exact (Classical.choose_spec (moduleRComp_existsUnique A f g)).1 N W.unop n
  have hp {V T : Scheme.{u}} (k : V ⟶ T) (N : Modules C V) (Q : T.ProEtᵒᵖ)
      (n : N.val.obj ((Scheme.proEtaleBaseChange k).op.obj Q)) :
      ((pushRes a k).hom.app N).val.app Q n = n := by
    unfold pushRes
    exact (Classical.choose_spec (Scheme.proEtaleRingRestrictionDirectImage_existsUnique k
      (coefficients B T) (coefficients C T) (coefficients B V) (coefficients C V)
      (coefficientMap a T) (coefficientMap a V) (constantRingIso B k) (constantRingIso C k)
      (coefficientSquare a k))).1 N Q n
  change ((moduleRComp B f g).hom.app ((res a Z).obj M)).val.app W
      (((pushRes a f).hom.app M).val.app
        ((Scheme.proEtaleBaseChange g).op.obj W)
        (((pushRes a g).hom.app ((moduleDirectImage C f).obj M)).val.app W m)) =
    ((pushRes a (f ≫ g)).hom.app M).val.app W
      (((moduleRComp C f g).hom.app M).val.app W m)
  simp only [hp, hd]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem pullRes_compositor_app (a : B →+* C)
    {Z Y X : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X) (M : Modules C X) :
    (moduleGComp B f g).hom.app ((res a X).obj M) ≫
        (modulePullback B f).map ((pullRes a g).hom.app M) ≫
        (pullRes a f).hom.app ((modulePullback C g).obj M) =
      (pullRes a (f ≫ g)).hom.app M ≫
        (res a Z).map ((moduleGComp C f g).hom.app M) := by
  have hh := congr_app (pullRes_compositor a f g) M
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] using hh

set_option backward.isDefEq.respectTransparency false in
private theorem pullRes_compositor_inv (a : B →+* C)
    {Z Y X : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X) (M : Modules C X) :
    (modulePullback B f).map ((pullRes a g).hom.app M) ≫
        (pullRes a f).hom.app ((modulePullback C g).obj M) ≫
        (res a Z).map ((moduleGComp C f g).inv.app M) =
      (moduleGComp B f g).inv.app ((res a X).obj M) ≫
        (pullRes a (f ≫ g)).hom.app M := by
  apply (cancel_epi ((moduleGComp B f g).hom.app ((res a X).obj M))).mp
  slice_lhs 1 3 => rw [pullRes_compositor_app]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app,
    Iso.hom_inv_id_app_assoc]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem pullRes_congr (a : B →+* C) {Y X : Scheme.{u}}
    {f g : Y ⟶ X} (h : f = g) (M : Modules C X) :
    (eqToIso (congrArg (modulePullback B) h)).inv.app ((res a X).obj M) ≫
        (pullRes a f).hom.app M =
      (pullRes a g).hom.app M ≫
        (res a Y).map ((eqToIso (congrArg (modulePullback C) h)).inv.app M) := by
  subst g
  simp only [eqToIso_refl, Iso.refl_inv, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact (Category.comp_id _).symm

attribute [local irreducible] moduleSquareG

private theorem square_inv_app (A : Type (u + 1)) [CommRing A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (h : gU ≫ j = j' ≫ g) (M : Modules A X) :
    (moduleSquareG A gU j' j g h).inv.app M =
      (moduleGComp A gU j).inv.app M ≫
        (eqToIso (congrArg (modulePullback A) h.symm)).inv.app M ≫
        (moduleGComp A j' g).hom.app M := by
  simpa only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Category.assoc] using
    congrArg (fun e ↦ e.inv.app M) (moduleSquareG_eq A gU j' j g h)

private theorem pullRes_square_formula (a : B →+* C)
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (h : gU ≫ j = j' ≫ g) (M : Modules C X) :
    (modulePullback B gU).map ((pullRes a j).hom.app M) ≫
        (pullRes a gU).hom.app ((modulePullback C j).obj M) ≫
        (res a U').map (((moduleGComp C gU j).inv.app M ≫
          (eqToIso (congrArg (modulePullback C) h.symm)).inv.app M ≫
          (moduleGComp C j' g).hom.app M)) =
      ((moduleGComp B gU j).inv.app ((res a X).obj M) ≫
        (eqToIso (congrArg (modulePullback B) h.symm)).inv.app ((res a X).obj M) ≫
        (moduleGComp B j' g).hom.app ((res a X).obj M)) ≫
        (modulePullback B j').map ((pullRes a g).hom.app M) ≫
        (pullRes a j').hom.app ((modulePullback C g).obj M) := by
  calc
    _ = (moduleGComp B gU j).inv.app ((res a X).obj M) ≫
        (pullRes a (gU ≫ j)).hom.app M ≫
        (res a U').map ((eqToIso (congrArg (modulePullback C) h.symm)).inv.app M) ≫
        (res a U').map ((moduleGComp C j' g).hom.app M) := by
      simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using
        congrArg (fun t ↦ t ≫
          (res a U').map ((eqToIso (congrArg (modulePullback C) h.symm)).inv.app M) ≫
          (res a U').map ((moduleGComp C j' g).hom.app M))
          (pullRes_compositor_inv a gU j M)
    _ = (moduleGComp B gU j).inv.app ((res a X).obj M) ≫
        (eqToIso (congrArg (modulePullback B) h.symm)).inv.app ((res a X).obj M) ≫
        (pullRes a (j' ≫ g)).hom.app M ≫
        (res a U').map ((moduleGComp C j' g).hom.app M) := by
      simpa only [Category.assoc] using
        congrArg (fun t ↦ (moduleGComp B gU j).inv.app ((res a X).obj M) ≫ t ≫
          (res a U').map ((moduleGComp C j' g).hom.app M))
          (pullRes_congr a h.symm M).symm
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun t ↦ (moduleGComp B gU j).inv.app ((res a X).obj M) ≫
          (eqToIso (congrArg (modulePullback B) h.symm)).inv.app ((res a X).obj M) ≫ t)
          (pullRes_compositor_app a j' g M).symm


private theorem pullRes_square (a : B →+* C)
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (h : gU ≫ j = j' ≫ g) (M : Modules C X) :
    (modulePullback B gU).map ((pullRes a j).hom.app M) ≫
        (pullRes a gU).hom.app ((modulePullback C j).obj M) ≫
        (res a U').map ((moduleSquareG C gU j' j g h).inv.app M) =
      (moduleSquareG B gU j' j g h).inv.app ((res a X).obj M) ≫
        (modulePullback B j').map ((pullRes a g).hom.app M) ≫
        (pullRes a j').hom.app ((modulePullback C g).obj M) := by
  have hc := congrArg (fun t ↦
    (modulePullback B gU).map ((pullRes a j).hom.app M) ≫
      (pullRes a gU).hom.app ((modulePullback C j).obj M) ≫ (res a U').map t)
    (square_inv_app C gU j' j g h M)
  have hb := congrArg (fun t ↦ t ≫
    (modulePullback B j').map ((pullRes a g).hom.app M) ≫
      (pullRes a j').hom.app ((modulePullback C g).obj M))
    (square_inv_app B gU j' j g h ((res a X).obj M))
  exact hc.trans ((pullRes_square_formula a gU j' j g h M).trans hb.symm)

/-- The scalar comparison for extension is the mate of the inverse pullback comparison.
Source: Stacks Tag 03DI, direct-sum adjunction construction
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def openResMap (a : B →+* C) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    res a U ⋙ moduleJ B j ⟶ moduleJ C j ⋙ res a X :=
  (mateEquiv (moduleJAdj C j) (moduleJAdj B j)).symm (pullRes a j).inv

set_option backward.isDefEq.respectTransparency false

private theorem inverse_path
    {D : Type*} [Category D] {A B C E F : D}
    (q : A ≅ B) (p : A ≅ C) (r : C ≅ E) (s : E ≅ F) (t : B ≅ F)
    (h : q.inv ≫ p.hom ≫ r.hom ≫ s.hom = t.hom) :
    r.inv ≫ p.inv ≫ q.hom = s.hom ≫ t.inv := by
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using
    (congrArg (fun f ↦ r.inv ≫ p.inv ≫ q.hom ≫ f ≫ t.inv) h).symm

private theorem invert_outer
    {D : Type*} [Category D] {A B C E : D}
    (b : A ≅ B) (c : C ≅ E) {s : B ⟶ E} {r : A ⟶ C}
    (h : b.hom ≫ s = r ≫ c.hom) : b.inv ≫ r = s ≫ c.inv := by
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using
    (congrArg (fun t ↦ b.inv ≫ t ≫ c.inv) h).symm

private theorem inverse_of_square
    {D : Type*} [Category D] {A B C E F : D}
    (b : A ≅ B) (p : B ≅ C) (c : E ≅ F) {s : C ⟶ F} {r : A ⟶ E}
    (h : b.hom ≫ p.hom ≫ s = r ≫ c.hom) : p.inv ≫ b.inv ≫ r = s ≫ c.inv := by
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using
    (congrArg (fun t ↦ p.inv ≫ b.inv ≫ t ≫ c.inv) h).symm

private theorem invert_cube
    {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type*}
    [Category A₁] [Category A₂] [Category A₃] [Category A₄]
    [Category B₁] [Category B₂] [Category B₃] [Category B₄]
    {L₁ : A₁ ⥤ B₁} {L₂ : A₂ ⥤ B₂} {L₃ : A₃ ⥤ B₃} {L₄ : A₄ ⥤ B₄}
    {G₁₂ : A₁ ⥤ A₂} {G₂₄ : A₂ ⥤ A₄} {G₁₃ : A₁ ⥤ A₃} {G₃₄ : A₃ ⥤ A₄}
    {H₁₂ : B₁ ⥤ B₂} {H₂₄ : B₂ ⥤ B₄} {H₁₃ : B₁ ⥤ B₃} {H₃₄ : B₃ ⥤ B₄}
    (w₁₂ : G₁₂ ⋙ L₂ ≅ L₁ ⋙ H₁₂) (w₂₄ : G₂₄ ⋙ L₄ ≅ L₂ ⋙ H₂₄)
    (w₁₃ : G₁₃ ⋙ L₃ ≅ L₁ ⋙ H₁₃) (w₃₄ : G₃₄ ⋙ L₄ ≅ L₃ ⋙ H₃₄)
    (s : G₁₂ ⋙ G₂₄ ≅ G₁₃ ⋙ G₃₄) (t : H₁₂ ⋙ H₂₄ ≅ H₁₃ ⋙ H₃₄)
    (h : ((TwoSquare.mk _ _ _ _ w₁₂.hom) ≫ₕ
        (TwoSquare.mk _ _ _ _ w₂₄.hom)).whiskerBottom t.hom =
      ((TwoSquare.mk _ _ _ _ w₁₃.hom) ≫ₕ
        (TwoSquare.mk _ _ _ _ w₃₄.hom)).whiskerTop s.hom) :
    ((TwoSquare.mk _ _ _ _ w₁₂.inv) ≫ᵥ
        (TwoSquare.mk _ _ _ _ w₂₄.inv)).whiskerLeft s.hom =
      ((TwoSquare.mk _ _ _ _ w₁₃.inv) ≫ᵥ
        (TwoSquare.mk _ _ _ _ w₃₄.inv)).whiskerRight t.hom := by
  apply TwoSquare.ext
  intro M
  have he := congrArg (fun w ↦ w.natTrans.app M) h
  simp only [TwoSquare.hComp, TwoSquare.whiskerBottom, TwoSquare.whiskerTop,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] at he
  simp only [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id]
  simpa only [Functor.mapIso_inv, Iso.app_inv, Iso.trans_inv, Category.assoc] using
    (inverse_of_square (w₂₄.app (G₁₂.obj M)) (H₂₄.mapIso (w₁₂.app M))
      ((w₃₄.app (G₁₃.obj M)) ≪≫ H₃₄.mapIso (w₁₃.app M))
      (by simpa only [Functor.mapIso_hom, Iso.app_hom, Iso.trans_hom, Category.assoc]
        using he))

private theorem forward_of_inverse
    {D : Type*} [Category D] {A B C E : D}
    (b : A ≅ B) (c : C ≅ E) {s : A ⟶ C} {t : B ⟶ E}
    (h : t ≫ c.inv = b.inv ≫ s) : s ≫ c.hom = b.hom ≫ t := by
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.hom_inv_id_assoc] using
    (congrArg (fun f ↦ b.hom ≫ f ≫ c.hom) h).symm

private theorem semilinear_square
    {A D : Type*} [Category A] [Category D] {L R : A ⥤ D}
    (b : L ≅ R) {M N : A} (f : M ⟶ N) {S T : D} (c : S ≅ T)
    (s : L.obj N ⟶ S) (t : R.obj N ⟶ T)
    (h : s ≫ c.hom = b.hom.app N ≫ t) :
    L.map f ≫ s ≫ c.hom = b.hom.app M ≫ R.map f ≫ t ∧
      R.map f ≫ t ≫ c.inv = b.inv.app M ≫ L.map f ≫ s := by
  have hi := forward_of_inverse (b.app N).symm c.symm h
  simp only [Iso.symm_hom, Iso.app_inv] at hi
  constructor
  · rw [h, ← Category.assoc, b.hom.naturality f, Category.assoc]
  · rw [hi, ← Category.assoc, b.inv.naturality f, Category.assoc]

private theorem mate_top
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') {G G' : A ⥤ C} {H : B ⥤ D}
    (w : TwoSquare G L L' H) (a : G' ⟶ G) :
    mateEquiv adj adj' (w.whiskerTop a) =
      (mateEquiv adj adj' w).whiskerRight a := by
  ext X
  simp only [mateEquiv_apply, TwoSquare.whiskerTop, TwoSquare.whiskerRight,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app, Category.id_comp,
    CategoryTheory.Functor.map_comp, Category.assoc]
  repeat first | erw [Category.id_comp] | erw [Category.comp_id]
  simp only [Functor.comp_map]
  rw [← Category.assoc]
  erw [adj'.unit_naturality (a.app (R.obj X))]
  simp only [Category.assoc]
  rfl
private theorem mate_bottom
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') {G : A ⥤ C} {H H' : B ⥤ D}
    (w : TwoSquare G L L' H) (a : H ⟶ H') :
    mateEquiv adj adj' (w.whiskerBottom a) =
      (mateEquiv adj adj' w).whiskerLeft a := by
  ext X
  simp only [mateEquiv_apply, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app, Category.id_comp,
    CategoryTheory.Functor.map_comp, Category.assoc]
  repeat first | erw [Category.id_comp] | erw [Category.comp_id]
  simp only [Functor.comp_map]
  rw [← R'.map_comp, ← a.naturality]
  simp only [R'.map_comp]
  rfl
private theorem isIso_of_hComp_cube
    {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type*}
    [Category A₁] [Category A₂] [Category A₃] [Category A₄]
    [Category B₁] [Category B₂] [Category B₃] [Category B₄]
    {L₁ : A₁ ⥤ B₁} {L₂ : A₂ ⥤ B₂} {L₃ : A₃ ⥤ B₃} {L₄ : A₄ ⥤ B₄}
    {G₁₂ : A₁ ⥤ A₂} {G₂₄ : A₂ ⥤ A₄} {G₁₃ : A₁ ⥤ A₃} {G₃₄ : A₃ ⥤ A₄}
    {H₁₂ : B₁ ⥤ B₂} {H₂₄ : B₂ ⥤ B₄} {H₁₃ : B₁ ⥤ B₃} {H₃₄ : B₃ ⥤ B₄}
    (w₁₂ : TwoSquare G₁₂ L₁ L₂ H₁₂) (w₂₄ : TwoSquare G₂₄ L₂ L₄ H₂₄)
    (w₁₃ : TwoSquare G₁₃ L₁ L₃ H₁₃) (w₃₄ : TwoSquare G₃₄ L₃ L₄ H₃₄)
    [H₂₄.ReflectsIsomorphisms] [IsIso w₂₄.natTrans]
    [IsIso w₁₃.natTrans] [IsIso w₃₄.natTrans]
    (s : G₁₂ ⋙ G₂₄ ≅ G₁₃ ⋙ G₃₄) (t : H₁₂ ⋙ H₂₄ ≅ H₁₃ ⋙ H₃₄)
    (h : (w₁₂ ≫ₕ w₂₄).whiskerBottom t.hom = (w₁₃ ≫ₕ w₃₄).whiskerTop s.hom) :
    IsIso w₁₂.natTrans := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have he := congrArg (fun z ↦ z.natTrans.app M) h
  simp only [TwoSquare.hComp, TwoSquare.whiskerBottom, TwoSquare.whiskerTop,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, TwoSquare.natTrans, Category.assoc] at he
  have hi : IsIso (w₂₄.natTrans.app (G₁₂.obj M) ≫ H₂₄.map (w₁₂.natTrans.app M) ≫
      t.hom.app (L₁.obj M)) := by
    rw [he]
    infer_instance
  have := IsIso.of_isIso_comp_left (w₂₄.natTrans.app (G₁₂.obj M))
    (H₂₄.map (w₁₂.natTrans.app M) ≫ t.hom.app (L₁.obj M))
  have := IsIso.of_isIso_comp_right (H₂₄.map (w₁₂.natTrans.app M))
    (t.hom.app (L₁.obj M))
  exact isIso_of_reflects_iso (w₁₂.natTrans.app M) H₂₄

private theorem inverse_cube
    {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type*}
    [Category A₁] [Category A₂] [Category A₃] [Category A₄]
    [Category B₁] [Category B₂] [Category B₃] [Category B₄]
    {L₁ : A₁ ⥤ B₁} {R₁ : B₁ ⥤ A₁} {L₂ : A₂ ⥤ B₂} {R₂ : B₂ ⥤ A₂}
    {L₃ : A₃ ⥤ B₃} {R₃ : B₃ ⥤ A₃} {L₄ : A₄ ⥤ B₄} {R₄ : B₄ ⥤ A₄}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    {G₁₂ : A₁ ⥤ A₂} {G₂₄ : A₂ ⥤ A₄} {G₁₃ : A₁ ⥤ A₃} {G₃₄ : A₃ ⥤ A₄}
    {H₁₂ : B₁ ⥤ B₂} {H₂₄ : B₂ ⥤ B₄} {H₁₃ : B₁ ⥤ B₃} {H₃₄ : B₃ ⥤ B₄}
    (w₁₂ : TwoSquare R₁ H₁₂ G₁₂ R₂) (w₂₄ : TwoSquare R₂ H₂₄ G₂₄ R₄)
    (w₁₃ : TwoSquare R₁ H₁₃ G₁₃ R₃) (w₃₄ : TwoSquare R₃ H₃₄ G₃₄ R₄)
    (s : G₁₂ ⋙ G₂₄ ⟶ G₁₃ ⋙ G₃₄) (t : H₁₂ ⋙ H₂₄ ⟶ H₁₃ ⋙ H₃₄)
    (h : (w₁₂ ≫ᵥ w₂₄).whiskerLeft t = (w₁₃ ≫ᵥ w₃₄).whiskerRight s) :
    (((mateEquiv a₁ a₂).symm w₁₂) ≫ₕ ((mateEquiv a₂ a₄).symm w₂₄)).whiskerBottom t =
      (((mateEquiv a₁ a₃).symm w₁₃) ≫ₕ ((mateEquiv a₃ a₄).symm w₃₄)).whiskerTop s := by
  apply (mateEquiv a₁ a₄).injective
  rw [mate_bottom, mate_top, mateEquiv_vcomp a₁ a₂ a₄, mateEquiv_vcomp a₁ a₃ a₄]
  simpa only [Equiv.apply_symm_apply] using h

private theorem inverted_mate_cube
    {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type*}
    [Category A₁] [Category A₂] [Category A₃] [Category A₄]
    [Category B₁] [Category B₂] [Category B₃] [Category B₄]
    {L₁ : A₁ ⥤ B₁} {R₁ : B₁ ⥤ A₁} {L₂ : A₂ ⥤ B₂} {R₂ : B₂ ⥤ A₂}
    {L₃ : A₃ ⥤ B₃} {R₃ : B₃ ⥤ A₃} {L₄ : A₄ ⥤ B₄} {R₄ : B₄ ⥤ A₄}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    {G₁₂ : A₁ ⥤ A₂} {G₂₄ : A₂ ⥤ A₄} {G₁₃ : A₁ ⥤ A₃} {G₃₄ : A₃ ⥤ A₄}
    {H₁₂ : B₁ ⥤ B₂} {H₂₄ : B₂ ⥤ B₄} {H₁₃ : B₁ ⥤ B₃} {H₃₄ : B₃ ⥤ B₄}
    (p₁₂ : G₁₂ ⋙ L₂ ≅ L₁ ⋙ H₁₂) (p₂₄ : G₂₄ ⋙ L₄ ≅ L₂ ⋙ H₂₄)
    (p₁₃ : G₁₃ ⋙ L₃ ≅ L₁ ⋙ H₁₃) (p₃₄ : G₃₄ ⋙ L₄ ≅ L₃ ⋙ H₃₄)
    (w₁₂ : TwoSquare R₁ H₁₂ G₁₂ R₂) (w₂₄ : TwoSquare R₂ H₂₄ G₂₄ R₄)
    (w₁₃ : TwoSquare R₁ H₁₃ G₁₃ R₃) (w₃₄ : TwoSquare R₃ H₃₄ G₃₄ R₄)
    (h₁₂ : (mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ p₁₂.hom)).natTrans = w₁₂.natTrans)
    (h₂₄ : (mateEquiv a₂ a₄ (TwoSquare.mk _ _ _ _ p₂₄.hom)).natTrans = w₂₄.natTrans)
    (h₁₃ : (mateEquiv a₁ a₃ (TwoSquare.mk _ _ _ _ p₁₃.hom)).natTrans = w₁₃.natTrans)
    (h₃₄ : (mateEquiv a₃ a₄ (TwoSquare.mk _ _ _ _ p₃₄.hom)).natTrans = w₃₄.natTrans)
    (s : G₁₂ ⋙ G₂₄ ≅ G₁₃ ⋙ G₃₄) (t : H₁₂ ⋙ H₂₄ ≅ H₁₃ ⋙ H₃₄)
    (h : (w₁₂ ≫ᵥ w₂₄).whiskerLeft t.hom = (w₁₃ ≫ᵥ w₃₄).whiskerRight s.hom) :
    ((TwoSquare.mk _ _ _ _ p₁₂.inv) ≫ᵥ
        (TwoSquare.mk _ _ _ _ p₂₄.inv)).whiskerLeft s.hom =
      ((TwoSquare.mk _ _ _ _ p₁₃.inv) ≫ᵥ
        (TwoSquare.mk _ _ _ _ p₃₄.inv)).whiskerRight t.hom := by
  have e₁₂ : mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ p₁₂.hom) = w₁₂ := by
    apply TwoSquare.ext; intro M; exact congrArg (fun z ↦ z.app M) h₁₂
  have e₂₄ : mateEquiv a₂ a₄ (TwoSquare.mk _ _ _ _ p₂₄.hom) = w₂₄ := by
    apply TwoSquare.ext; intro M; exact congrArg (fun z ↦ z.app M) h₂₄
  have e₁₃ : mateEquiv a₁ a₃ (TwoSquare.mk _ _ _ _ p₁₃.hom) = w₁₃ := by
    apply TwoSquare.ext; intro M; exact congrArg (fun z ↦ z.app M) h₁₃
  have e₃₄ : mateEquiv a₃ a₄ (TwoSquare.mk _ _ _ _ p₃₄.hom) = w₃₄ := by
    apply TwoSquare.ext; intro M; exact congrArg (fun z ↦ z.app M) h₃₄
  apply invert_cube p₁₂ p₂₄ p₁₃ p₃₄ s t
  have hh := inverse_cube a₁ a₂ a₃ a₄ w₁₂ w₂₄ w₁₃ w₃₄ s.hom t.hom h
  rw [← e₁₂, ← e₂₄, ← e₁₃, ← e₃₄] at hh
  simpa only [Equiv.symm_apply_apply] using hh

private theorem inverseMate_isIso_of_cube
    {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type*}
    [Category A₁] [Category A₂] [Category A₃] [Category A₄]
    [Category B₁] [Category B₂] [Category B₃] [Category B₄]
    {L₁ : A₁ ⥤ B₁} {R₁ : B₁ ⥤ A₁} {L₂ : A₂ ⥤ B₂} {R₂ : B₂ ⥤ A₂}
    {L₃ : A₃ ⥤ B₃} {R₃ : B₃ ⥤ A₃} {L₄ : A₄ ⥤ B₄} {R₄ : B₄ ⥤ A₄}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    {G₁₂ : A₁ ⥤ A₂} {G₂₄ : A₂ ⥤ A₄} {G₁₃ : A₁ ⥤ A₃} {G₃₄ : A₃ ⥤ A₄}
    {H₁₂ : B₁ ⥤ B₂} {H₂₄ : B₂ ⥤ B₄} {H₁₃ : B₁ ⥤ B₃} {H₃₄ : B₃ ⥤ B₄}
    [G₂₄.IsEquivalence] [H₂₄.IsEquivalence]
    [G₁₃.IsEquivalence] [H₁₃.IsEquivalence]
    (w : TwoSquare R₁ H₁₂ G₁₂ R₂) (b : R₂ ⋙ G₂₄ ≅ H₂₄ ⋙ R₄)
    (c : R₁ ⋙ G₁₃ ≅ H₁₃ ⋙ R₃) (d : TwoSquare R₃ H₃₄ G₃₄ R₄)
    [IsIso (((mateEquiv a₃ a₄).symm d).natTrans)]
    (s : G₁₂ ⋙ G₂₄ ≅ G₁₃ ⋙ G₃₄) (t : H₁₂ ⋙ H₂₄ ≅ H₁₃ ⋙ H₃₄)
    (h : (w ≫ᵥ b.hom).whiskerLeft t.hom = (c.hom ≫ᵥ d).whiskerRight s.hom) :
    IsIso (((mateEquiv a₁ a₂).symm w).natTrans) := by
  have := isIso_inverseMate_of_equivalences a₂ a₄ b
  have := isIso_inverseMate_of_equivalences a₁ a₃ c
  exact isIso_of_hComp_cube
    ((mateEquiv a₁ a₂).symm w) ((mateEquiv a₂ a₄).symm b.hom)
    ((mateEquiv a₁ a₃).symm c.hom) ((mateEquiv a₃ a₄).symm d) s t
    (inverse_cube a₁ a₂ a₃ a₄ w b.hom c.hom d s.hom t.hom h)


private noncomputable def scalarDirectModel (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    moduleDirectImage A f ⋙ scalarSectionsAt Y A ≅
      scalarSectionsAt X A ⋙ lowerStar (ModuleCat.{u + 1} A) f :=
  scalarDirectImageIso (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y)
    (Scheme.proEtaleBaseChange f) A _ _ _ _ _ (scalarDirectImage_unit f A)
private theorem fixedRestriction_mate (a : B →+* C)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (mateEquiv (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} C) j)
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) j)
      (TwoSquare.mk (Sheaf.restrictScalars (Scheme.ProEt.topology X) a) _ _
        (Sheaf.restrictScalars (Scheme.ProEt.topology U) a) (eqToHom (by rfl)))).natTrans =
        𝟙 (lowerStar (ModuleCat.{u + 1} C) j ⋙
          Sheaf.restrictScalars (Scheme.ProEt.topology X) a) := by
  ext M W x
  simp only [mateEquiv_apply, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    eqToHom_refl, NatTrans.id_app, Category.id_comp]
  repeat first | erw [Category.id_comp] | erw [Category.comp_id]
  simp only [Functor.comp_map]
  exact congrArg (fun z ↦ (z.hom.app W).hom x)
    ((openImmersionRestrictionLowerStarAdjunction
      (ModuleCat.{u + 1} C) j).right_triangle_components M)

private noncomputable def scalarRestrictionAt (a : B →+* C) (X : Scheme.{u}) :
    res a X ⋙ scalarSectionsAt X B ≅ scalarSectionsAt X C ⋙
      Sheaf.restrictScalars (Scheme.ProEt.topology X) a :=
  scalarRestrictionIso (Scheme.ProEt.topology X) a _ _ _ _ _ (scalarChange_unit X a)

private theorem scalarDirectModel_apply (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) (M : Modules A U) (W : X.ProEtᵒᵖ)
    (x : M.val.obj ((Scheme.proEtaleBaseChange j).op.obj W)) :
    (((scalarDirectModel A j).hom.app M).hom.app W).hom x = x := by
  rfl

private theorem scalarRestrictionAt_apply (a : B →+* C) (X : Scheme.{u})
    (M : Modules C X) (W : X.ProEtᵒᵖ) (x : M.val.obj W) :
    (((scalarRestrictionAt a X).hom.app M).hom.app W).hom x = x := by
  rfl

attribute [local irreducible] scalarDirectModel scalarRestrictionAt

private noncomputable def scalarPullModel (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    scalarSectionsAt X A ⋙ openImmersionRestriction (ModuleCat.{u + 1} A) j ≅
      modulePullback A j ⋙ scalarSectionsAt U A := by
  have := scalarSectionsAt_equiv X A
  have := scalarSectionsAt_equiv U A
  let adj := Scheme.proEtaleRingModuleAdjunction j
    (coefficients A X) (coefficients A U) (constantRingIso A j)
  have := isIso_inverseMate_of_equivalences adj
    (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j)
    (scalarDirectModel A j)
  exact asIso ((mateEquiv adj
    (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j)).symm
      (scalarDirectModel A j).hom).natTrans
private theorem scalarPullModel_hom (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (scalarPullModel A j).hom =
      ((mateEquiv (Scheme.proEtaleRingModuleAdjunction j
          (coefficients A X) (coefficients A U) (constantRingIso A j))
        (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j)).symm
          (TwoSquare.mk _ _ _ _ (scalarDirectModel A j).hom)).natTrans := by
  rfl

attribute [local irreducible] scalarPullModel

private theorem scalarPullModel_mate (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (mateEquiv (Scheme.proEtaleRingModuleAdjunction j
        (coefficients A X) (coefficients A U) (constantRingIso A j))
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j)
      (TwoSquare.mk _ _ _ _ (scalarPullModel A j).hom)).natTrans =
        (scalarDirectModel A j).hom := by
  simpa only [scalarPullModel_hom] using congrArg TwoSquare.natTrans
    ((mateEquiv (Scheme.proEtaleRingModuleAdjunction j
        (coefficients A X) (coefficients A U) (constantRingIso A j))
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j)).apply_symm_apply
        (TwoSquare.mk _ _ _ _ (scalarDirectModel A j).hom))

set_option backward.isDefEq.respectTransparency true in
private theorem scalarDirectCube [Finite B] [Finite C] (a : B →+* C)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ((TwoSquare.mk _ _ _ _ (pushRes a j).hom) ≫ᵥ
        (TwoSquare.mk _ _ _ _ (scalarDirectModel B j).hom)).whiskerLeft
          (scalarRestrictionAt a U).hom =
      ((TwoSquare.mk _ _ _ _ (scalarDirectModel C j).hom) ≫ᵥ
        (TwoSquare.mk (lowerStar (ModuleCat.{u + 1} C) j)
          (Sheaf.restrictScalars (Scheme.ProEt.topology U) a)
          (Sheaf.restrictScalars (Scheme.ProEt.topology X) a)
          (lowerStar (ModuleCat.{u + 1} B) j) (𝟙 _))).whiskerRight
            (scalarRestrictionAt a X).hom := by
  ext N W x
  change (((scalarRestrictionAt a U).hom.app N).hom.app
      ((Scheme.proEtaleBaseChange j).op.obj W)).hom
      ((((scalarDirectModel B j).hom.app ((res a U).obj N)).hom.app W).hom
        (((pushRes a j).hom.app N).val.app W x)) =
    (((scalarDirectModel C j).hom.app N).hom.app W).hom
      ((((scalarRestrictionAt a X).hom.app ((moduleDirectImage C j).obj N)).hom.app W).hom x)
  simp only [scalarRestrictionAt_apply, scalarDirectModel_apply]
  unfold pushRes
  exact (Classical.choose_spec (Scheme.proEtaleRingRestrictionDirectImage_existsUnique j
    (coefficients B X) (coefficients C X) (coefficients B U) (coefficients C U)
    (coefficientMap a X) (coefficientMap a U) (constantRingIso B j) (constantRingIso C j)
    (coefficientSquare a j))).1 N W x

set_option backward.isDefEq.respectTransparency true in
private theorem scalarOpenIso [Finite B] [Finite C] (a : B →+* C)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : IsIso (openResMap a j) := by
  have := scalarSectionsAt_equiv X B
  have := scalarSectionsAt_equiv U B
  have := scalarSectionsAt_equiv X C
  have := scalarSectionsAt_equiv U C
  have := ((proEtale_extension_by_zero B j).2.2.2.2.2.2 C a).1
  let aj (D : Type (u + 1)) [CommRing D] :=
    openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} D) j
  let w := TwoSquare.mk _ _ _ _ (pullRes a j).inv
  let b := TwoSquare.mk _ _ _ _ (scalarPullModel B j).inv
  let c := TwoSquare.mk _ _ _ _ (scalarPullModel C j).inv
  let d := TwoSquare.mk (openImmersionRestriction (ModuleCat.{u + 1} C) j)
    (Sheaf.restrictScalars (Scheme.ProEt.topology X) a)
    (Sheaf.restrictScalars (Scheme.ProEt.topology U) a)
    (openImmersionRestriction (ModuleCat.{u + 1} B) j) (eqToHom (by rfl))
  let e : Sheaf.restrictScalars (Scheme.ProEt.topology X) a ⋙
      openImmersionRestriction (ModuleCat.{u + 1} B) j ≅
    openImmersionRestriction (ModuleCat.{u + 1} C) j ⋙
      Sheaf.restrictScalars (Scheme.ProEt.topology U) a := eqToIso (by rfl)
  have heh : e.hom = eqToHom (by rfl) := rfl
  have hei : e.inv = eqToHom (by rfl) := rfl
  have hright : (w ≫ᵥ b).whiskerLeft (scalarRestrictionAt a X).hom =
      (c ≫ᵥ d).whiskerRight (scalarRestrictionAt a U).hom := by
    let adj (D : Type (u + 1)) [CommRing D] :=
      Scheme.proEtaleRingModuleAdjunction j
        (coefficients D X) (coefficients D U) (constantRingIso D j)
    have hf := inverted_mate_cube (adj C) (adj B)
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} C) j)
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) j)
      (pullRes a j) (scalarPullModel B j) (scalarPullModel C j) e
      (TwoSquare.mk _ _ _ _ (pushRes a j).hom)
      (TwoSquare.mk _ _ _ _ (scalarDirectModel B j).hom)
      (TwoSquare.mk _ _ _ _ (scalarDirectModel C j).hom)
      (TwoSquare.mk (lowerStar (ModuleCat.{u + 1} C) j)
        (Sheaf.restrictScalars (Scheme.ProEt.topology U) a)
        (Sheaf.restrictScalars (Scheme.ProEt.topology X) a)
        (lowerStar (ModuleCat.{u + 1} B) j) (𝟙 _))
      (pullRes_mate a j) (scalarPullModel_mate B j) (scalarPullModel_mate C j)
      (by simpa only [heh] using fixedRestriction_mate a j)
      (scalarRestrictionAt a X) (scalarRestrictionAt a U) (scalarDirectCube a j)
    simpa only [modulePullback, w, b, c, d, hei] using hf
  have hiD : IsIso (((mateEquiv (aj C) (aj B)).symm d).natTrans) := by
    change IsIso (openExtensionScalarMap a j)
    infer_instance
  exact inverseMate_isIso_of_cube
    (moduleJAdj C j) (moduleJAdj B j) (aj C) (aj B)
    w (scalarPullModel B j).symm (scalarPullModel C j).symm d
    (scalarRestrictionAt a U) (scalarRestrictionAt a X) hright

/-- The normalized open scalar mate is invertible, including for the empty open.
Source: Stacks Tag 03DI (blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: transport the pullback scalar comparison to the fixed-scalar sheaf model,
using the inverse-mate cube identity for the direct-image adjunctions. Invert that
cube and transpose under the extension adjunctions. The fixed-scalar open comparison
is invertible by the extension-by-zero theorem, and the coordinate comparisons are
invertible by equivalence of the scalar models. These equivalences reflect
invertibility of the specified openResMap. -/
theorem openResMap_isIso [Finite B] [Finite C] (a : B →+* C)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : IsIso (openResMap a j) := by
  exact scalarOpenIso a j

/-- The canonical scalar-restriction identification for open extension.
Source: Stacks Tag 03DI (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def openRes [Finite B] [Finite C] (a : B →+* C)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    res a U ⋙ moduleJ B j ≅ moduleJ C j ⋙ res a X :=
  @asIso _ _ _ _ (openResMap a j) (openResMap_isIso a j)

private theorem openRes_mate [Finite B] [Finite C] (a : B →+* C)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (mateEquiv (moduleJAdj C j) (moduleJAdj B j)
      (TwoSquare.mk _ _ _ _ (openRes a j).hom)).natTrans = (pullRes a j).inv := by
  simpa only [openRes, asIso_hom, openResMap] using
    congrArg TwoSquare.natTrans
      ((mateEquiv (moduleJAdj C j) (moduleJAdj B j)).apply_symm_apply
        (TwoSquare.mk _ _ _ _ (pullRes a j).inv))

/-- The recorded canonical open exchange on sheaves, before degreewise extension.
Its inverse is exactly singleBetaInv, the pulled-back open-unit transpose.
Source: Stacks Tag 09AE (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def beta (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g) :
    moduleJ A j ⋙ modulePullback A g ≅ modulePullback A gU ⋙ moduleJ A j' :=
  (@asIso _ _ _ _ (singleBetaInv A gU j' j g h)
    (singleBetaInv_isIso A gU j' j g h hsq)).symm

/-- The scalar identification on the source of open exchange.
Source: Stacks Tags 03DI and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def sourceRes [Finite B] [Finite C] (a : B →+* C)
    {U X' X : Scheme.{u}} (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] :
    res a U ⋙ (moduleJ B j ⋙ modulePullback B g) ≅
      (moduleJ C j ⋙ modulePullback C g) ⋙ res a X' :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (openRes a j) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (pullRes a g) ≪≫
    (Functor.associator _ _ _).symm

/-- The scalar identification on the target of open exchange.
Source: Stacks Tags 03DI and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def targetRes [Finite B] [Finite C] (a : B →+* C)
    {U' U X' : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X') [IsOpenImmersion j'] :
    res a U ⋙ (modulePullback B gU ⋙ moduleJ B j') ≅
      (modulePullback C gU ⋙ moduleJ C j') ⋙ res a X' :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (pullRes a gU) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (openRes a j') ≪≫
    (Functor.associator _ _ _).symm

/-- Scalar restriction on unbounded complexes, with all terms and differentials retained.
Source: blueprint finite exchange paragraph
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
abbrev resC (a : B →+* C) (X : Scheme.{u}) :
    CochainComplex (Modules C X) ℤ ⥤ CochainComplex (Modules B X) ℤ :=
  (res a X).mapHomologicalComplex (.up ℤ)

/-- The complex-level exchange, from the recorded sheaf exchange term by term.
Source: Stacks Tag 09AE (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def betaC (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g) :
    (moduleJ A j ⋙ modulePullback A g).mapHomologicalComplex (.up ℤ) ≅
      (modulePullback A gU ⋙ moduleJ A j').mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (beta A gU j' j g h hsq) (.up ℤ)

/-- The source identification on complexes.
Source: blueprint finite exchange paragraph
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def sourceResC [Finite B] [Finite C] (a : B →+* C)
    {U X' X : Scheme.{u}} (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] :
    (res a U ⋙ (moduleJ B j ⋙ modulePullback B g)).mapHomologicalComplex (.up ℤ) ≅
      ((moduleJ C j ⋙ modulePullback C g) ⋙ res a X').mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (sourceRes a j g) (.up ℤ)

/-- The target identification on complexes.
Source: blueprint finite exchange paragraph
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def targetResC [Finite B] [Finite C] (a : B →+* C)
    {U' U X' : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X') [IsOpenImmersion j'] :
    (res a U ⋙ (modulePullback B gU ⋙ moduleJ B j')).mapHomologicalComplex (.up ℤ) ≅
      ((modulePullback C gU ⋙ moduleJ C j') ⋙ res a X').mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (targetRes a gU j') (.up ℤ)

set_option backward.isDefEq.respectTransparency false in
/-- Scalar restriction preserves the specified open unit and counit.
Source: Stacks Tag 03DI, explicit summand adjunction
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: the pullback comparison is the mate of identity on sections. The open comparison
is its mate under extension/restriction. The two mate equations are exactly the unit
and counit identities below; alternatively the summand formulas send s to the same s
before and after restriction of scalars. These identities hold in each complex degree. -/
theorem open_unit_counit [Finite B] [Finite C] (a : B →+* C)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (∀ F : Modules C U,
      (moduleJAdj B j).unit.app ((res a U).obj F) ≫
          (modulePullback B j).map ((openRes a j).hom.app F) ≫
          (pullRes a j).hom.app ((moduleJ C j).obj F) =
        (res a U).map ((moduleJAdj C j).unit.app F)) ∧
    (∀ N : Modules C X,
      (openRes a j).hom.app ((modulePullback C j).obj N) ≫
          (res a X).map ((moduleJAdj C j).counit.app N) =
        (moduleJ B j).map ((pullRes a j).inv.app N) ≫
          (moduleJAdj B j).counit.app ((res a X).obj N)) := by
  simpa only [Iso.symm_hom, Iso.symm_inv] using
    mate_unit_counit_iso (moduleJAdj C j) (moduleJAdj B j)
      (G := res a U) (H := res a X) (openRes a j).hom (pullRes a j).symm
      (openRes_mate a j)

/-- Scalar restriction preserves the inverse-image/direct-image unit and counit.
Source: Stacks Tags 03D2 and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: direct image comparison is the identity on sections. The pullback comparison
was defined as its mate using the normalized module adjunctions. The mate unit and
counit equations give the two equalities; all constructions are applied degreewise. -/
theorem pull_unit_counit [Finite B] [Finite C] (a : B →+* C)
    {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (∀ F : Modules C X,
      (res a X).map ((Scheme.proEtaleRingModuleAdjunction f
          (coefficients C X) (coefficients C Y) (constantRingIso C f)).unit.app F) ≫
          (pushRes a f).hom.app ((modulePullback C f).obj F) =
        (Scheme.proEtaleRingModuleAdjunction f
          (coefficients B X) (coefficients B Y) (constantRingIso B f)).unit.app
            ((res a X).obj F) ≫
          (moduleDirectImage B f).map ((pullRes a f).hom.app F)) ∧
    (∀ N : Modules C Y,
      (pullRes a f).hom.app ((moduleDirectImage C f).obj N) ≫
          (res a Y).map ((Scheme.proEtaleRingModuleAdjunction f
            (coefficients C X) (coefficients C Y) (constantRingIso C f)).counit.app N) =
        (modulePullback B f).map ((pushRes a f).hom.app N) ≫
          (Scheme.proEtaleRingModuleAdjunction f
            (coefficients B X) (coefficients B Y) (constantRingIso B f)).counit.app
              ((res a Y).obj N)) := by
  exact mate_unit_counit
    (Scheme.proEtaleRingModuleAdjunction f
      (coefficients C X) (coefficients C Y) (constantRingIso C f))
    (Scheme.proEtaleRingModuleAdjunction f
      (coefficients B X) (coefficients B Y) (constantRingIso B f))
    (G := res a X) (H := res a Y) (pullRes a f).hom (pushRes a f).hom
    (pullRes_mate a f)


set_option backward.isDefEq.respectTransparency false in
private theorem beta_mate (A : Type (u + 1)) [CommRing A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) :
    ((mateEquiv (moduleJAdj A j) (moduleJAdj A j')).symm
      (TwoSquare.mk _ _ _ _ (moduleSquareG A gU j' j g h).inv)).natTrans =
      singleBetaInv A gU j' j g h := by
  apply NatTrans.ext
  funext M
  apply ((moduleJAdj A j').homEquiv _ _).injective
  simp only [singleBetaInv, singleBetaInvApp, Functor.comp_obj,
    Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm (moduleJAdj A j) (moduleJAdj A j')
    (TwoSquare.mk _ _ _ _ (moduleSquareG A gU j' j g h).inv) M).symm


private theorem beta_inv (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g) :
    (beta A gU j' j g h hsq).inv = singleBetaInv A gU j' j g h := by
  rfl

attribute [local irreducible] beta

set_option backward.isDefEq.respectTransparency false in
private theorem inverse_exchange_scalars [Finite B] [Finite C] (a : B →+* C)
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g)
    (M : Modules C U) :
    (targetRes a gU j').hom.app M ≫
        (res a X').map ((singleBetaInv C gU j' j g h).app M) =
      (singleBetaInv B gU j' j g h).app ((res a U).obj M) ≫
        (sourceRes a j g).hom.app M := by
  let w := TwoSquare.mk _ _ _ _ (pullRes a j).inv
  let b := TwoSquare.mk _ _ _ _ (moduleSquareG B gU j' j g h).inv
  let c := TwoSquare.mk _ _ _ _ (moduleSquareG C gU j' j g h).inv
  let d := TwoSquare.mk _ _ _ _ (pullRes a j').inv
  have hr : (w ≫ᵥ b).whiskerLeft (pullRes a g).hom =
      (c ≫ᵥ d).whiskerRight (pullRes a gU).hom := by
    apply TwoSquare.ext
    intro N
    simp only [w, b, c, d, TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
      TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id]
    simpa only [Functor.mapIso_inv, Iso.app_inv, Category.assoc] using
      (invert_outer
        ((modulePullback B gU).mapIso ((pullRes a j).app N))
        ((pullRes a j').app ((modulePullback C g).obj N))
        (s := (pullRes a gU).hom.app ((modulePullback C j).obj N) ≫
          (res a U').map ((moduleSquareG C gU j' j g h).inv.app N))
        (r := (moduleSquareG B gU j' j g h).inv.app ((res a X).obj N) ≫
          (modulePullback B j').map ((pullRes a g).hom.app N))
        (by simpa only [Functor.mapIso_hom, Iso.app_hom, Category.assoc] using
          pullRes_square a gU j' j g h N))
  have hh := inverse_cube (moduleJAdj C j) (moduleJAdj B j)
    (moduleJAdj C j') (moduleJAdj B j') w b c d
    (pullRes a gU).hom (pullRes a g).hom hr
  have he := congrArg (fun z ↦ z.natTrans.app M) hh
  simp only [w, b, c, d, TwoSquare.hComp, TwoSquare.whiskerBottom, TwoSquare.whiskerTop,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, beta_mate] at he
  simpa only [targetRes, sourceRes, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    openRes, asIso_hom, openResMap, Category.assoc] using he.symm

private theorem exchange_scalars_app [Finite B] [Finite C] (a : B →+* C)
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g)
    (M : Modules C U) :
    (sourceRes a j g).hom.app M ≫
        (res a X').map ((beta C gU j' j g h hsq).hom.app M) =
      (beta B gU j' j g h hsq).hom.app ((res a U).obj M) ≫
        (targetRes a gU j').hom.app M := by
  apply forward_of_inverse ((beta B gU j' j g h hsq).app ((res a U).obj M))
    ((res a X').mapIso ((beta C gU j' j g h hsq).app M))
  simpa only [Functor.mapIso_inv, Iso.app_inv, beta_inv] using
    inverse_exchange_scalars a gU j' j g h M

/-- Restriction carries the finite C-exchange to the finite B-exchange, for every complex.
Source: blueprint finite exchange paragraph; Stacks Tags 03DI and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: the coefficient square preserves constants. Pullback and extension scalar
comparisons preserve the units and counits. The recorded inverse exchange is the
transpose of the pulled-back open unit and the site-composition comparison. Restricting
this formula gives the B-formula, so uniqueness of adjuncts gives equality of inverses
and then equality of exchanges. Apply the equality degreewise; naturality supplies
compatibility with all differentials and chain maps. -/
theorem exchange_restrictScalars [Finite B] [Finite C] (a : B →+* C)
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g)
    (F : CochainComplex (Modules C U) ℤ) :
    (sourceResC a j g).hom.app F ≫
        (resC a X').map ((betaC C gU j' j g h hsq).hom.app F) =
      (betaC B gU j' j g h hsq).hom.app ((resC a U).obj F) ≫
        (targetResC a gU j').hom.app F := by
  ext i : 1
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  exact congrArg (fun k ↦ k.val.app W x)
    (exchange_scalars_app a gU j' j g h hsq (F.X i))

attribute [local irreducible] sourceRes targetRes sourceResC targetResC betaC

set_option backward.isDefEq.respectTransparency false

/-- The inverse exchange is the specified pulled-back open-unit transpose in every degree.
Source: Stacks Tag 09AE and the blueprint's inverse-mate normalization
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: the recorded singleBetaInvApp is defined by exactly this adjunction transpose.
The inverse of beta is that recorded natural transformation. Mapping it termwise
retains its components, giving the equality for every integer degree. -/
theorem inverse_unit_transpose (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g)
    (F : CochainComplex (Modules A U) ℤ) (i : ℤ) :
    ((betaC A gU j' j g h hsq).inv.app F).f i =
      ((moduleJAdj A j').homEquiv _ _).symm
        ((modulePullback A gU).map ((moduleJAdj A j).unit.app (F.X i)) ≫
          (moduleSquareG A gU j' j g h).inv.app ((moduleJ A j).obj (F.X i))) := by
  simp only [betaC, NatIso.mapHomologicalComplex_inv_app_f, beta,
    Iso.symm_inv, asIso_hom, singleBetaInv, singleBetaInvApp, Functor.id_obj]

private theorem exchange_transition_app [Finite B] [Finite C] (a : B →+* C)
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g)
    (F : Modules B U) (G : Modules C U)
    (t : F ⟶ (res a U).obj G) :
    (moduleJ B j ⋙ modulePullback B g).map t ≫
          (sourceRes a j g).hom.app G ≫
          (res a X').map ((beta C gU j' j g h hsq).hom.app G) =
        (beta B gU j' j g h hsq).hom.app F ≫
          (modulePullback B gU ⋙ moduleJ B j').map t ≫
          (targetRes a gU j').hom.app G ∧
    (modulePullback B gU ⋙ moduleJ B j').map t ≫
          (targetRes a gU j').hom.app G ≫
          (res a X').map ((beta C gU j' j g h hsq).inv.app G) =
        (beta B gU j' j g h hsq).inv.app F ≫
          (moduleJ B j ⋙ modulePullback B g).map t ≫
          (sourceRes a j g).hom.app G := by
  exact semilinear_square (beta B gU j' j g h hsq) t
    ((res a X').mapIso ((beta C gU j' j g h hsq).app G))
    ((sourceRes a j g).hom.app G) ((targetRes a gU j').hom.app G)
    (exchange_scalars_app a gU j' j g h hsq G)

/-- Every semilinear chain map commutes with the exchange and its inverse.
This includes successive strict tower transitions and every composite transition.
Source: blueprint finite exchange paragraph
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: apply naturality of beta and its inverse to the strict B-linear map t.
Use exchange_restrictScalars at G and its inverse square to replace the restricted
C-exchange. Composition gives both displayed commuting squares without homotopy. -/
theorem exchange_transition [Finite B] [Finite C] (a : B →+* C)
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g)
    (F : CochainComplex (Modules B U) ℤ) (G : CochainComplex (Modules C U) ℤ)
    (t : F ⟶ (resC a U).obj G) :
    ((moduleJ B j ⋙ modulePullback B g).mapHomologicalComplex (.up ℤ)).map t ≫
          (sourceResC a j g).hom.app G ≫
          (resC a X').map ((betaC C gU j' j g h hsq).hom.app G) =
        (betaC B gU j' j g h hsq).hom.app F ≫
          ((modulePullback B gU ⋙ moduleJ B j').mapHomologicalComplex (.up ℤ)).map t ≫
          (targetResC a gU j').hom.app G ∧
    ((modulePullback B gU ⋙ moduleJ B j').mapHomologicalComplex (.up ℤ)).map t ≫
          (targetResC a gU j').hom.app G ≫
          (resC a X').map ((betaC C gU j' j g h hsq).inv.app G) =
        (betaC B gU j' j g h hsq).inv.app F ≫
          ((moduleJ B j ⋙ modulePullback B g).mapHomologicalComplex (.up ℤ)).map t ≫
          (sourceResC a j g).hom.app G := by
  constructor
  · ext i : 1
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    ext x
    unfold sourceResC targetResC betaC resC
    exact congrArg (fun k ↦ k.val.app W x)
      (exchange_transition_app a gU j' j g h hsq (F.X i) (G.X i) (t.f i)).1
  · ext i : 1
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    ext x
    unfold sourceResC targetResC betaC resC
    exact congrArg (fun k ↦ k.val.app W x)
      (exchange_transition_app a gU j' j g h hsq (F.X i) (G.X i) (t.f i)).2

/-- Restriction along the identity has its unique identity-on-sections identification.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: identity scalar restriction leaves the action unchanged. Identity section maps
are linear and natural, and their inverses are identical. Sections determine uniqueness. -/
theorem resId_existsUnique (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    ∃! e : res (RingHom.id A) X ≅ 𝟭 (Modules A X),
      ∀ (M : Modules A X) (W : X.ProEtᵒᵖ) (m : M.val.obj W),
        (e.hom.app M).val.app W m = m := by
  have hid : ringCoefficientMap (RingHom.id A) X = 𝟙 _ := by
    change (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (𝟙 _)) = _
    exact (congrArg (fun k ↦ (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map k)
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map_id
        (CommRingCat.of A))).trans
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_id _)
  let e : res (RingHom.id A) X ≅ 𝟭 (Modules A X) :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun W ↦
        ModuleCat.restrictScalarsId'App _
          (congrArg (fun k ↦ (k.hom.app W).hom) hid) (M.val.obj W)) (by
        intro W W' f
        ext m
        rfl))) (by
      intro M N f
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro W
      ext m
      rfl)
  refine ⟨e, fun _ _ _ ↦ rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext m
  exact he' M W m

/-- The identity-on-sections identification for identity restriction.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def resId (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    res (RingHom.id A) X ≅ 𝟭 (Modules A X) :=
  Classical.choose (resId_existsUnique A X)

/-- Compatible ambient coefficient actions give a unique identity-on-sections comparison.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: the equation on ring maps says the two restricted actions agree. Identity on
every section is therefore linear, natural, and its own inverse. Sectionwise faithfulness
makes the resulting natural isomorphism unique. -/
theorem ambientRes_existsUnique (a : B →+* C) (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1})
    (rB : R ⟶ ringCoefficients B X) (rC : R ⟶ ringCoefficients C X)
    (hr : rB ≫ ringCoefficientMap a X = rC) :
    ∃! e : res a X ⋙ SheafOfModules.restrictScalars.{u + 1} rB ≅
        SheafOfModules.restrictScalars.{u + 1} rC,
      ∀ (M : Modules C X) (W : X.ProEtᵒᵖ) (m : M.val.obj W),
        (e.hom.app M).val.app W m = m := by
  let e : res a X ⋙ SheafOfModules.restrictScalars.{u + 1} rB ≅
      SheafOfModules.restrictScalars.{u + 1} rC :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun W ↦
        (ModuleCat.restrictScalarsComp'App (rB.hom.app W).hom
          ((ringCoefficientMap a X).hom.app W).hom (rC.hom.app W).hom
          (congrArg (fun k ↦ (k.hom.app W).hom) hr.symm) (M.val.obj W)).symm) (by
        intro W W' f
        ext m
        rfl))) (by
      intro M N f
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro W
      ext m
      rfl)
  refine ⟨e, fun _ _ _ ↦ rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext m
  exact he' M W m

/-- The fixed comparison for restriction to compatible ambient actions.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def ambientRes (a : B →+* C) (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1})
    (rB : R ⟶ ringCoefficients B X) (rC : R ⟶ ringCoefficients C X)
    (hr : rB ≫ ringCoefficientMap a X = rC) :
    res a X ⋙ SheafOfModules.restrictScalars.{u + 1} rB ≅
      SheafOfModules.restrictScalars.{u + 1} rC :=
  Classical.choose (ambientRes_existsUnique a X R rB rC hr)

/-- Constant coefficient maps respect composition.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: this is functoriality of constant-sheaf sheafification on ring maps. -/
theorem coefficientMap_comp {D : Type (u + 1)} [CommRing D]
    (a : B →+* C) (b : C →+* D) (X : Scheme.{u}) :
    ringCoefficientMap a X ≫ ringCoefficientMap b X = ringCoefficientMap (b.comp a) X := by
  change (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map _ ≫
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map _ = _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  rfl

/-- The identity-on-sections comparison between successive and composite restriction.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def resComp {D : Type (u + 1)} [CommRing D] (a : B →+* C) (b : C →+* D)
    (X : Scheme.{u}) : res b X ⋙ res a X ≅ res (b.comp a) X :=
  ambientRes b X (ringCoefficients B X) (ringCoefficientMap a X)
    (ringCoefficientMap (b.comp a) X)
    (coefficientMap_comp a b X)


set_option backward.isDefEq.respectTransparency false

private theorem resId_apply (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (M : Modules A X) (W : X.ProEtᵒᵖ) (m : M.val.obj W) :
    ((resId A X).hom.app M).val.app W m = m :=
  (Classical.choose_spec (resId_existsUnique A X)).1 M W m

private theorem pushRes_apply {B C : Type (u + 1)} [CommRing B] [CommRing C]
    (a : B →+* C) {Y X : Scheme.{u}} (f : Y ⟶ X) (N : Modules C Y)
    (W : X.ProEtᵒᵖ) (m : N.val.obj ((Scheme.proEtaleBaseChange f).op.obj W)) :
    ((pushRes a f).hom.app N).val.app W m = m := by
  unfold pushRes
  exact (Classical.choose_spec (Scheme.proEtaleRingRestrictionDirectImage_existsUnique f
    (coefficients B X) (coefficients C X) (coefficients B Y) (coefficients C Y)
    (coefficientMap a X) (coefficientMap a Y) (constantRingIso B f) (constantRingIso C f)
    (coefficientSquare a f))).1 N W m

private theorem push_identity (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (f : Y ⟶ X) (N : Modules A Y) :
    (pushRes (RingHom.id A) f).hom.app N ≫
        (moduleDirectImage A f).map ((resId A Y).hom.app N) =
      (resId A X).hom.app ((moduleDirectImage A f).obj N) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext m
  change ((resId A Y).hom.app N).val.app ((Scheme.proEtaleBaseChange f).op.obj W)
    (((pushRes (RingHom.id A) f).hom.app N).val.app W m) = _
  rw [pushRes_apply, resId_apply]
  exact (resId_apply A X ((moduleDirectImage A f).obj N) W m).symm

private theorem left_square_identity
    {D E : Type*} [Category D] [Category E]
    {L : D ⥤ E} {R : E ⥤ D} (adj : L ⊣ R)
    {G : D ⥤ D} {H : E ⥤ E} (eG : G ⟶ 𝟭 D) (eH : H ⟶ 𝟭 E)
    (p : G ⋙ L ⟶ L ⋙ H) (d : R ⋙ G ⟶ H ⋙ R)
    (hu : ∀ M, G.map (adj.unit.app M) ≫ d.app (L.obj M) =
      adj.unit.app (G.obj M) ≫ R.map (p.app M))
    (hd : ∀ N, d.app N ≫ R.map (eH.app N) = eG.app (R.obj N)) (M : D) :
    p.app M ≫ eH.app (L.obj M) = L.map (eG.app M) := by
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp]
  rw [← Category.assoc, ← hu, Category.assoc, hd]
  exact (eG.naturality (adj.unit.app M)).trans (adj.unit.naturality (eG.app M))

private theorem pull_identity_aux (A : Type (u + 1)) [CommRing A] [Finite A]
    {Y X : Scheme.{u}} (f : Y ⟶ X) (M : Modules A X) :
    (pullRes (RingHom.id A) f).hom.app M ≫
        (resId A Y).hom.app ((modulePullback A f).obj M) =
      (modulePullback A f).map ((resId A X).hom.app M) := by
  exact left_square_identity (Scheme.proEtaleRingModuleAdjunction f
    (coefficients A X) (coefficients A Y) (constantRingIso A f))
    (resId A X).hom (resId A Y).hom (pullRes (RingHom.id A) f).hom
    (pushRes (RingHom.id A) f).hom
    (pull_unit_counit (RingHom.id A) f).1 (push_identity A f) M

/-- The canonical inverse-image and extension scalar identifications preserve identities.
Source: Stacks Tags 03D2 and 03DI
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: the identity-on-sections direct-image comparison is the identity after resId.
Uniqueness of the unit-preserving mate gives the pullback equality. Transposing that
equality under the two open adjunctions gives the extension equality. -/
theorem scalar_identity (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (∀ M : Modules A X,
      (pullRes (RingHom.id A) j).hom.app M ≫
          (resId A U).hom.app ((modulePullback A j).obj M) =
        (modulePullback A j).map ((resId A X).hom.app M)) ∧
    (∀ F : Modules A U,
      (openRes (RingHom.id A) j).hom.app F ≫
          (resId A X).hom.app ((moduleJ A j).obj F) =
        (moduleJ A j).map ((resId A U).hom.app F)) := by
  constructor
  · exact pull_identity_aux A j
  · intro F
    apply left_square_identity (moduleJAdj A j)
      (resId A U).hom (resId A X).hom (openRes (RingHom.id A) j).hom
      (pullRes (RingHom.id A) j).inv
    · intro M
      exact unit_mateEquiv_symm (moduleJAdj A j) (moduleJAdj A j)
        (TwoSquare.mk _ _ _ _ (pullRes (RingHom.id A) j).inv) M
    · intro N
      apply (cancel_epi ((pullRes (RingHom.id A) j).hom.app N)).mp
      simpa only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using
        (pull_identity_aux A j N).symm


set_option backward.isDefEq.respectTransparency false in
private theorem left_square_composition
    {D₁ D₂ D₃ E₁ E₂ E₃ : Type*}
    [Category D₁] [Category D₂] [Category D₃]
    [Category E₁] [Category E₂] [Category E₃]
    {L₁ : D₁ ⥤ E₁} {R₁ : E₁ ⥤ D₁}
    {L₂ : D₂ ⥤ E₂} {R₂ : E₂ ⥤ D₂}
    {L₃ : D₃ ⥤ E₃} {R₃ : E₃ ⥤ D₃}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    {G₁ : D₁ ⥤ D₂} {G₂ : D₂ ⥤ D₃} {G₃ : D₁ ⥤ D₃}
    {H₁ : E₁ ⥤ E₂} {H₂ : E₂ ⥤ E₃} {H₃ : E₁ ⥤ E₃}
    (eG : G₁ ⋙ G₂ ≅ G₃) (eH : H₁ ⋙ H₂ ≅ H₃)
    (p₁ : G₁ ⋙ L₂ ⟶ L₁ ⋙ H₁) (p₂ : G₂ ⋙ L₃ ⟶ L₂ ⋙ H₂)
    (p₃ : G₃ ⋙ L₃ ⟶ L₁ ⋙ H₃)
    (d₁ : R₁ ⋙ G₁ ⟶ H₁ ⋙ R₂) (d₂ : R₂ ⋙ G₂ ⟶ H₂ ⋙ R₃)
    (d₃ : R₁ ⋙ G₃ ⟶ H₃ ⋙ R₃)
    (hu₁ : ∀ M, G₁.map (adj₁.unit.app M) ≫ d₁.app (L₁.obj M) =
      adj₂.unit.app (G₁.obj M) ≫ R₂.map (p₁.app M))
    (hu₂ : ∀ M, G₂.map (adj₂.unit.app M) ≫ d₂.app (L₂.obj M) =
      adj₃.unit.app (G₂.obj M) ≫ R₃.map (p₂.app M))
    (hu₃ : ∀ M, G₃.map (adj₁.unit.app M) ≫ d₃.app (L₁.obj M) =
      adj₃.unit.app (G₃.obj M) ≫ R₃.map (p₃.app M))
    (hd : ∀ N, G₂.map (d₁.app N) ≫ d₂.app (H₁.obj N) ≫ R₃.map (eH.hom.app N) =
      eG.hom.app (R₁.obj N) ≫ d₃.app N) (M : D₁) :
    L₃.map (eG.inv.app M) ≫ p₂.app (G₁.obj M) ≫ H₂.map (p₁.app M) ≫
        eH.hom.app (L₁.obj M) = p₃.app M := by
  apply (cancel_epi (L₃.map (eG.hom.app M))).mp
  simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  apply (adj₃.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp,
    Functor.comp_obj, Category.assoc]
  simp only [← Category.assoc]
  rw [← hu₂ (G₁.obj M)]
  simp only [Category.assoc]
  have hn := NatTrans.naturality_assoc d₂ (p₁.app M)
    (R₃.map (eH.hom.app (L₁.obj M)))
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [← hn]
  simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  rw [← hu₁ M]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hd, ← Category.assoc]
  have he := eG.hom.naturality (adj₁.unit.app M)
  dsimp only [Functor.comp_obj, Functor.comp_map] at he
  rw [he]
  simp only [Category.assoc]
  rw [hu₃]
  have ha := adj₃.unit.naturality (eG.hom.app M)
  dsimp only [Functor.id_map, Functor.comp_map] at ha
  simpa only [Functor.id_obj, Functor.comp_obj, Category.assoc] using
    congrArg (fun k ↦ k ≫ R₃.map (p₃.app M)) ha

private theorem left_square_composition_of_mates
    {D₁ D₂ D₃ E₁ E₂ E₃ : Type*}
    [Category D₁] [Category D₂] [Category D₃]
    [Category E₁] [Category E₂] [Category E₃]
    {L₁ : D₁ ⥤ E₁} {R₁ : E₁ ⥤ D₁}
    {L₂ : D₂ ⥤ E₂} {R₂ : E₂ ⥤ D₂}
    {L₃ : D₃ ⥤ E₃} {R₃ : E₃ ⥤ D₃}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    {G₁ : D₁ ⥤ D₂} {G₂ : D₂ ⥤ D₃} {G₃ : D₁ ⥤ D₃}
    {H₁ : E₁ ⥤ E₂} {H₂ : E₂ ⥤ E₃} {H₃ : E₁ ⥤ E₃}
    (eG : G₁ ⋙ G₂ ≅ G₃) (eH : H₁ ⋙ H₂ ≅ H₃)
    (p₁ : G₁ ⋙ L₂ ⟶ L₁ ⋙ H₁) (p₂ : G₂ ⋙ L₃ ⟶ L₂ ⋙ H₂)
    (p₃ : G₃ ⋙ L₃ ⟶ L₁ ⋙ H₃)
    (d₁ : R₁ ⋙ G₁ ⟶ H₁ ⋙ R₂) (d₂ : R₂ ⋙ G₂ ⟶ H₂ ⋙ R₃)
    (d₃ : R₁ ⋙ G₃ ⟶ H₃ ⋙ R₃)
    (hm₁ : (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ p₁)).natTrans = d₁)
    (hm₂ : (mateEquiv adj₂ adj₃ (TwoSquare.mk _ _ _ _ p₂)).natTrans = d₂)
    (hm₃ : (mateEquiv adj₁ adj₃ (TwoSquare.mk _ _ _ _ p₃)).natTrans = d₃)
    (hd : ∀ N, G₂.map (d₁.app N) ≫ d₂.app (H₁.obj N) ≫ R₃.map (eH.hom.app N) =
      eG.hom.app (R₁.obj N) ≫ d₃.app N) (M : D₁) :
    L₃.map (eG.inv.app M) ≫ p₂.app (G₁.obj M) ≫ H₂.map (p₁.app M) ≫
        eH.hom.app (L₁.obj M) = p₃.app M := by
  exact left_square_composition adj₁ adj₂ adj₃ eG eH p₁ p₂ p₃ d₁ d₂ d₃
    (mate_unit_counit adj₁ adj₂ p₁ d₁ hm₁).1
    (mate_unit_counit adj₂ adj₃ p₂ d₂ hm₂).1
    (mate_unit_counit adj₁ adj₃ p₃ d₃ hm₃).1 hd M

private theorem ambientRes_apply {B C : Type (u + 1)} [CommRing B] [CommRing C]
    (a : B →+* C) (X : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1})
    (rB : R ⟶ ringCoefficients B X) (rC : R ⟶ ringCoefficients C X)
    (hr : rB ≫ ringCoefficientMap a X = rC)
    (M : Modules C X) (W : X.ProEtᵒᵖ) (x : M.val.obj W) :
    ((ambientRes a X R rB rC hr).hom.app M).val.app W x = x := by
  unfold ambientRes
  exact (Classical.choose_spec (ambientRes_existsUnique a X R rB rC hr)).1 M W x

set_option backward.isDefEq.respectTransparency false in
private theorem resComp_apply {D : Type (u + 1)} [CommRing D]
    (a : B →+* C) (b : C →+* D) (X : Scheme.{u})
    (M : Modules D X) (W : X.ProEtᵒᵖ) (m : M.val.obj W) :
    ((resComp a b X).hom.app M).val.app W m = m :=
  (Classical.choose_spec (ambientRes_existsUnique b X (ringCoefficients B X)
    (ringCoefficientMap a X) (ringCoefficientMap (b.comp a) X)
    (coefficientMap_comp a b X))).1 M W m

set_option backward.isDefEq.respectTransparency false in
private theorem push_composition {D : Type (u + 1)} [CommRing D]
    (a : B →+* C) (b : C →+* D) {Y X : Scheme.{u}} (f : Y ⟶ X)
    (N : Modules D Y) :
    (res a X).map ((pushRes b f).hom.app N) ≫
        (pushRes a f).hom.app ((res b Y).obj N) ≫
        (moduleDirectImage B f).map ((resComp a b Y).hom.app N) =
      (resComp a b X).hom.app ((moduleDirectImage D f).obj N) ≫
        (pushRes (b.comp a) f).hom.app N := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext m
  change ((resComp a b Y).hom.app N).val.app
      ((Scheme.proEtaleBaseChange f).op.obj W)
      (((pushRes a f).hom.app ((res b Y).obj N)).val.app W
        (((pushRes b f).hom.app N).val.app W m)) =
    ((pushRes (b.comp a) f).hom.app N).val.app W
      (((resComp a b X).hom.app ((moduleDirectImage D f).obj N)).val.app W m)
  simp only [resComp_apply, pushRes_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem pull_composition_aux {D : Type (u + 1)} [CommRing D]
    [Finite B] [Finite C] [Finite D] (a : B →+* C) (b : C →+* D)
    {Y X : Scheme.{u}} (f : Y ⟶ X) (M : Modules D X) :
    (modulePullback B f).map ((resComp a b X).inv.app M) ≫
        (pullRes a f).hom.app ((res b X).obj M) ≫
        (res a Y).map ((pullRes b f).hom.app M) ≫
        (resComp a b Y).hom.app ((modulePullback D f).obj M) =
      (pullRes (b.comp a) f).hom.app M := by
  exact left_square_composition_of_mates
    (D₁ := Modules D X) (D₂ := Modules C X) (D₃ := Modules B X)
    (E₁ := Modules D Y) (E₂ := Modules C Y) (E₃ := Modules B Y)
    (L₁ := modulePullback D f) (R₁ := moduleDirectImage D f)
    (L₂ := modulePullback C f) (R₂ := moduleDirectImage C f)
    (L₃ := modulePullback B f) (R₃ := moduleDirectImage B f)
    (G₁ := res b X) (G₂ := res a X) (G₃ := res (b.comp a) X)
    (H₁ := res b Y) (H₂ := res a Y) (H₃ := res (b.comp a) Y)
    (Scheme.proEtaleRingModuleAdjunction f
      (coefficients D X) (coefficients D Y) (constantRingIso D f))
    (Scheme.proEtaleRingModuleAdjunction f
      (coefficients C X) (coefficients C Y) (constantRingIso C f))
    (Scheme.proEtaleRingModuleAdjunction f
      (coefficients B X) (coefficients B Y) (constantRingIso B f))
    (resComp a b X) (resComp a b Y)
    (pullRes b f).hom (pullRes a f).hom (pullRes (b.comp a) f).hom
    (pushRes b f).hom (pushRes a f).hom (pushRes (b.comp a) f).hom
    (pullRes_mate b f) (pullRes_mate a f)
    (pullRes_mate (b.comp a) f) (push_composition a b f) M

/-- Pullback and open-extension identifications compose along arbitrary coefficient maps.
Source: Stacks Tags 03D2 and 03DI
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: all direct-image scalar identifications are identity on sections, so their
composite is the identity for the composite ring map under resComp. Mate pasting gives
the pullback equality; mate pasting once more under the open adjunctions gives the
extension equality. Applying degreewise gives the same identities for chain maps. -/
theorem scalar_composition {D : Type (u + 1)} [CommRing D]
    [Finite B] [Finite C] [Finite D] (a : B →+* C) (b : C →+* D)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (∀ M : Modules D X,
      (modulePullback B j).map ((resComp a b X).inv.app M) ≫
          (pullRes a j).hom.app ((res b X).obj M) ≫
          (res a U).map ((pullRes b j).hom.app M) ≫
          (resComp a b U).hom.app ((modulePullback D j).obj M) =
        (pullRes (b.comp a) j).hom.app M) ∧
    (∀ F : Modules D U,
      (moduleJ B j).map ((resComp a b U).inv.app F) ≫
          (openRes a j).hom.app ((res b U).obj F) ≫
          (res a X).map ((openRes b j).hom.app F) ≫
          (resComp a b X).hom.app ((moduleJ D j).obj F) =
        (openRes (b.comp a) j).hom.app F) := by
  constructor
  · exact pull_composition_aux a b j
  · intro F
    apply left_square_composition_of_mates
      (D₁ := Modules D U) (D₂ := Modules C U) (D₃ := Modules B U)
      (E₁ := Modules D X) (E₂ := Modules C X) (E₃ := Modules B X)
      (L₁ := moduleJ D j) (R₁ := modulePullback D j)
      (L₂ := moduleJ C j) (R₂ := modulePullback C j)
      (L₃ := moduleJ B j) (R₃ := modulePullback B j)
      (G₁ := res b U) (G₂ := res a U) (G₃ := res (b.comp a) U)
      (H₁ := res b X) (H₂ := res a X) (H₃ := res (b.comp a) X)
      (moduleJAdj D j) (moduleJAdj C j) (moduleJAdj B j)
      (resComp a b U) (resComp a b X)
      (openRes b j).hom (openRes a j).hom (openRes (b.comp a) j).hom
      (pullRes b j).inv (pullRes a j).inv (pullRes (b.comp a) j).inv
    · exact openRes_mate b j
    · exact openRes_mate a j
    · exact openRes_mate (b.comp a) j
    · intro N
      simpa only [Functor.mapIso_inv, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv] using
        (inverse_path ((modulePullback B j).mapIso ((resComp a b X).app N))
          ((pullRes a j).app ((res b X).obj N))
          ((res a U).mapIso ((pullRes b j).app N))
          ((resComp a b U).app ((modulePullback D j).obj N))
          ((pullRes (b.comp a) j).app N)
          (by simpa only [Functor.mapIso_inv, Functor.mapIso_hom,
            Iso.app_hom, Iso.app_inv] using pull_composition_aux a b j N))

/-- Pullback scalar identifications preserve the identity for arbitrary scheme maps.
Source: Stacks Tags 03D2 and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: the direct-image comparison is identity on every section after the identity
restriction comparison. Uniqueness of its adjunction mate gives this equation. -/
theorem pull_identity (A : Type (u + 1)) [CommRing A] [Finite A]
    {Y X : Scheme.{u}} (f : Y ⟶ X) (M : Modules A X) :
    (pullRes (RingHom.id A) f).hom.app M ≫
        (resId A Y).hom.app ((modulePullback A f).obj M) =
      (modulePullback A f).map ((resId A X).hom.app M) := by
  exact pull_identity_aux A f M

/-- Pullback scalar identifications compose for arbitrary scheme maps.
Source: Stacks Tags 03D2 and 03CY
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: the successive direct-image identifications are identity on sections, hence
compose to the comparison for b composed with a. The adjunction mate pastes,
and resComp gives precisely the identity identifications at the two ends. -/
theorem pull_composition {D : Type (u + 1)} [CommRing D]
    [Finite B] [Finite C] [Finite D] (a : B →+* C) (b : C →+* D)
    {Y X : Scheme.{u}} (f : Y ⟶ X) (M : Modules D X) :
    (modulePullback B f).map ((resComp a b X).inv.app M) ≫
        (pullRes a f).hom.app ((res b X).obj M) ≫
        (res a Y).map ((pullRes b f).hom.app M) ≫
        (resComp a b Y).hom.app ((modulePullback D f).obj M) =
      (pullRes (b.comp a) f).hom.app M := by
  exact pull_composition_aux a b f M

/-- Forgetting the constant-ring action, using Mathlib's module-sheaf forgetful functor.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
abbrev forgetModules (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    Modules A X ⥤ Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  SheafOfModules.toSheaf _

/-- Restricting scalars leaves the underlying abelian sheaf literally unchanged.
Source: Stacks Tag 03CY (blueprint: lem-cbc-finite-open-exchange-scalars). -/
def resForget (a : B →+* C) (X : Scheme.{u}) :
    res a X ⋙ forgetModules B X ≅ forgetModules C X := Iso.refl _

/-- The source transition on underlying abelian sheaf complexes, with the canonical
scalar identification included. Source: blueprint strict transition assertion
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def sourceStep [Finite B] [Finite C] (a : B →+* C)
    {U X' X : Scheme.{u}} (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j]
    (F : CochainComplex (Modules B U) ℤ) (G : CochainComplex (Modules C U) ℤ)
    (t : F ⟶ (resC a U).obj G) :
    ((forgetModules B X').mapHomologicalComplex (.up ℤ)).obj
        (((moduleJ B j ⋙ modulePullback B g).mapHomologicalComplex (.up ℤ)).obj F) ⟶
      ((forgetModules C X').mapHomologicalComplex (.up ℤ)).obj
        (((moduleJ C j ⋙ modulePullback C g).mapHomologicalComplex (.up ℤ)).obj G) :=
  ((forgetModules B X').mapHomologicalComplex (.up ℤ)).map
    (((moduleJ B j ⋙ modulePullback B g).mapHomologicalComplex (.up ℤ)).map t ≫
      (sourceResC a j g).hom.app G) ≫
    (NatIso.mapHomologicalComplex (resForget a X') (.up ℤ)).hom.app
      (((moduleJ C j ⋙ modulePullback C g).mapHomologicalComplex (.up ℤ)).obj G)

/-- The target transition on underlying abelian sheaf complexes.
Source: blueprint strict transition assertion
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def targetStep [Finite B] [Finite C] (a : B →+* C)
    {U' U X' : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X') [IsOpenImmersion j']
    (F : CochainComplex (Modules B U) ℤ) (G : CochainComplex (Modules C U) ℤ)
    (t : F ⟶ (resC a U).obj G) :
    ((forgetModules B X').mapHomologicalComplex (.up ℤ)).obj
        (((modulePullback B gU ⋙ moduleJ B j').mapHomologicalComplex (.up ℤ)).obj F) ⟶
      ((forgetModules C X').mapHomologicalComplex (.up ℤ)).obj
        (((modulePullback C gU ⋙ moduleJ C j').mapHomologicalComplex (.up ℤ)).obj G) :=
  ((forgetModules B X').mapHomologicalComplex (.up ℤ)).map
    (((modulePullback B gU ⋙ moduleJ B j').mapHomologicalComplex (.up ℤ)).map t ≫
      (targetResC a gU j').hom.app G) ≫
    (NatIso.mapHomologicalComplex (resForget a X') (.up ℤ)).hom.app
      (((modulePullback C gU ⋙ moduleJ C j').mapHomologicalComplex (.up ℤ)).obj G)


attribute [local irreducible] sourceStep targetStep openRes openResMap

set_option backward.isDefEq.respectTransparency false in
/-- Finite exchanges and their inverses form inverse maps of the actual strict towers.
The natural isomorphism is between towers of complexes, before any localization.
Source: blueprint strict reduction-tower assertion
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: apply exchange_transition at every successor level, then forget the action.
The scalar-forget identification is identity on sections. These equalities give
naturality for adjacent arrows and hence for their composites. The degreewise inverse
exchanges give an inverse natural transformation, by the component inverse identities.
This constructs the displayed natural isomorphism with exactly the specified components. -/
theorem exchange_strict_towers
    (A : ℕ → Type (u + 1)) [∀ n, CommRing (A n)] [∀ n, Finite (A n)]
    (a : ∀ n, A (n + 1) →+* A n)
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g)
    (F : ∀ n, CochainComplex (Modules (A n) U) ℤ)
    (t : ∀ n, F (n + 1) ⟶ (resC (a n) U).obj (F n)) :
    ∃ e : (Functor.ofOpSequence
          (X := fun n ↦ ((forgetModules (A n) X').mapHomologicalComplex (.up ℤ)).obj
            (((moduleJ (A n) j ⋙ modulePullback (A n) g).mapHomologicalComplex (.up ℤ)).obj
              (F n)))
          (fun n ↦ sourceStep (a n) j g (F (n + 1)) (F n) (t n)) :
          ℕᵒᵖ ⥤ CochainComplex (Sheaf (Scheme.ProEt.topology X') AddCommGrpCat.{u + 1}) ℤ) ≅
        (Functor.ofOpSequence
          (X := fun n ↦ ((forgetModules (A n) X').mapHomologicalComplex (.up ℤ)).obj
            (((modulePullback (A n) gU ⋙ moduleJ (A n) j').mapHomologicalComplex (.up ℤ)).obj
              (F n)))
          (fun n ↦ targetStep (a n) gU j' (F (n + 1)) (F n) (t n)) :
          ℕᵒᵖ ⥤ CochainComplex (Sheaf (Scheme.ProEt.topology X') AddCommGrpCat.{u + 1}) ℤ),
      (∀ n, e.hom.app (Opposite.op n) =
        ((forgetModules (A n) X').mapHomologicalComplex (.up ℤ)).map
          ((betaC (A n) gU j' j g h hsq).hom.app (F n))) ∧
      (∀ n, e.inv.app (Opposite.op n) =
        ((forgetModules (A n) X').mapHomologicalComplex (.up ℤ)).map
          ((betaC (A n) gU j' j g h hsq).inv.app (F n))) := by
  let e n := ((forgetModules (A n) X').mapHomologicalComplex (.up ℤ)).mapIso
    ((betaC (A n) gU j' j g h hsq).app (F n))
  apply sequence_iso _ _ e
  intro n
  dsimp only [e, Functor.mapIso_hom, Iso.app_hom]
  rw [sourceStep, targetStep]
  ext i : 1
  ext W x
  exact congrArg (fun k ↦ (k.f i).val.app W x)
    (exchange_transition (a n) gU j' j g h hsq (F (n + 1)) (F n) (t n)).1



/-- The source transition, linear for a compatible ambient ring-sheaf action.
Source: blueprint final ambient-action clause
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def ambientSourceStep [Finite B] [Finite C] (a : B →+* C)
    {U X' X : Scheme.{u}} (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X') RingCat.{u + 1})
    (rB : R ⟶ ringCoefficients B X') (rC : R ⟶ ringCoefficients C X')
    (hr : rB ≫ ringCoefficientMap a X' = rC)
    (F : CochainComplex (Modules B U) ℤ) (G : CochainComplex (Modules C U) ℤ)
    (t : F ⟶ (resC a U).obj G) :
    ((SheafOfModules.restrictScalars.{u + 1} rB).mapHomologicalComplex (.up ℤ)).obj
        (((moduleJ B j ⋙ modulePullback B g).mapHomologicalComplex (.up ℤ)).obj F) ⟶
      ((SheafOfModules.restrictScalars.{u + 1} rC).mapHomologicalComplex (.up ℤ)).obj
        (((moduleJ C j ⋙ modulePullback C g).mapHomologicalComplex (.up ℤ)).obj G) :=
  ((SheafOfModules.restrictScalars.{u + 1} rB).mapHomologicalComplex (.up ℤ)).map
    (((moduleJ B j ⋙ modulePullback B g).mapHomologicalComplex (.up ℤ)).map t ≫
      (sourceResC a j g).hom.app G) ≫
    (NatIso.mapHomologicalComplex (ambientRes a X' R rB rC hr) (.up ℤ)).hom.app
      (((moduleJ C j ⋙ modulePullback C g).mapHomologicalComplex (.up ℤ)).obj G)

/-- The target transition, linear for a compatible ambient ring-sheaf action.
Source: blueprint final ambient-action clause
(blueprint: lem-cbc-finite-open-exchange-scalars). -/
def ambientTargetStep [Finite B] [Finite C] (a : B →+* C)
    {U' U X' : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X') [IsOpenImmersion j']
    (R : Sheaf (Scheme.ProEt.topology X') RingCat.{u + 1})
    (rB : R ⟶ ringCoefficients B X') (rC : R ⟶ ringCoefficients C X')
    (hr : rB ≫ ringCoefficientMap a X' = rC)
    (F : CochainComplex (Modules B U) ℤ) (G : CochainComplex (Modules C U) ℤ)
    (t : F ⟶ (resC a U).obj G) :
    ((SheafOfModules.restrictScalars.{u + 1} rB).mapHomologicalComplex (.up ℤ)).obj
        (((modulePullback B gU ⋙ moduleJ B j').mapHomologicalComplex (.up ℤ)).obj F) ⟶
      ((SheafOfModules.restrictScalars.{u + 1} rC).mapHomologicalComplex (.up ℤ)).obj
        (((modulePullback C gU ⋙ moduleJ C j').mapHomologicalComplex (.up ℤ)).obj G) :=
  ((SheafOfModules.restrictScalars.{u + 1} rB).mapHomologicalComplex (.up ℤ)).map
    (((modulePullback B gU ⋙ moduleJ B j').mapHomologicalComplex (.up ℤ)).map t ≫
      (targetResC a gU j').hom.app G) ≫
    (NatIso.mapHomologicalComplex (ambientRes a X' R rB rC hr) (.up ℤ)).hom.app
      (((modulePullback C gU ⋙ moduleJ C j').mapHomologicalComplex (.up ℤ)).obj G)


attribute [local irreducible] ambientSourceStep ambientTargetStep ambientRes

set_option backward.isDefEq.respectTransparency false in
/-- The same strict-tower isomorphism is linear over every compatible ambient ring sheaf.
Source: blueprint final ambient-action clause
(blueprint: lem-cbc-finite-open-exchange-scalars).
Proof: restrict exchange_transition along each ambient coefficient map. Its equality
remains an equality of linear chain maps; ambientRes is identity on sections and is
natural, so the next coefficient restriction agrees. The successor squares and their
inverse squares therefore hold over R. Compose them to obtain all tower arrows.
The component inverse identities give inverse tower maps with the displayed components. -/
theorem exchange_ambient_towers
    (A : ℕ → Type (u + 1)) [∀ n, CommRing (A n)] [∀ n, Finite (A n)]
    (a : ∀ n, A (n + 1) →+* A n)
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g)
    (R : Sheaf (Scheme.ProEt.topology X') RingCat.{u + 1})
    (r : ∀ n, R ⟶ ringCoefficients (A n) X')
    (hr : ∀ n, r (n + 1) ≫ ringCoefficientMap (a n) X' = r n)
    (F : ∀ n, CochainComplex (Modules (A n) U) ℤ)
    (t : ∀ n, F (n + 1) ⟶ (resC (a n) U).obj (F n)) :
    ∃ e : (Functor.ofOpSequence
          (X := fun n ↦
            ((SheafOfModules.restrictScalars.{u + 1} (r n)).mapHomologicalComplex (.up ℤ)).obj
              (((moduleJ (A n) j ⋙ modulePullback (A n) g).mapHomologicalComplex (.up ℤ)).obj
                (F n)))
          (fun n ↦ ambientSourceStep (a n) j g R (r (n + 1)) (r n) (hr n)
            (F (n + 1)) (F n) (t n)) :
          ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{u + 1} R) ℤ) ≅
        (Functor.ofOpSequence
          (X := fun n ↦
            ((SheafOfModules.restrictScalars.{u + 1} (r n)).mapHomologicalComplex (.up ℤ)).obj
              (((modulePullback (A n) gU ⋙ moduleJ (A n) j').mapHomologicalComplex (.up ℤ)).obj
                (F n)))
          (fun n ↦ ambientTargetStep (a n) gU j' R (r (n + 1)) (r n) (hr n)
            (F (n + 1)) (F n) (t n)) :
          ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{u + 1} R) ℤ),
      (∀ n, e.hom.app (Opposite.op n) =
        ((SheafOfModules.restrictScalars.{u + 1} (r n)).mapHomologicalComplex (.up ℤ)).map
          ((betaC (A n) gU j' j g h hsq).hom.app (F n))) ∧
      (∀ n, e.inv.app (Opposite.op n) =
        ((SheafOfModules.restrictScalars.{u + 1} (r n)).mapHomologicalComplex (.up ℤ)).map
          ((betaC (A n) gU j' j g h hsq).inv.app (F n))) := by
  let e n := ((SheafOfModules.restrictScalars.{u + 1} (r n)).mapHomologicalComplex
    (.up ℤ)).mapIso ((betaC (A n) gU j' j g h hsq).app (F n))
  apply sequence_iso _ _ e
  intro n
  dsimp only [e, Functor.mapIso_hom, Iso.app_hom]
  rw [ambientSourceStep, ambientTargetStep]
  ext i : 1
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  let s := ((moduleJ (A (n + 1)) j ⋙ modulePullback (A (n + 1)) g).mapHomologicalComplex
    (.up ℤ)).map (t n) ≫ (sourceResC (a n) j g).hom.app (F n)
  let v := ((modulePullback (A (n + 1)) gU ⋙ moduleJ (A (n + 1)) j').mapHomologicalComplex
    (.up ℤ)).map (t n) ≫ (targetResC (a n) gU j').hom.app (F n)
  let b := (betaC (A (n + 1)) gU j' j g h hsq).hom.app (F (n + 1))
  let c := (betaC (A n) gU j' j g h hsq).hom.app (F n)
  let M := ((moduleJ (A n) j ⋙ modulePullback (A n) g).mapHomologicalComplex
    (.up ℤ)).obj (F n)
  let N := ((modulePullback (A n) gU ⋙ moduleJ (A n) j').mapHomologicalComplex
    (.up ℤ)).obj (F n)
  have hi := congrArg (fun k ↦ (k.f i).val.app W x)
    (exchange_transition (a n) gU j' j g h hsq (F (n + 1)) (F n) (t n)).1
  change (c.f i).val.app W
      (((ambientRes (a n) X' R (r (n + 1)) (r n) (hr n)).hom.app (M.X i)).val.app W
        ((s.f i).val.app W x)) =
    ((ambientRes (a n) X' R (r (n + 1)) (r n) (hr n)).hom.app (N.X i)).val.app W
      ((v.f i).val.app W ((b.f i).val.app W x))
  rw [ambientRes_apply, ambientRes_apply]
  exact hi


end AlgebraicGeometry.ProEtale.StrictTower.FiniteOpenScalars
