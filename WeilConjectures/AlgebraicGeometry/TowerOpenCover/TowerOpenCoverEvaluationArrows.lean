/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverTriangleData
import all WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerOpenAdjunctionEvaluation
import all WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction

/-! Compact-support and finite-level transport for the tower open-cover triangle.
Source: latest blueprint, sec-smooth-purity/sk-prop-tower-geometric,
`sk-prop-sp-tower-geometric-gluing.proof.md`, Gluing and Levels paragraphs.
(blueprint: lem-dla1-tower-open-cover-evaluation-arrows).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.TowerOpenCover

private theorem nested_evaluation
    {C A B C' A' B' : Type*}
    [Category* C] [Category* A] [Category* B]
    [Category* C'] [Category* A'] [Category* B']
    {r : C ⥤ A} {s : A ⥤ B} {t : C ⥤ B} {L : A ⥤ C} {K : B ⥤ C}
    {r' : C' ⥤ A'} {s' : A' ⥤ B'} {t' : C' ⥤ B'}
    {L' : A' ⥤ C'} {K' : B' ⥤ C'}
    (a : L ⊣ r) (b : K ⊣ t) (a' : L' ⊣ r') (b' : K' ⊣ t')
    (c : r ⋙ s ≅ t) (c' : r' ⋙ s' ≅ t')
    (EC : C ⥤ C') (EA : A ⥤ A') (EB : B ⥤ B')
    (p : L ⋙ EC ≅ EA ⋙ L') (q : r ⋙ EA ≅ EC ⋙ r')
    (P : K ⋙ EC ≅ EB ⋙ K') (Q : t ⋙ EB ≅ EC ⋙ t')
    (e : s ⋙ EB ≅ EA ⋙ s')
    (hu : ∀ Y, EA.map (a.unit.app Y) ≫ q.hom.app (L.obj Y) ≫
      r'.map (p.hom.app Y) = a'.unit.app (EA.obj Y))
    (hc : ∀ Z, EC.map (b.counit.app Z) = P.hom.app (t.obj Z) ≫
      K'.map (Q.hom.app Z) ≫ b'.counit.app (EC.obj Z))
    (hcomp : ∀ Z, EB.map (c.hom.app Z) ≫ Q.hom.app Z =
      e.hom.app (r.obj Z) ≫ s'.map (q.hom.app Z) ≫ c'.hom.app (EC.obj Z))
    (M : C) :
    EC.map (nestedCounit a b c M) ≫ p.hom.app (r.obj M) ≫ L'.map (q.hom.app M) =
      P.hom.app (t.obj M) ≫ K'.map (Q.hom.app M) ≫
        nestedCounit a' b' c' (EC.obj M) := by
  let z := p.hom.app (r.obj M) ≫ L'.map (q.hom.app M)
  let v := c.inv.app M ≫ s.map (a.unit.app (r.obj M)) ≫ c.hom.app (L.obj (r.obj M))
  let v' := c'.inv.app (EC.obj M) ≫ s'.map (a'.unit.app (r'.obj (EC.obj M))) ≫
    c'.hom.app (L'.obj (r'.obj (EC.obj M)))
  have hi : EB.map (c.inv.app M) ≫ e.hom.app (r.obj M) ≫ s'.map (q.hom.app M) =
      Q.hom.app M ≫ c'.inv.app (EC.obj M) := by
    apply (cancel_mono (c'.hom.app (EC.obj M))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← hcomp]
    simp only [← EB.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact (Category.comp_id _).symm
  have hz : EB.map v ≫ Q.hom.app (L.obj (r.obj M)) ≫ t'.map z =
      Q.hom.app M ≫ v' := by
    dsimp only [v, v']
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hcomp]
    rw [← c'.hom.naturality]
    dsimp only [Functor.comp_map]
    have he := e.hom.naturality (a.unit.app (r.obj M))
    dsimp only [Functor.comp_map] at he
    rw [reassoc_of% he]
    dsimp only [Functor.comp_map, z]
    simp only [Functor.map_comp, Category.assoc]
    have hs := congrArg s'.map (hu (r.obj M))
    simp only [Functor.map_comp] at hs
    rw [reassoc_of% hs]
    have hn := congrArg s'.map (a'.unit.naturality (q.hom.app M))
    simp only [Functor.comp_map, Functor.id_map, Functor.map_comp] at hn
    rw [← reassoc_of% hn]
    rw [reassoc_of% hi]
    rfl
  change EC.map (K.map v ≫ b.counit.app (L.obj (r.obj M))) ≫ z =
    P.hom.app (t.obj M) ≫ K'.map (Q.hom.app M) ≫
      (K'.map v' ≫ b'.counit.app (L'.obj (r'.obj (EC.obj M))))
  rw [EC.map_comp, hc]
  simp only [Category.assoc]
  have hp := P.hom.naturality v
  change EC.map (K.map v) ≫ P.hom.app (t.obj (L.obj (r.obj M))) =
    P.hom.app (t.obj M) ≫ K'.map (EB.map v) at hp
  rw [reassoc_of% hp]
  have hb := b'.counit.naturality z
  change K'.map (t'.map z) ≫ b'.counit.app (L'.obj (r'.obj (EC.obj M))) =
    b'.counit.app (EC.obj (L.obj (r.obj M))) ≫ z at hb
  rw [← hb]
  simp only [← K'.map_comp_assoc]
  rw [hz]


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HasDerivedCategory.standard

private theorem finite_open_unit
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ)
    (M : SpTowerShriek.D l E U) :
    (SpTowerShriek.Ev l E U n).map ((o.openOp j).derivedAdjunction.unit.app M) ≫
      ((o.geometry j).pullEvaluation n).hom.app ((SpTowerShriek.openD l E b (o.openOp j)).obj M) ≫
      (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) j).map
        ((SpTowerShriek.openEvaluation l E b (o.openOp j) n).hom.app M) =
      (finiteAdjunction l E b j n).unit.app ((SpTowerShriek.Ev l E U n).obj M) := by
  let : Finite (SpTowerShriek.R l E n) := b.finite n
  have h := SpTowerShriek.open_adjunction_unit_evaluation l E b (o.openOp j) n M
  rw [SpTowerShriek.exact_adjunction_eq_local] at h
  exact h

private theorem finite_open_counit
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ)
    (M : SpTowerShriek.D l E X) :
    (SpTowerShriek.Ev l E X n).map ((o.openOp j).derivedAdjunction.counit.app M) =
      (SpTowerShriek.openEvaluation l E b (o.openOp j) n).hom.app
        ((SpTowerShriek.pull l E b (o.geometry j)).obj M) ≫
      (sfIntrinsicDerivedOpen (SpTowerShriek.R l E n) j).map
        (((o.geometry j).pullEvaluation n).hom.app M) ≫
      (finiteAdjunction l E b j n).counit.app ((SpTowerShriek.Ev l E X n).obj M) := by
  let e := SpTowerShriek.openEvaluation l E b (o.openOp j) n
  let d := (o.geometry j).pullEvaluation n
  exact ((SheafOfModules.RingedOpenScalar.equations_of_inverseMate e d.symm
    (o.openOp j).derivedAdjunction (finiteAdjunction l E b j n)
    (SheafOfModules.RingedOpenScalar.inverseMate_of_unit e d.symm
      (o.openOp j).derivedAdjunction (finiteAdjunction l E b j n)
      (finite_open_unit l E b o j n))).2 M).symm

private theorem evaluated_alpha
    {W U X : Scheme.{u}} (a : W ⟶ U) (j : U ⟶ X) (k : W ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] [IsOpenImmersion k]
    (w : a ≫ j = k) (M : SpTowerShriek.D l E X) (n : ℕ) :
    (SpTowerShriek.Ev l E X n).map (alpha l E b o a j k w M) ≫
        (supportEvaluation l E b o j n).hom.app M =
      (supportEvaluation l E b o k n).hom.app M ≫
        finiteAlpha l E b a j k w n ((SpTowerShriek.Ev l E X n).obj M) := by
  subst k
  let : Finite (SpTowerShriek.R l E n) := b.finite n
  have h := nested_evaluation (o.openOp j).derivedAdjunction
    (o.openOp (a ≫ j)).derivedAdjunction
    (finiteAdjunction l E b j n) (finiteAdjunction l E b (a ≫ j) n)
    (o.comp a j) (proEtaleConstantRingPullbackComposition a j (SpTowerShriek.R l E n))
    (SpTowerShriek.Ev l E X n) (SpTowerShriek.Ev l E U n) (SpTowerShriek.Ev l E W n)
    (SpTowerShriek.openEvaluation l E b (o.openOp j) n) ((o.geometry j).pullEvaluation n)
    (SpTowerShriek.openEvaluation l E b (o.openOp (a ≫ j)) n)
    ((o.geometry (a ≫ j)).pullEvaluation n) ((o.geometry a).pullEvaluation n)
    (finite_open_unit l E b o j n) (finite_open_counit l E b o (a ≫ j) n)
    (o.comp_evaluation a j n) M
  simpa only [alpha, finiteAlpha, supportEvaluation, Iso.trans_hom, Iso.symm_hom,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Category.id_comp, Category.comp_id, eqToIso_refl, Iso.trans_refl, Category.assoc] using h


/-- Exact coefficient evaluation carries the normalized nested counit and ordinary
open counit to their finite counterparts. No cover or intersection is needed.

Source: latest blueprint, tower-geometric Levels paragraph; normalized units,
counits and compositors in the Operations data.
(blueprint: lem-dla1-tower-open-cover-evaluation-arrows).

Proof: First descend the ordinary unit and counit evaluation squares through exact
termwise localization. The mapDerivedCategory identity and composition comparisons
identify their descents with unit_termwise and counit_termwise. The result is the
adjunction evaluation square for derivedAdjunction and finiteAdjunction, with the
pullEvaluation and openEvaluation comparisons. Expand nestedCounit as the inverse
homEquiv, namely extension applied to the transpose followed by the counit. Naturality
of openEvaluation moves the transpose across extension. The unit evaluation square
then replaces its unit by the finite unit; comp_evaluation replaces the compositor
by the finite pullback compositor. Cancel the inverse comparison maps. This is exactly
the displayed alpha square. The counit square is the descended counit_evaluation,
composed with the pull comparison; its composite comparison is supportEvaluation.
Identity and empty-open cases obey the same adjunction identities. -/
theorem tower_open_cover_evaluation_arrows {W U X : Scheme.{u}}
    (a : W ⟶ U) (j : U ⟶ X) (k : W ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] [IsOpenImmersion k]
    (w : a ≫ j = k) (M : SpTowerShriek.D l E X) (n : ℕ) :
    ((SpTowerShriek.Ev l E X n).map (alpha l E b o a j k w M) ≫
        (supportEvaluation l E b o j n).hom.app M =
      (supportEvaluation l E b o k n).hom.app M ≫
        finiteAlpha l E b a j k w n ((SpTowerShriek.Ev l E X n).obj M)) ∧
    ((SpTowerShriek.Ev l E X n).map ((o.openOp j).derivedAdjunction.counit.app M) =
      (supportEvaluation l E b o j n).hom.app M ≫
        (finiteAdjunction l E b j n).counit.app ((SpTowerShriek.Ev l E X n).obj M)) := by
  constructor
  · exact evaluated_alpha l E b o a j k w M n
  · simpa only [supportEvaluation, Iso.trans_hom, Iso.symm_hom,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      Category.id_comp, Category.comp_id, Category.assoc] using
      finite_open_counit l E b o j n M

end AlgebraicGeometry.ProEtale.TowerOpenCover
