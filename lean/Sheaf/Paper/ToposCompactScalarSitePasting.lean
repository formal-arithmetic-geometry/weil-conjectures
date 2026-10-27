/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.CompactScalarSiteExchange
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.CategoryTheory.DerivedExactCube
import Sheaf.CategoryTheory.ExchangeMateCube

/-! # Mixed scalar/site normalization
Source: blueprint main-20261015, sk-thm-purity-transport, Steps 1 and 3
(blueprint: lem-pur-topos-compact-scalar-site-pasting).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u v
open CategoryTheory CategoryTheory.Limits
attribute [local irreducible] Functor.mapDerivedCategory
  Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategoryCompIso
namespace CategoryTheory.CompactScalarSite
variable {A B : Type (max u v)} [CommRing A] [CommRing B]

/-- Paste of the section-normalized restriction comparisons on the tilde system.
Source: Stacks 03DA and blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: lem-pur-topos-compact-scalar-site-pasting). -/
def tildeRestrictionPaste {φ : A →+* B} (D : Factorization.{u, v} φ)
    (ρp : derivedRestrict φ D.T.tildeW ⋙ D.tildeRA.functor ≅
      D.tildeRB.functor ⋙ derivedRestrict φ D.Y.tildeW)
    (ρj : derivedRestrict φ D.X.tildeW ⋙ D.j.tildeIA.functor ≅
      D.j.tildeIB.functor ⋙ derivedRestrict φ D.T.tildeW) :
    derivedRestrict φ D.X.tildeW ⋙ tildeFactorA φ D ≅
      tildeFactorB φ D ⋙ derivedRestrict φ D.Y.tildeW :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ρj _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ ρp ≪≫
    (Functor.associator _ _ _).symm

/-- The actual tilde coefficient arrow is the restriction-of-scalars transpose.
The restriction comparisons are characterized by their ordinary section identity
and their proper and open mates, rather than chosen arbitrarily.
Source: Stacks 03DA, 07A7, 0GL1 and blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: lem-pur-topos-compact-scalar-site-pasting).
Proof (node Step 5): the finite-free constituent lemma supplies the two normalized
restriction comparisons. Its direct-image identification uses the counit and its
open identification uses the invertible open unit. Paste these comparisons.
Scalar-adjunction transposition of the counit/balancing composite is this paste
after F_A of the insertion-of-one unit, by mate pasting. Apply the constituent
lemma to the tilde factorization; neither properness nor boundedness is needed. -/
theorem tilde_coefficient_transpose [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (D : Factorization.{u, v} (algebraMap A B)) :
    ∃ ρp : derivedRestrict (algebraMap A B) D.T.tildeW ⋙ D.tildeRA.functor ≅
        D.tildeRB.functor ⋙ derivedRestrict (algebraMap A B) D.Y.tildeW,
      ρp.inv = (mateEquiv D.tildeRB.adj D.tildeRA.adj
        (TwoSquare.mk _ _ _ _
          (Functor.mapDerivedCategorySquareIso D.p.tildeScalar.restriction).hom)).natTrans ∧
      ∃ ρj : derivedRestrict (algebraMap A B) D.X.tildeW ⋙ D.j.tildeIA.functor ≅
          D.j.tildeIB.functor ⋙ derivedRestrict (algebraMap A B) D.T.tildeW,
        (mateEquiv D.j.tildeIB.adj D.j.tildeIA.adj
          (TwoSquare.mk _ _ _ _ ρj.hom)).natTrans =
            (Functor.mapDerivedCategorySquareIso D.j.square.tildeScalar.restriction).inv ∧
        ∀ M : derived D.X.tildeW A,
          D.Y.tildeScalar.adjunction.homEquiv
              ((tildeFactorA (algebraMap A B) D).obj M)
              ((tildeFactorB (algebraMap A B) D).obj (D.X.tildeScalar.model.T.obj M))
              ((tildeCoefficient (algebraMap A B) D).app M) =
            (tildeFactorA (algebraMap A B) D).map
                (D.X.tildeScalar.adjunction.unit.app M) ≫
              (tildeRestrictionPaste D ρp ρj).hom.app (D.X.tildeScalar.model.T.obj M) := by
  sorry

private theorem mate_whisker_top
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (b : L' ⊣ R') {G G' : C ⥤ E} {H : D ⥤ F}
    (s : TwoSquare G' L L' H) (t : G ⟶ G') :
    mateEquiv a b (s.whiskerTop t) = (mateEquiv a b s).whiskerRight t := by
  ext M
  apply (b.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, TwoSquare.whiskerRight,
    Functor.whiskerLeft_app, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [mateEquiv_counit, mateEquiv_counit]
  simp [TwoSquare.whiskerTop, Category.assoc]

private theorem mate_whisker_bottom
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (b : L' ⊣ R') {G : C ⥤ E} {H H' : D ⥤ F}
    (s : TwoSquare G L L' H) (t : H ⟶ H') :
    mateEquiv a b (s.whiskerBottom t) = (mateEquiv a b s).whiskerLeft t := by
  ext M
  apply (b.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, TwoSquare.whiskerLeft,
    Functor.whiskerRight_app, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  have hn := b.counit.naturality (t.app M)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn, ← Category.assoc, mateEquiv_counit, mateEquiv_counit]
  simp [TwoSquare.whiskerBottom, Category.assoc, t.naturality]

private theorem restrict_underlying {φ : A →+* B} (W : Presentation.{u, v})
    {M N : modules W B} (f : M ⟶ N) :
    (underlying W A).map ((restrict φ W).map f) = (underlying W B).map f := rfl

private theorem normalized_chain {C : Type*} [Category C]
    {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ O₁₀ O₁₁ : C}
    (a : O₀ ⟶ O₁) (b : O₁ ⟶ O₂) (c : O₂ ⟶ O₃) (d : O₃ ⟶ O₄)
    (e : O₄ ⟶ O₅) (l : O₂ ⟶ O₆) (m : O₆ ⟶ O₇) (n : O₇ ⟶ O₅)
    (t : O₁ ⟶ O₆) (z : O₀ ⟶ O₈) (v : O₈ ⟶ O₆) (w : O₈ ⟶ O₇)
    (f : O₀ ⟶ O₉) (k : O₉ ⟶ O₁₀) (r : O₁₀ ⟶ O₅) (s : O₁₀ ⟶ O₄)
    (g : O₉ ⟶ O₁₁) (h : O₁₁ ⟶ O₃) (h₀ : O₁₁ ⟶ O₄)
    (hB : c ≫ d ≫ e = l ≫ m ≫ n) (ht : b ≫ l = t)
    (hn : a ≫ t = z ≫ v) (hv : v ≫ m = w)
    (hA : z ≫ w ≫ n = f ≫ k ≫ r) (hr : r = s ≫ e)
    (hg : g ≫ h₀ = k ≫ s) (hT : h ≫ d = h₀) :
    a ≫ b ≫ c ≫ d ≫ e = f ≫ g ≫ h ≫ d ≫ e := by
  calc
    _ = a ≫ b ≫ (l ≫ m ≫ n) := by rw [hB]
    _ = (a ≫ t) ≫ m ≫ n := by rw [← ht]; simp only [Category.assoc]
    _ = z ≫ (v ≫ m) ≫ n := by rw [hn]; simp only [Category.assoc]
    _ = f ≫ k ≫ r := by rw [hv]; exact hA
    _ = f ≫ (k ≫ s) ≫ e := by rw [hr]; simp only [Category.assoc]
    _ = f ≫ g ≫ (h ≫ d) ≫ e := by rw [← hg, hT]; simp only [Category.assoc]
    _ = _ := by simp only [Category.assoc]

/- Work before localization, where the underlying module-sheaf functor is faithful. -/
private theorem restriction_cube {φ : A →+* B} {T Y : Vertex.{u, v} φ}
    (p : InverseSquare φ T Y) (N : modules Y.W B) :
    p.tildeLA.lift.modules.map (Y.scalarPullback.restriction.hom.app N) ≫
        p.tildeScalar.restriction.hom.app (Y.NB.lift.modules.obj N) ≫
        (restrict φ T.tildeW).map (p.aB.hom.app N) =
      p.aA.hom.app ((restrict φ Y.W).obj N) ≫
        T.NA.lift.modules.map (p.scalar.restriction.hom.app N) ≫
        T.scalarPullback.restriction.hom.app (p.LB.lift.modules.obj N) := by
  apply (underlying T.tildeW A).map_injective
  apply (cancel_mono
    (T.NB.lift.moduleUnderlying.hom.app (p.LB.lift.modules.obj N) ≫
      T.ν.inverse.map (p.LB.lift.moduleUnderlying.hom.app N))).1
  simp only [Functor.map_comp, Category.assoc, restrict_underlying]
  have hna := T.NA.lift.moduleUnderlying.hom.naturality
    (p.scalar.restriction.hom.app N)
  change (underlying T.tildeW A).map
      (T.NA.lift.modules.map (p.scalar.restriction.hom.app N)) ≫
        T.NA.lift.moduleUnderlying.hom.app ((p.LB.lift.modules ⋙ restrict φ T.W).obj N) =
      T.NA.lift.moduleUnderlying.hom.app ((restrict φ Y.W ⋙ p.LA.lift.modules).obj N) ≫
        T.ν.inverse.map ((underlying T.W A).map (p.scalar.restriction.hom.app N)) at hna
  have hnt := p.tildeLA.lift.moduleUnderlying.hom.naturality
    (Y.scalarPullback.restriction.hom.app N)
  change (underlying T.tildeW A).map
      (p.tildeLA.lift.modules.map (Y.scalarPullback.restriction.hom.app N)) ≫
        p.tildeLA.lift.moduleUnderlying.hom.app
          ((Y.NB.lift.modules ⋙ restrict φ Y.tildeW).obj N) =
      p.tildeLA.lift.moduleUnderlying.hom.app
          ((restrict φ Y.W ⋙ Y.NA.lift.modules).obj N) ≫
        p.tildeP.inverse.map ((underlying Y.tildeW A).map
          (Y.scalarPullback.restriction.hom.app N)) at hnt
  dsimp only [Functor.comp_obj] at hna hnt
  have hv := congrArg p.tildeP.inverse.map (Y.scalarPullback.underlying_normalized N)
  have hr := congrArg T.ν.inverse.map (p.scalar.underlying_normalized N)
  simp only [Functor.map_comp] at hv hr
  exact normalized_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (p.normalizedB N)
    (p.tildeScalar.underlying_normalized (Y.NB.lift.modules.obj N))
    hnt hv (p.normalizedA ((restrict φ Y.W).obj N)).symm hr.symm hna
    (T.scalarPullback.underlying_normalized (p.LB.lift.modules.obj N))

private theorem derived_restriction_cube {φ : A →+* B} {T Y : Vertex.{u, v} φ}
    (p : InverseSquare φ T Y) :
    Functor.whiskerRight
        (Functor.mapDerivedCategorySquareIso Y.scalarPullback.restriction).hom
        (inverse p.tildeLA) ≫
      Functor.whiskerLeft (inverse Y.NB)
        (Functor.mapDerivedCategorySquareIso p.tildeScalar.restriction).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso p.aB).hom
        (derivedRestrict φ T.tildeW) =
    Functor.whiskerLeft (derivedRestrict φ Y.W)
        (Functor.mapDerivedCategorySquareIso p.aA).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso p.scalar.restriction).hom
        (inverse T.NA) ≫
      Functor.whiskerLeft (inverse p.LB)
        (Functor.mapDerivedCategorySquareIso T.scalarPullback.restriction).hom := by
  exact Functor.mapDerivedCategory_exactCube
    (restrict φ Y.W) Y.NA.lift.modules p.tildeLA.lift.modules
    Y.NB.lift.modules (restrict φ Y.tildeW) p.tildeLB.lift.modules
    (restrict φ T.tildeW) p.LB.lift.modules T.NB.lift.modules
    p.LA.lift.modules T.NA.lift.modules (restrict φ T.W)
    Y.scalarPullback.restriction p.tildeScalar.restriction p.aB p.aA
    p.scalar.restriction T.scalarPullback.restriction (restriction_cube p)

/- A cube can be transposed without unfolding the four adjunctions. -/
private theorem scalar_mate_cube
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    {L₀ : C₀ ⥤ D₀} {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃}
    {R₀ : D₀ ⥤ C₀} {R₁ : D₁ ⥤ C₁} {R₂ : D₂ ⥤ C₂} {R₃ : D₃ ⥤ C₃}
    {F : C₀ ⥤ C₁} {G : C₂ ⥤ C₃} {N : C₀ ⥤ C₂} {T : C₁ ⥤ C₃}
    {F' : D₀ ⥤ D₁} {G' : D₂ ⥤ D₃} {N' : D₀ ⥤ D₂} {T' : D₁ ⥤ D₃}
    (q₀ : L₀ ⊣ R₀) (q₁ : L₁ ⊣ R₁) (q₂ : L₂ ⊣ R₂) (q₃ : L₃ ⊣ R₃)
    (a : L₀ ⋙ F' ≅ F ⋙ L₁) (b : L₁ ⋙ T' ≅ T ⋙ L₃)
    (c : L₀ ⋙ N' ≅ N ⋙ L₂) (d : L₂ ⋙ G' ≅ G ⋙ L₃)
    (aa : N ⋙ G ≅ F ⋙ T) (bb : N' ⋙ G' ≅ F' ⋙ T')
    (ra : R₀ ⋙ F ≅ F' ⋙ R₁) (rb : R₁ ⋙ T ≅ T' ⋙ R₃)
    (rc : R₀ ⋙ N ≅ N' ⋙ R₂) (rd : R₂ ⋙ G ≅ G' ⋙ R₃)
    (ha : mateEquiv q₀ q₁ a.inv = ra.hom)
    (hb : mateEquiv q₁ q₃ b.inv = rb.hom)
    (hc : mateEquiv q₀ q₂ c.inv = rc.hom)
    (hd : mateEquiv q₂ q₃ d.inv = rd.hom)
    (h : Functor.whiskerRight rc.hom G ≫ Functor.whiskerLeft N' rd.hom ≫
        Functor.whiskerRight bb.hom R₃ =
      Functor.whiskerLeft R₀ aa.hom ≫ Functor.whiskerRight ra.hom T ≫
        Functor.whiskerLeft F' rb.hom) (M : C₀) :
    L₃.map (aa.hom.app M) ≫ b.inv.app (F.obj M) ≫ T'.map (a.inv.app M) =
      d.inv.app (N.obj M) ≫ G'.map (c.inv.app M) ≫ bb.hom.app (L₀.obj M) := by
  have he : TwoSquare.hComp a.inv b.inv =
      ((TwoSquare.hComp c.inv d.inv).whiskerTop aa.inv).whiskerBottom bb.hom := by
    apply (mateEquiv q₀ q₃).injective
    rw [mate_whisker_bottom, mate_whisker_top, mateEquiv_vcomp, mateEquiv_vcomp,
      ha, hb, hc, hd]
    ext K
    simp only [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id]
    have hh := NatTrans.congr_app h K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] at hh
    apply (cancel_epi (aa.hom.app (R₀.obj K))).1
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hh.symm
  have hh := congrArg (fun z ↦ z.app M) he
  simp only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at hh
  have hh' := congrArg (fun f ↦ L₃.map (aa.hom.app M) ≫ f) hh
  simpa only [Category.assoc, ← L₃.map_comp_assoc, Iso.hom_inv_id_app,
    Functor.map_id, Category.id_comp] using hh'

private theorem scalar_cube_inverse {φ : A →+* B} {T Y : Vertex.{u, v} φ}
    (p : InverseSquare φ T Y) (M : derived Y.W A) :
    T.tildeScalar.model.T.map ((Functor.mapDerivedCategorySquareIso p.aA).hom.app M) ≫
        T.scalarPullback.comparison.inv.app ((inverse p.LA).obj M) ≫
        (inverse T.NB).map (p.scalar.comparison.inv.app M) =
      p.tildeScalar.comparison.inv.app ((inverse Y.NA).obj M) ≫
        (inverse p.tildeLB).map (Y.scalarPullback.comparison.inv.app M) ≫
        (Functor.mapDerivedCategorySquareIso p.aB).hom.app (Y.scalar.model.T.obj M) := by
  exact scalar_mate_cube Y.scalar.adjunction T.scalar.adjunction
    Y.tildeScalar.adjunction T.tildeScalar.adjunction
    p.scalar.comparison T.scalarPullback.comparison Y.scalarPullback.comparison
    p.tildeScalar.comparison (Functor.mapDerivedCategorySquareIso p.aA)
    (Functor.mapDerivedCategorySquareIso p.aB)
    (Functor.mapDerivedCategorySquareIso p.scalar.restriction)
    (Functor.mapDerivedCategorySquareIso T.scalarPullback.restriction)
    (Functor.mapDerivedCategorySquareIso Y.scalarPullback.restriction)
    (Functor.mapDerivedCategorySquareIso p.tildeScalar.restriction)
    p.scalar.mate_normalized T.scalarPullback.mate_normalized
    Y.scalarPullback.mate_normalized p.tildeScalar.mate_normalized
    (derived_restriction_cube p) M

/- Conjugate only isomorphisms; the middle maps need not be invertible. -/
private theorem move_iso_sides {C : Type*} [Category C]
    {W X Y Z : C} (i : W ≅ X) (j : Y ≅ Z) (f : X ⟶ Z) (g : W ⟶ Y)
    (h : f ≫ j.inv = i.inv ≫ g) : g ≫ j.hom = i.hom ≫ f := by
  have hh := congrArg (fun k ↦ i.hom ≫ k ≫ j.hom) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using hh.symm

private theorem scalar_cube {φ : A →+* B} {T Y : Vertex.{u, v} φ}
    (p : InverseSquare φ T Y) (M : derived Y.W A) :
    (inverse p.tildeLB).map (Y.scalarPullback.comparison.inv.app M) ≫
        (Functor.mapDerivedCategorySquareIso p.aB).hom.app (Y.scalar.model.T.obj M) ≫
        (inverse T.NB).map (p.scalar.comparison.hom.app M) =
      p.tildeScalar.comparison.hom.app ((inverse Y.NA).obj M) ≫
        T.tildeScalar.model.T.map ((Functor.mapDerivedCategorySquareIso p.aA).hom.app M) ≫
        T.scalarPullback.comparison.inv.app ((inverse p.LA).obj M) := by
  have h := move_iso_sides
    (p.tildeScalar.comparison.app ((inverse Y.NA).obj M))
    ((inverse T.NB).mapIso (p.scalar.comparison.app M))
    (T.tildeScalar.model.T.map ((Functor.mapDerivedCategorySquareIso p.aA).hom.app M) ≫
      T.scalarPullback.comparison.inv.app ((inverse p.LA).obj M))
    ((inverse p.tildeLB).map (Y.scalarPullback.comparison.inv.app M) ≫
      (Functor.mapDerivedCategorySquareIso p.aB).hom.app (Y.scalar.model.T.obj M))
    (by simpa only [Category.assoc, Functor.mapIso_hom, Functor.mapIso_inv,
      Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv] using scalar_cube_inverse p M)
  simpa only [Category.assoc, Functor.mapIso_hom, Functor.mapIso_inv,
      Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv] using h

private theorem direct_mixed {φ : A →+* B} {T Y : Vertex.{u, v} φ}
    (p : InverseSquare φ T Y)
    (RA : DirectModel p.LA) (RB : DirectModel p.LB)
    (RtA : DirectModel p.tildeLA) (RtB : DirectModel p.tildeLB)
    (M : derived T.W A) : (directValue φ p RA RB RtA RtB).MixedAt φ M := by
  have h := exchangeMate_cube RA.adj RB.adj RtA.adj RtB.adj
    (inverse Y.NA) (inverse T.NA) (inverse Y.NB) (inverse T.NB)
    (Functor.mapDerivedCategorySquareIso p.aA).symm Y.scalarPullback.comparison
    T.scalarPullback.comparison (Functor.mapDerivedCategorySquareIso p.aB).symm
    p.scalar.comparison.hom p.tildeScalar.comparison.hom (scalar_cube p) M
  change (inverse Y.NB).map ((directScalar φ p.scalar RA RB).app M) ≫
      (directSiteB φ p RB RtB).app (T.scalar.model.T.obj M) ≫
      RtB.functor.map (T.scalarPullback.comparison.hom.app M) =
    Y.scalarPullback.comparison.hom.app (RA.functor.obj M) ≫
      Y.tildeScalar.model.T.map ((directSiteA φ p RA RtA).app M) ≫
      (directScalar φ p.tildeScalar RtA RtB).app ((inverse T.NA).obj M) at h
  unfold Value.MixedAt
  dsimp only [directValue]
  have hh := move_iso_sides
    (Y.scalarPullback.comparison.app (RA.functor.obj M)).symm
    (RtB.functor.mapIso (T.scalarPullback.comparison.app M)).symm
    ((inverse Y.NB).map ((directScalar φ p.scalar RA RB).app M) ≫
      (directSiteB φ p RB RtB).app (T.scalar.model.T.obj M))
    (Y.tildeScalar.model.T.map ((directSiteA φ p RA RtA).app M) ≫
      (directScalar φ p.tildeScalar RtA RtB).app ((inverse T.NA).obj M))
    (by simpa only [Category.assoc, Functor.mapIso_hom, Functor.mapIso_inv,
      Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv] using h)
  simpa only [Category.assoc, Functor.mapIso_hom, Functor.mapIso_inv,
      Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv] using hh

private theorem open_mixed {φ : A →+* B} {X T : Vertex.{u, v} φ}
    (j : OpenSquare φ X T) (M : derived X.W A) : (openValue φ j).MixedAt φ M := by
  have hc : Functor.whiskerRight
        (Functor.mapDerivedCategorySquareIso j.square.aA).inv X.tildeScalar.model.T ≫
      Functor.whiskerLeft (inverse T.NA) j.square.tildeScalar.comparison.inv ≫
      Functor.whiskerRight T.scalarPullback.comparison.inv (inverse j.square.tildeLB) =
    Functor.whiskerLeft (inverse j.square.LA) X.scalarPullback.comparison.inv ≫
      Functor.whiskerRight j.square.scalar.comparison.inv (inverse X.NB) ≫
      Functor.whiskerLeft T.scalar.model.T
        (Functor.mapDerivedCategorySquareIso j.square.aB).inv := by
    ext N
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    have h := move_iso_sides
      (X.tildeScalar.model.T.mapIso
        ((Functor.mapDerivedCategorySquareIso j.square.aA).app N)).symm
      ((Functor.mapDerivedCategorySquareIso j.square.aB).app (T.scalar.model.T.obj N)).symm
      (j.square.tildeScalar.comparison.inv.app ((inverse T.NA).obj N) ≫
        (inverse j.square.tildeLB).map (T.scalarPullback.comparison.inv.app N))
      (X.scalarPullback.comparison.inv.app ((inverse j.square.LA).obj N) ≫
        (inverse X.NB).map (j.square.scalar.comparison.inv.app N))
      (by simpa only [Category.assoc, Functor.mapIso_hom, Functor.mapIso_inv,
        Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv] using
        (scalar_cube_inverse j.square N).symm)
    simpa only [Category.assoc, Functor.mapIso_hom, Functor.mapIso_inv,
      Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv] using h.symm
  have h := scalar_mate_cube j.IA.adj j.IB.adj j.tildeIA.adj j.tildeIB.adj
    j.beta j.eB j.eA j.tildeBeta
    X.scalarPullback.comparison.symm T.scalarPullback.comparison.symm
    j.square.scalar.comparison.symm
    (Functor.mapDerivedCategorySquareIso j.square.aB).symm
    (Functor.mapDerivedCategorySquareIso j.square.aA).symm
    j.square.tildeScalar.comparison.symm
    j.beta_normalized j.eB_normalized j.eA_normalized j.tildeBeta_normalized hc M
  have hh := move_iso_sides
    (T.tildeScalar.model.T.mapIso (j.eA.app M) ≪≫ j.tildeBeta.app ((inverse X.NA).obj M))
    ((inverse T.NB).mapIso (j.beta.app M) ≪≫ j.eB.app (X.scalar.model.T.obj M))
    (j.tildeIB.functor.map (X.scalarPullback.comparison.inv.app M))
    (T.scalarPullback.comparison.inv.app (j.IA.functor.obj M))
    (by simpa only [Iso.trans_inv, Category.assoc, Functor.mapIso_inv,
      Iso.app_inv, Iso.symm_hom] using h)
  simpa only [Value.MixedAt, openValue, Iso.trans_hom, Category.assoc,
    Functor.mapIso_hom, Iso.app_hom] using hh.symm

private theorem compose_mixed {φ : A →+* B} {X Y Z : Vertex.{u, v} φ}
    (K : Value φ X Y) (G : Value φ Y Z)
    (hK : ∀ M, K.MixedAt φ M) (hG : ∀ M, G.MixedAt φ M)
    (M : derived X.W A) : (composeValue φ K G).MixedAt φ M := by
  have hk := hK M
  have hg := hG (K.FA.obj M)
  have hn := G.tildeC.naturality (K.siteA.app M)
  have hc := G.siteB.naturality (K.c.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn hc
  unfold Value.MixedAt at hk hg ⊢
  simp only [composeValue, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.comp_map, Functor.comp_obj,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  simp only [← Functor.map_comp, ← Functor.map_comp_assoc]
  rw [hk]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hg]
  rw [← reassoc_of% hc]

/-- The mixed identity simultaneously for every finite word, including the empty word.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: lem-pur-topos-compact-scalar-site-pasting).
Proof (node Step 6): induct on the word. The identity word uses unitors. Direct
letters use the counit-mate cube, open letters the inverse open-unit cube, as in
Steps 1--3 of topos_compact_scalar_site_pasting. Expand both comparisons of a
concatenation, use naturality to interchange the middle maps, and apply the two
induction hypotheses at the indicated intermediate inputs. The same induction
shows the site arrows are invertible, using exactly SiteInvertibleAt. -/
theorem word_mixed [Algebra A B] [Module.Finite A B] [Module.Free A B]
    {X Y : Vertex.{u, v} (algebraMap A B)}
    (H : Word (algebraMap A B) X Y) (M : derived X.W A)
    (h : H.SiteInvertibleAt (algebraMap A B) M (X.scalar.model.T.obj M)) :
    IsIso (H.value.siteA.app M) ∧
      IsIso (H.value.siteB.app (X.scalar.model.T.obj M)) ∧ H.value.MixedAt (algebraMap A B) M := by
  have mixed {X Y : Vertex.{u, v} (algebraMap A B)}
      (H : Word (algebraMap A B) X Y) : ∀ M, H.value.MixedAt (algebraMap A B) M := by
    induction H with
    | identity X =>
      intro M
      simp [Word.value, identityValue, Value.MixedAt]
    | direct p RA RB RtA RtB => exact direct_mixed p RA RB RtA RtB
    | openExtension j => exact open_mixed j
    | compose K G ihK ihG => exact compose_mixed K.value G.value ihK ihG
  -- Track independent inputs: coefficient comparison need not identify their objects.
  have invertible {X Y : Vertex.{u, v} (algebraMap A B)}
      (H : Word (algebraMap A B) X Y) (MA : derived X.W A) (MB : derived X.W B)
      (h : H.SiteInvertibleAt (algebraMap A B) MA MB) :
      IsIso (H.value.siteA.app MA) ∧ IsIso (H.value.siteB.app MB) := by
    induction H with
    | identity X =>
      constructor <;> simp only [Word.value, identityValue, NatTrans.comp_app] <;>
        infer_instance
    | direct p RA RB RtA RtB => exact h
    | openExtension j =>
      constructor
      · change IsIso (j.eA.hom.app MA); infer_instance
      · change IsIso (j.eB.hom.app MB); infer_instance
    | compose K G ihK ihG =>
      obtain ⟨hkA, hkB⟩ := ihK MA MB h.1
      obtain ⟨hgA, hgB⟩ := ihG (K.value.FA.obj MA) (K.value.FB.obj MB) h.2
      constructor <;>
        simp only [Word.value, composeValue, NatTrans.comp_app, Functor.whiskerLeft_app,
          Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
          Category.id_comp, Category.comp_id] <;> infer_instance
  exact ⟨(invertible H M _ h).1, (invertible H M _ h).2, mixed H M⟩

/-- Mixed scalar/site normalization for a direct-image/open factorization.
The hypotheses ask only for invertibility on the two displayed inputs, and do not
assert that a comparison pullback or scalar restriction is faithful.

Source: blueprint main-20261015, sk-thm-purity-transport, Steps 1 and 3;
Stacks 07A7, 0E46, 0E47 and 0E8I
(blueprint: lem-pur-topos-compact-scalar-site-pasting).

Proof, node Steps 1--4:
1. The ordinary restriction/inverse-image comparison is the identity under the
   normalized underlying-sheaf identifications. The two ordinary inverse-image
   site squares have the same set-level commutation. Their cube therefore commutes
   by faithfulness on ordinary module sheaves; no assertion about faithfulness on
   derived morphisms is made. Exact-square composition carries this cube to the
   unbounded derived categories (lem-pod-derived-exact-square-composition).
   Scalar adjunction mates identify the resulting maps with the specified tensor
   comparisons: their units insert one, so their inverses pull back both entries.
2. Take geometric right mates. Mate pasting identifies the resulting cube with
   the direct-image constituent square for chi and d, using their actual counits
   (lem-weil-pbc-mate-pasting and def-weil-pbc-adjunction-mate).
3. Take open left mates of the inverse cube. Their transposes are the specified
   open units, hence the inverse arrows are beta^{-1} and e^{-1}. Invert this
   equality, using the Cartesian open square and the open balancing isomorphisms.
4. Expand c and C. Naturality of chi moves the image of e across chi. Substitute
   the open square from Step 3 and the direct-image square from Step 2. Naturality
   of d at beta gives precisely the right-hand side below. All factors are natural
   transformations, so this equality is natural in M.
The remaining node Steps 5--11 are the transpose and finite-paste statements below. -/
theorem topos_compact_scalar_site_pasting
    [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (D : Factorization.{u, v} (algebraMap A B)) (M : derived D.X.W A)
    (hA : IsIso ((directSiteA (algebraMap A B) D.p D.RA D.tildeRA).app
      (D.j.IA.functor.obj M)))
    (hB : IsIso ((directSiteB (algebraMap A B) D.p D.RB D.tildeRB).app
      (D.j.IB.functor.obj (D.X.scalar.model.T.obj M)))) :
    D.Y.tildeScalar.model.T.map ((siteA (algebraMap A B) D).app M) ≫
        (tildeCoefficient (algebraMap A B) D).app ((inverse D.X.NA).obj M) ≫
        (tildeFactorB (algebraMap A B) D).map
          (D.X.scalarPullback.comparison.inv.app M) =
      D.Y.scalarPullback.comparison.inv.app ((factorA (algebraMap A B) D).obj M) ≫
        (inverse D.Y.NB).map ((coefficient (algebraMap A B) D).app M) ≫
        (siteB (algebraMap A B) D).app (D.X.scalar.model.T.obj M) := by
  have h := word_mixed
    (Word.compose (Word.openExtension D.j)
      (Word.direct D.p D.RA D.RB D.tildeRA D.tildeRB)) M ⟨True.intro, hA, hB⟩
  exact h.2.2

private theorem transfer_value {φ : A →+* B} {X Y : Vertex.{u, v} φ}
    (H H' : Value φ X Y) (θ : Comparison φ H H') (M : derived X.W A)
    (hA : IsIso (H.siteA.app M)) (hm : H.MixedAt φ M) (hm' : H'.MixedAt φ M)
    (hsite : θ.SiteAt φ M (X.scalar.model.T.obj M))
    (hscalar : θ.ScalarAt φ M) :
    θ.TildeScalarAt φ ((inverse X.NA).obj M) := by
  have := hA
  obtain ⟨hsA, hsB⟩ := hsite
  unfold Comparison.TildeScalarAt
  apply (cancel_epi (Y.tildeScalar.model.T.map (H.siteA.app M))).1
  apply (cancel_mono
    (H'.tildeFB.map (X.scalarPullback.comparison.inv.app M))).1
  unfold Value.MixedAt at hm hm'
  have hs := congrArg Y.tildeScalar.model.T.map hsA
  simp only [Functor.map_comp] at hs
  have hn := Y.scalarPullback.comparison.inv.naturality (θ.A.app M)
  have hb := θ.tildeB.naturality (X.scalarPullback.comparison.inv.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn hb
  calc
    _ = Y.tildeScalar.model.T.map ((inverse Y.NA).map (θ.A.app M)) ≫
        (Y.tildeScalar.model.T.map (H'.siteA.app M) ≫
          H'.tildeC.app ((inverse X.NA).obj M) ≫
          H'.tildeFB.map (X.scalarPullback.comparison.inv.app M)) := by
      simp only [Category.assoc]
      rw [← reassoc_of% hs]
    _ = Y.scalarPullback.comparison.inv.app (H.FA.obj M) ≫
        (inverse Y.NB).map (Y.scalar.model.T.map (θ.A.app M) ≫ H'.c.app M) ≫
          H'.siteB.app (X.scalar.model.T.obj M) := by
      rw [hm', ← Category.assoc, hn]
      simp only [Functor.map_comp, Category.assoc]
    _ = Y.scalarPullback.comparison.inv.app (H.FA.obj M) ≫
        (inverse Y.NB).map (H.c.app M) ≫
          (H.siteB.app (X.scalar.model.T.obj M) ≫
            θ.tildeB.app ((inverse X.NB).obj (X.scalar.model.T.obj M))) := by
      rw [hscalar]
      simp only [Functor.map_comp, Category.assoc]
      rw [hsB]
    _ = (Y.tildeScalar.model.T.map (H.siteA.app M) ≫
        H.tildeC.app ((inverse X.NA).obj M) ≫
        H.tildeFB.map (X.scalarPullback.comparison.inv.app M)) ≫
          θ.tildeB.app ((inverse X.NB).obj (X.scalar.model.T.obj M)) := by
      rw [hm]
      simp only [Category.assoc]
    _ = _ := by
      simp only [Category.assoc]
      rw [hb]


/-- Transfer of a normalized scalar square to all comparison-pullback inputs.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: lem-pur-topos-compact-scalar-site-pasting).
Proof (node Step 10): apply the mixed identity to H and H'. Insert their normalized
site squares and the untilde scalar square. Cancel C in A coefficients, which is
invertible on M, and the image under H'_B of delta_X, which is invertible. The
remaining equality is precisely the tilde scalar square at N_X M. This uses no
faithfulness or essential surjectivity of any derived functor. -/
theorem transfer_scalar_square [Algebra A B] [Module.Finite A B] [Module.Free A B]
    {X Y : Vertex.{u, v} (algebraMap A B)}
    (H H' : Word (algebraMap A B) X Y) (θ : Comparison (algebraMap A B) H.value H'.value)
    (M : derived X.W A)
    (hH : H.SiteInvertibleAt (algebraMap A B) M (X.scalar.model.T.obj M))
    (hH' : H'.SiteInvertibleAt (algebraMap A B) M (X.scalar.model.T.obj M))
    (hsite : θ.SiteAt (algebraMap A B) M (X.scalar.model.T.obj M))
    (hscalar : θ.ScalarAt (algebraMap A B) M) :
    θ.TildeScalarAt (algebraMap A B) ((inverse X.NA).obj M) := by
  obtain ⟨hA, _, hm⟩ := word_mixed H M hH
  obtain ⟨_, _, hm'⟩ := word_mixed H' M hH'
  exact transfer_value H.value H'.value θ M hA hm hm' hsite hscalar

/-- Input conjugation and independence of the presentation of the input object.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: lem-pur-topos-compact-scalar-site-pasting).
Proof (node Step 11): naturality of c_H, c_H', theta and the scalar functor carries
both sides across i and its inverse. For two presentations i and i', the same
calculation with i^{-1} followed by i' gives their canonical conjugation. Thus the
assertion is independent of the chosen presentation, without requiring pullback
to be essentially surjective. -/
theorem scalar_square_conjugation {φ : A →+* B} {X Y : Vertex.{u, v} φ}
    {H H' : Value φ X Y} (θ : Comparison φ H H')
    (K K' : derived X.tildeW A) (i : K ≅ K') :
    θ.TildeScalarAt φ K ↔ θ.TildeScalarAt φ K' := by
  let a : H.tildeFA ⋙ Y.tildeScalar.model.T ⟶ X.tildeScalar.model.T ⋙ H'.tildeFB :=
    Functor.whiskerRight θ.tildeA Y.tildeScalar.model.T ≫ H'.tildeC
  let b : H.tildeFA ⋙ Y.tildeScalar.model.T ⟶ X.tildeScalar.model.T ⋙ H'.tildeFB :=
    H.tildeC ≫ Functor.whiskerLeft X.tildeScalar.model.T θ.tildeB
  change a.app K = b.app K ↔ a.app K' = b.app K'
  have transport {L L' : derived X.tildeW A} (e : L ≅ L')
      (h : a.app L = b.app L) : a.app L' = b.app L' := by
    apply (cancel_epi ((H.tildeFA ⋙ Y.tildeScalar.model.T).map e.hom)).1
    rw [a.naturality, b.naturality, h]
  exact ⟨transport i, transport i.symm⟩

/-- The normalized site square for generators, finite pastes and their inputwise
inverses, including proper-refinement comparisons expressed by these pastes.
Source: Stacks 07A7, 0E46, 0E47 and blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: lem-pur-topos-compact-scalar-site-pasting).
Proof (node Steps 7--9): direct compositors are conjugates of inverse-image
composition. Mate pasting along adjunctions proves their square. The left-mate
version proves the open compositor square, using its open-unit normalization.
For an exchange use lem-weil-pbc-exchange-mate-cube, invert at the indicated
inputs, and take the two open mates. Their unit transposes are e inverse.
Vertical pastes substitute the two squares; horizontal pastes additionally use
naturality. For an inverse multiply by its two component inverses. Induction on
PasteAt proves the assertion, without requiring any derived functor faithful. -/
theorem paste_site {φ : A →+* B} {X Y : Vertex.{u, v} φ}
    {H H' : Value φ X Y} (θ : Comparison φ H H')
    (MA : derived X.W A) (MB : derived X.W B) (h : PasteAt φ θ MA MB) :
    θ.SiteAt φ MA MB := by
  sorry

/-- Scalar/refinement and scalar/composition equations transfer along every
normalized finite paste, at every comparison-pullback input.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: lem-pur-topos-compact-scalar-site-pasting).
Proof (node Steps 6--10): word_mixed supplies the two mixed identities and the
invertibility of the site arrows at the displayed inputs. paste_site gives the
normalized site squares, including inverse and refinement pastes. Substitute
these and the untilde scalar square into the mixed identities. Cancel the A-site
comparison and the image of delta_X under the target B-word. The remaining
equality is the asserted tilde scalar square. No faithfulness is used. -/
theorem paste_transfer [Algebra A B] [Module.Finite A B] [Module.Free A B]
    {X Y : Vertex.{u, v} (algebraMap A B)}
    (H H' : Word (algebraMap A B) X Y)
    (θ : Comparison (algebraMap A B) H.value H'.value) (M : derived X.W A)
    (hH : H.SiteInvertibleAt (algebraMap A B) M (X.scalar.model.T.obj M))
    (hH' : H'.SiteInvertibleAt (algebraMap A B) M (X.scalar.model.T.obj M))
    (hpaste : PasteAt (algebraMap A B) θ M (X.scalar.model.T.obj M))
    (hscalar : θ.ScalarAt (algebraMap A B) M) :
    θ.TildeScalarAt (algebraMap A B) ((inverse X.NA).obj M) := by
  exact transfer_scalar_square H H' θ M hH hH'
    (paste_site θ M (X.scalar.model.T.obj M) hpaste) hscalar

end CategoryTheory.CompactScalarSite
