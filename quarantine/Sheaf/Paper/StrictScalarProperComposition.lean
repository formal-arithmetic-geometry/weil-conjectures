/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.Paper.CompactSupportStrictScalarMate

import Sheaf.Paper.StrictScalarPullComposition

/-! # Scalar compatibility with the normalized strict proper compositor

Source: Stacks Project, Tags 07A6, 0B56, 0D6D; strict scalar refinement, Steps 3--6 and 9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
attribute [local irreducible] T U scalarAdj properRestriction openTensor strictScalarPull
  AlgebraicGeometry.ProEtale.StrictTower.G AlgebraicGeometry.ProEtale.StrictTower.J
  AlgebraicGeometry.ProEtale.StrictTower.R

private theorem scalar_cube_mates
    {VA WA SA ZA VB WB SB ZB : Type*}
    [Category VA] [Category WA] [Category SA] [Category ZA]
    [Category VB] [Category WB] [Category SB] [Category ZB]
    {gpA : ZA ⥤ WA} {rpA : WA ⥤ ZA} {grA : SA ⥤ VA} {rrA : VA ⥤ SA}
    {gpB : ZB ⥤ WB} {rpB : WB ⥤ ZB} {grB : SB ⥤ VB} {rrB : VB ⥤ SB}
    (apA : gpA ⊣ rpA) (arA : grA ⊣ rrA) (apB : gpB ⊣ rpB) (arB : grB ⊣ rrB)
    {jkA : VA ⥤ WA} {jjA : SA ⥤ ZA} {jkB : VB ⥤ WB} {jjB : SB ⥤ ZB}
    {tv : VA ⥤ VB} {tw : WA ⥤ WB} {ts : SA ⥤ SB} {tz : ZA ⥤ ZB}
    (αA : jjA ⋙ gpA ⟶ grA ⋙ jkA) (αB : jjB ⋙ gpB ⟶ grB ⋙ jkB)
    (hp : tz ⋙ gpB ⟶ gpA ⋙ tw) (hr : ts ⋙ grB ⟶ grA ⋙ tv)
    (mp : rpA ⋙ tz ⟶ tw ⋙ rpB) (mr : rrA ⋙ ts ⟶ tv ⋙ rrB)
    (bk : jkA ⋙ tw ⟶ tv ⋙ jkB) (bj : jjA ⋙ tz ⟶ ts ⋙ jjB)
    (hmp : ∀ N, gpB.map (mp.app N) ≫ apB.counit.app (tw.obj N) =
      hp.app (rpA.obj N) ≫ tw.map (apA.counit.app N))
    (hmr : ∀ N, grB.map (mr.app N) ≫ arB.counit.app (tv.obj N) =
      hr.app (rrA.obj N) ≫ tv.map (arA.counit.app N))
    (hcube : ∀ L, hp.app (jjA.obj L) ≫ tw.map (αA.app L) ≫ bk.app (grA.obj L) =
      gpB.map (bj.app L) ≫ αB.app (ts.obj L) ≫ jkB.map (hr.app L)) (N : VA) :
    tz.map ((mateEquiv arA apA (TwoSquare.mk _ _ _ _ αA)).app N) ≫
        mp.app (jkA.obj N) ≫ rpB.map (bk.app N) =
      bj.app (rrA.obj N) ≫ jjB.map (mr.app N) ≫
        (mateEquiv arB apB (TwoSquare.mk _ _ _ _ αB)).app (tv.obj N) := by
  let γA := (mateEquiv arA apA (TwoSquare.mk _ _ _ _ αA)).natTrans
  let γB := (mateEquiv arB apB (TwoSquare.mk _ _ _ _ αB)).natTrans
  have hga := mateEquiv_counit arA apA (TwoSquare.mk _ _ _ _ αA) N
  have hgb := mateEquiv_counit arB apB (TwoSquare.mk _ _ _ _ αB) (tv.obj N)
  change gpA.map (γA.app N) ≫ apA.counit.app _ =
    αA.app (rrA.obj N) ≫ jkA.map (arA.counit.app N) at hga
  change gpB.map (γB.app (tv.obj N)) ≫ apB.counit.app _ =
    αB.app (rrB.obj (tv.obj N)) ≫ jkB.map (arB.counit.app (tv.obj N)) at hgb
  apply (apB.homEquiv _ _).symm.injective
  change gpB.map (tz.map (γA.app N) ≫ mp.app _ ≫ rpB.map (bk.app N)) ≫
    apB.counit.app _ =
      gpB.map (bj.app _ ≫ jjB.map (mr.app N) ≫ γB.app _) ≫ apB.counit.app _
  have hn := hp.naturality (γA.app N)
  have hb := bk.naturality (arA.counit.app N)
  have hn' := αB.naturality (mr.app N)
  have hc := apB.counit.naturality (bk.app N)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj]
    at hn hb hn' hc ⊢
  simp only [Functor.map_comp, Category.assoc]
  rw [hc, ← Category.assoc (gpB.map (mp.app _)), hmp]
  simp only [Category.assoc]
  rw [reassoc_of% hn, ← tw.map_comp_assoc, hga]
  simp only [Functor.map_comp, Category.assoc]
  rw [hb]
  rw [reassoc_of% hcube]
  rw [← jkB.map_comp, ← hmr]
  simp only [Functor.map_comp]
  rw [← reassoc_of% hn', ← hgb]

private theorem composite_scalar_transpose
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ B} {R₁ : B ⥤ C} {L₂ : B ⥤ A} {R₂ : A ⥤ B}
    {L₁' : F ⥤ E} {R₁' : E ⥤ F} {L₂' : E ⥤ D} {R₂' : D ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (b₁ : L₁' ⊣ R₁') (b₂ : L₂' ⊣ R₂')
    (TA : A ⥤ D) (TB : B ⥤ E) (TC : C ⥤ F)
    (h₁ : TC ⋙ L₁' ⟶ L₁ ⋙ TB) (h₂ : TB ⋙ L₂' ⟶ L₂ ⋙ TA)
    (m₁ : R₁ ⋙ TC ⟶ TB ⋙ R₁') (m₂ : R₂ ⋙ TB ⟶ TA ⋙ R₂')
    (hm₁ : ∀ M, L₁'.map (m₁.app M) ≫ b₁.counit.app (TB.obj M) =
      h₁.app (R₁.obj M) ≫ TB.map (a₁.counit.app M))
    (hm₂ : ∀ M, L₂'.map (m₂.app M) ≫ b₂.counit.app (TA.obj M) =
      h₂.app (R₂.obj M) ≫ TA.map (a₂.counit.app M)) (M : A) :
    (L₁' ⋙ L₂').map (m₁.app (R₂.obj M) ≫ R₁'.map (m₂.app M)) ≫
        (b₁.comp b₂).counit.app (TA.obj M) =
      (L₂'.map (h₁.app (R₁.obj (R₂.obj M))) ≫
        h₂.app (L₁.obj (R₁.obj (R₂.obj M)))) ≫
          TA.map ((a₁.comp a₂).counit.app M) := by
  have hn₁ := b₁.counit.naturality (m₂.app M)
  have hn₂ := h₂.naturality (a₁.counit.app (R₂.obj M))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at hn₁ hn₂
  simp only [Functor.comp_map, Functor.map_comp, Adjunction.comp_counit_app, Category.assoc]
  slice_lhs 2 3 => rw [← L₂'.map_comp, hn₁, L₂'.map_comp]
  slice_lhs 1 2 => rw [← L₂'.map_comp, hm₁, L₂'.map_comp]
  simp only [Category.assoc]
  rw [hm₂, reassoc_of% hn₂]

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- The proper scalar mate respects the normalized direct-image compositor.
Source: Stacks Tags 07A6, 0B56, 0D6D; strict scalar refinement, Steps 6 and 9.
(blueprint: lem-pur-strict-scalar-proper-composition).
Proof: take proper-adjunction mates of strictScalarPullComposition. The mate of
the pullback compositor gComp is the specified direct-image compositor rComp.
The geometric counit transpose of each scalar mate is given by
strictProper_geometric_transpose. Mate pasting identifies the transpose of the
successive proper scalar maps with the pullback-composition equation, retaining
the ordered composite counit. Injectivity of the adjunction Hom equivalence gives
the displayed equality in the derived category of strict towers. -/
theorem strictScalarProperComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X) :
    (T l E F i Z).map
        ((rComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) f g).hom.app M) ≫
        (proper l E F i (f ≫ g)).app M =
      (proper l E F i g).app
          ((R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) f).obj M) ≫
        (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g).map
          ((proper l E F i f).app M) ≫
        (rComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) f g).hom.app
          ((T l E F i X).obj M)  := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let B := ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)
  let mf := proper l E F i f
  let mg := proper l E F i g
  let hf := (strictScalarPull l E F i f).inv
  let hg := (strictScalarPull l E F i g).inv
  let mfg : (R A f ⋙ R A g) ⋙ T l E F i Z ⟶
      T l E F i X ⋙ (R B f ⋙ R B g) :=
    Functor.whiskerLeft (R A f) mg ≫ Functor.whiskerRight mf (R B g)
  let hfg : T l E F i Z ⋙ (G B g ⋙ G B f) ⟶
      (G A g ⋙ G A f) ⋙ T l E F i X :=
    Functor.whiskerRight hg (G B f) ≫ Functor.whiskerLeft (G A g) hf
  have hmfg (Q : Derived A X) :
      (G B g ⋙ G B f).map (mfg.app Q) ≫
          ((adj B g).comp (adj B f)).counit.app ((T l E F i X).obj Q) =
        hfg.app ((R A f ⋙ R A g).obj Q) ≫
          (T l E F i X).map (((adj A g).comp (adj A f)).counit.app Q) := by
    exact composite_scalar_transpose (adj A g) (adj A f) (adj B g) (adj B f)
      (T l E F i X) (T l E F i Y) (T l E F i Z) hg hf mg mf
      (strictProper_geometric_transpose l E F i g)
      (strictProper_geometric_transpose l E F i f) Q
  have h := scalar_cube_mates
    (adj A (f ≫ g)) ((adj A g).comp (adj A f))
    (adj B (f ≫ g)) ((adj B g).comp (adj B f))
    (jkA := 𝟭 _) (jjA := 𝟭 _) (jkB := 𝟭 _) (jjB := 𝟭 _)
    (gComp A f g).hom (gComp B f g).hom
    (strictScalarPull l E F i (f ≫ g)).inv hfg
    (proper l E F i (f ≫ g)) mfg (𝟙 _) (𝟙 _)
    (strictProper_geometric_transpose l E F i (f ≫ g)) hmfg
    (fun Q ↦ by
      dsimp only [hfg, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, NatTrans.id_app, Functor.id_obj, Functor.comp_obj]
      erw [(G B (f ≫ g)).map_id, Category.id_comp, Category.comp_id]
      exact (strictScalarPullComposition l E F i f g Q).symm) M
  simp only [rComp, conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app,
    mateEquiv_apply,
    TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map,
    NatTrans.id_app, Category.comp_id, Category.id_comp, Category.assoc,
    mfg, mf, mg] at h ⊢
  erw [(R B (f ≫ g)).map_id, Category.comp_id] at h
  exact h

end WeilConjectures.PurStrictScalar
