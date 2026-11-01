/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralComparisons
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPullComposition
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteDiscreteRingObj.FiniteDiscreteCoefficientBaseChange

/-! # Coherence of integral localization and the specified exchange map: pull comparisons

The calculus lemmas and the pull-comparison squares used by
`Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct` (split from it for compile time). -/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

open CategoryTheory

universe u₇ u₈ v₇ v₈
section ScalarMapAPI
variable {C : Type u₇} {D : Type u₈} [Category.{v₇} C] [Category.{v₈} D]
end ScalarMapAPI

section MateCalculus

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {E₁ : A ⥤ B} {Res₁ : B ⥤ A} (adj₁ : E₁ ⊣ Res₁)
  {E₂ : A' ⥤ B'} {Res₂ : B' ⥤ A'} (adj₂ : E₂ ⊣ Res₂)
  {U₁ : A' ⥤ A} {L₁ : A ⥤ A'} (adjR : U₁ ⊣ L₁)
  {U₂ : B' ⥤ B} {L₂ : B ⥤ B'} (adjS : U₂ ⊣ L₂)
  (e : L₂ ⋙ Res₂ ≅ Res₁ ⋙ L₁)
set_option backward.defeqAttrib.useBackward true
section Diagrams
universe v₅ u₅
variable {C : Type u₅} [Category.{v₅} C]
universe u₆ v₆

private def scalarMap (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : F.obj X ⟶ F.obj Y := F.map f

private lemma scalarMap_comp (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    scalarMap F (f ≫ g) = scalarMap F f ≫ scalarMap F g := F.map_comp f g

private lemma map_eq_whisker (F : C ⥤ D) {X Y Z : C} {A B : D}
    (a : A ⟶ F.obj X) (b : F.obj Z ⟶ B)
    (u : X ⟶ Z) (v : X ⟶ Y) (w : Y ⟶ Z) (h : u = v ≫ w) :
    a ≫ scalarMap F u ≫ b = a ≫ scalarMap F v ≫ scalarMap F w ≫ b := by
  rw [h, scalarMap_comp]
  simp only [Category.assoc]

private lemma push_pull_counit (K : A) :
    U₂.map ((Adjunction.pushHomOfComapIso adj₁ adj₂ e).app K) ≫
        adjS.counit.app (E₁.obj K) =
      (Adjunction.pullIsoOfComapIso adj₁ adj₂ adjR adjS e).inv.app (L₁.obj K) ≫
        E₁.map (adjR.counit.app K) := by
  have h := iterated_mateEquiv_conjugateEquiv_symm adjR adjS adj₂ adj₁
    (TwoSquare.mk Res₁ L₂ L₁ Res₂ e.inv)
  have hh := mateEquiv_counit_symm adjR adjS
    (TwoSquare.mk L₁ E₁ E₂ L₂ (Adjunction.pushHomOfComapIso adj₁ adj₂ e)) K
  change U₂.map ((Adjunction.pushHomOfComapIso adj₁ adj₂ e).app K) ≫
      adjS.counit.app (E₁.obj K) =
    ((mateEquiv adjR adjS).symm
      ((mateEquiv adj₁ adj₂).symm (TwoSquare.mk Res₁ L₂ L₁ Res₂ e.inv))).app
        (L₁.obj K) ≫ E₁.map (adjR.counit.app K) at hh
  rw [h] at hh
  exact hh

private lemma adjunct_target_start {M : A'} {N : A} {P : B}
    (u : M ⟶ L₁.obj N) (v : E₂.obj (L₁.obj N) ⟶ L₂.obj (E₁.obj N))
    (w : E₁.obj N ⟶ P)
    (v' : E₂.obj (L₁.obj N) ⟶ L₂.obj P)
    (hv' : v' = v ≫ L₂.map w)
    (αM : E₁.obj (U₁.obj M) ≅ U₂.obj (E₂.obj M))
    (αN : E₁.obj (U₁.obj (L₁.obj N)) ≅ U₂.obj (E₂.obj (L₁.obj N)))
    (hv : U₂.map v ≫ adjS.counit.app (E₁.obj N) =
      αN.inv ≫ E₁.map (adjR.counit.app N))
    (hu : U₂.map (E₂.map u) ≫ αN.inv = αM.inv ≫ E₁.map (U₁.map u)) :
    (adjS.homEquiv _ _).symm (E₂.map u ≫ v') =
      αM.inv ≫ E₁.map ((adjR.homEquiv _ _).symm u) ≫ w := by
  rw [hv']
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_counit, hv]
  simp only [← Category.assoc]
  rw [hu]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp,
    Adjunction.homEquiv_counit]

private lemma rectangle
    {A₀ A₁ A₂ A₃ B₀ B₁ C₀ C₁ D₀ D₁ : C}
    (p : A₀ ≅ A₁) (q : A₃ ≅ A₂) (r : A₀ ≅ A₃)
    (pE : C₁ ≅ C₀) (qE : D₁ ≅ D₀) (rE : C₁ ≅ D₁)
    (a : A₁ ⟶ B₀) (b : B₀ ⟶ C₀) (c : A₂ ⟶ B₁) (d : B₁ ⟶ D₀)
    (e : A₀ ⟶ C₁) (f : A₃ ⟶ D₁)
    (h₁ : q.hom ≫ c ≫ d = f ≫ qE.hom)
    (h₂ : p.hom ≫ a ≫ b = e ≫ pE.hom)
    (he : r.hom ≫ f = e ≫ rE.hom) :
    p.inv ≫ r.hom ≫ q.hom ≫ c ≫ d = a ≫ b ≫ pE.inv ≫ rE.hom ≫ qE.hom := by
  apply (cancel_epi p.hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [h₁, reassoc_of% he, reassoc_of% h₂]
  simp

private lemma mapped_rectangle {D : Type u₆} [Category.{v₆} D]
    (F : C ⥤ D) {A₀ A₁ A₂ A₃ : C} {B₀ B₁ C₀ C₁ D₀ D₁ : D}
    (p : A₀ ≅ A₁) (q : A₃ ≅ A₂) (r : A₀ ≅ A₃)
    (pE : C₁ ≅ C₀) (qE : D₁ ≅ D₀) (rE : C₁ ≅ D₁)
    (a : F.obj A₁ ⟶ B₀) (b : B₀ ⟶ C₀)
    (c : F.obj A₂ ⟶ B₁) (d : B₁ ⟶ D₀)
    (e : F.obj A₀ ⟶ C₁) (f : F.obj A₃ ⟶ D₁)
    (h₁ : F.map q.hom ≫ c ≫ d = f ≫ qE.hom)
    (h₂ : F.map p.hom ≫ a ≫ b = e ≫ pE.hom)
    (he : F.map r.hom ≫ f = e ≫ rE.hom) :
    F.map (p.inv ≫ r.hom ≫ q.hom) ≫ c ≫ d =
      a ≫ b ≫ pE.inv ≫ rE.hom ≫ qE.hom := by
  simpa only [CategoryTheory.Functor.map_comp, Functor.mapIso_hom,
    Functor.mapIso_inv, Category.assoc] using
    rectangle (F.mapIso p) (F.mapIso q) (F.mapIso r) pE qE rE a b c d e f h₁ h₂ he

private lemma mapped_iso_rectangle {D : Type u₆} [Category.{v₆} D]
    (F : C ⥤ D) {A₀ A₁ A₂ A₃ : C} {B₀ B₁ C₀ C₁ D₀ D₁ : D}
    (p : A₀ ≅ A₁) (q : A₃ ≅ A₂) (r : A₀ ≅ A₃)
    (pE : C₁ ≅ C₀) (qE : D₁ ≅ D₀) (rE : C₁ ≅ D₁)
    (a : F.obj A₁ ≅ B₀) (b : B₀ ≅ C₀)
    (c : F.obj A₂ ≅ B₁) (d : B₁ ≅ D₀)
    (e : F.obj A₀ ≅ C₁) (f : F.obj A₃ ≅ D₁)
    (h₁ : F.mapIso q ≪≫ c ≪≫ d = f ≪≫ qE)
    (h₂ : F.mapIso p ≪≫ a ≪≫ b = e ≪≫ pE)
    (he : F.mapIso r ≪≫ f = e ≪≫ rE) :
    F.mapIso (p.symm ≪≫ r ≪≫ q) ≪≫ c ≪≫ d =
      a ≪≫ b ≪≫ pE.symm ≪≫ rE ≪≫ qE := by
  apply Iso.ext
  exact mapped_rectangle F p q r pE qE rE a.hom b.hom c.hom d.hom e.hom f.hom
    (congrArg Iso.hom h₁) (congrArg Iso.hom h₂) (congrArg Iso.hom he)

private lemma inverse_square {P Q R S : C}
    (a : P ≅ Q) (b : R ≅ S) (x : P ⟶ R) (u : Q ⟶ S)
    (h : x ≫ b.hom = a.hom ≫ u) : a.inv ≫ x = u ≫ b.inv := by
  apply (cancel_mono b.hom).1
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc] using congrArg (fun v ↦ a.inv ≫ v) h

private lemma inverse_mapped_square {D : Type u₆} [Category.{v₆} D]
    (F : D ⥤ C) {P Q R : C} {S T : D}
    (a : P ≅ Q) (b : S ≅ T) (x : P ⟶ R) (y : R ⟶ F.obj S)
    (u : Q ⟶ F.obj T)
    (h : x ≫ y ≫ F.map b.hom = a.hom ≫ u) :
    a.inv ≫ x ≫ y = u ≫ F.map b.inv := by
  simpa only [Category.assoc, Functor.mapIso_inv] using
    inverse_square a (F.mapIso b) (x ≫ y) u
      (by simpa only [Category.assoc, Functor.mapIso_hom] using h)

private lemma upperStar_map_hom {T U : Scheme.{u}} [T.Over (Spec (.of k))]
    [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    {A B : ProEtale.BoundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) U)} (φ : A ⟶ B) :
    ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
      (h.asOver (Spec (.of k)))).map φ).hom = (L((h)^*⟦normedRing E⟧)).map φ.hom :=
  rfl

private lemma bounded_counit_hom_continuousMap
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    (K : ProEtale.BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) T)) :
    ((ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
      (h.asOver (Spec (.of k)))).counit.app K).hom =
      (derivedUpperStarLowerStarAdjunction (normedRing E) h).counit.app K.obj :=
  (congrArg (fun a ↦ (a.counit.app K).hom)
    (continuousMap_adjunction_eq ℓ E k (h.asOver (Spec (.of k))))).trans
    (restricted_counit_hom ℓ k _ (h.asOver (Spec (.of k))) _ K)

/-- The `E̲`-coefficient adjunction `Lf^* ⊣ Rf_*` is the restricted derived adjunction. -/
private lemma continuousMap_adjunction_eq {T U : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] (h : T ⟶ U) :
    ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E h =
      Adjunction.restrictFullyFaithful
        (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E) h.left)
        (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
        (boundedConstructibleUpperStarCompatibility (Profinite.continuousMapRingObj E) ℓ h).symm
        (ObjectProperty.liftCompιIso _ _
          (ContinuousMapRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E h)).symm :=
  rfl

/-- `E̲` with the topology and ring structure of the normed field `F`, the coefficient ring of
`integralScalarConstructible`. -/
private noncomputable abbrev normedRing (F : Type) [NormedField F] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  Profinite.continuousMapRingObj.{u} F

private lemma integralPull_square
    (sq : CommSq g' f' f g) (M : integralConstructible ℓ E Y) :
    (integralConstructiblePullIso ℓ E k f'
        ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g.asOver (Spec (.of k)))).obj M)).inv
          ≫
      scalarMap (integralScalarConstructible ℓ E X')
        (((boundedConstructiblePullbackSquareComparison (integralCoeff ℓ E) ℓ (sq.asOver (Spec (.of
          k)))).app M).hom) ≫
      integralConstructiblePullHom ℓ E k g'
        ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (f.asOver (Spec (.of k)))).obj M) =
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (f'.asOver (Spec (.of
      k)))).map
        (integralConstructiblePullHom ℓ E k g M) ≫
      ((boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ (sq.asOver
        (Spec (.of k)))).app
          ((integralScalarConstructible ℓ E Y).obj M)).hom ≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of
        k)))).map
        (integralConstructiblePullIso ℓ E k f M).inv := by
  simpa only [Category.assoc] using inverse_mapped_square
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of k))))
    (integralConstructiblePullIso ℓ E k f'
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g.asOver (Spec (.of k)))).obj M))
    (integralConstructiblePullIso ℓ E k f M) _ _ _
    (integralPull_square_cube ℓ E k f g f' g' sq M)

private lemma integralPull_square_cube
    (sq : CommSq g' f' f g) (M : integralConstructible ℓ E Y) :
    scalarMap (integralScalarConstructible ℓ E X')
        (((boundedConstructiblePullbackSquareComparison (integralCoeff ℓ E) ℓ (sq.asOver (Spec (.of
          k)))).app M).hom) ≫
      integralConstructiblePullHom ℓ E k g'
        ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (f.asOver (Spec (.of k)))).obj M) ≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of
        k)))).map
        (integralConstructiblePullHom ℓ E k f M) =
    integralConstructiblePullHom ℓ E k f'
        ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g.asOver (Spec (.of k)))).obj M) ≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (f'.asOver (Spec (.of
        k)))).map
        (integralConstructiblePullHom ℓ E k g M) ≫
      ((boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ (sq.asOver
        (Spec (.of k)))).app
          ((integralScalarConstructible ℓ E Y).obj M)).hom := by
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    integralConstructiblePullHom, scalarMap] using
    congrArg Iso.hom (integralPull_square_cube_iso ℓ E k f g f' g' sq M)

private lemma integralPull_square_cube_iso
    (sq : CommSq g' f' f g) (M : integralConstructible ℓ E Y) :
    (integralScalarConstructible ℓ E X').mapIso
        ((boundedConstructiblePullbackSquareComparison (integralCoeff ℓ E) ℓ (sq.asOver (Spec (.of
          k)))).app M) ≪≫
      integralConstructiblePullIso ℓ E k g'
        ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (f.asOver (Spec (.of k)))).obj M) ≪≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of
        k)))).mapIso
        (integralConstructiblePullIso ℓ E k f M) =
    integralConstructiblePullIso ℓ E k f'
        ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g.asOver (Spec (.of k)))).obj M) ≪≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (f'.asOver (Spec (.of
        k)))).mapIso
        (integralConstructiblePullIso ℓ E k g M) ≪≫
      (boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ (sq.asOver
        (Spec (.of k)))).app
          ((integralScalarConstructible ℓ E Y).obj M) := by
  have h₁ := integralConstructiblePullIso_comp ℓ E k g' f M
  have h₂ := integralConstructiblePullIso_comp ℓ E k f' g M
  have he := integralPull_eq ℓ E k (f' ≫ g) (g' ≫ f) sq.w.symm M
  simp only [boundedConstructiblePullbackSquareComparison_app]
  exact mapped_iso_rectangle (integralScalarConstructible ℓ E X')
      ((boundedConstructibleUpperStarComp (integralCoeff ℓ E) ℓ (f'.asOver (Spec (.of k))) (g.asOver
        (Spec (.of k)))).app M)
      ((boundedConstructibleUpperStarComp (integralCoeff ℓ E) ℓ (g'.asOver (Spec (.of k))) (f.asOver
        (Spec (.of k)))).app M)
      ((eqToIso (by simp only [sq.w]) :
        boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ ((f' ≫ g).asOver (Spec (.of k))) ≅
        boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ ((g' ≫ f).asOver (Spec (.of k)))).app M)
      ((boundedConstructibleUpperStarComp (Profinite.continuousMapRingObj E) ℓ (f'.asOver (Spec (.of
        k))) (g.asOver (Spec (.of k)))).app ((integralScalarConstructible ℓ E Y).obj M))
      ((boundedConstructibleUpperStarComp (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of
        k))) (f.asOver (Spec (.of k)))).app ((integralScalarConstructible ℓ E Y).obj M))
      ((eqToIso (by simp only [sq.w]) :
        boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ ((f' ≫ g).asOver (Spec
          (.of k))) ≅
        boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ ((g' ≫ f).asOver (Spec
          (.of k)))).app
        ((integralScalarConstructible ℓ E Y).obj M))
      _ _ _ _ _ _ h₁ h₂ he

private lemma integralPull_eq
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    (j : T ⟶ U) [j.IsOver (Spec (.of k))] (w : h = j)
    (K : integralConstructible ℓ E U) :
    (integralScalarConstructible ℓ E T).mapIso
        ((eqToIso (by subst j; rfl) :
          boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (h.asOver (Spec (.of k))) ≅
            boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (j.asOver (Spec (.of k)))).app K) ≪≫
      integralConstructiblePullIso ℓ E k j K =
    integralConstructiblePullIso ℓ E k h K ≪≫
      (eqToIso (by subst j; rfl) :
        boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (h.asOver (Spec (.of k)))
          ≅
          boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (j.asOver (Spec (.of
            k)))).app
          ((integralScalarConstructible ℓ E U).obj K) := by
  subst j
  change (integralScalarConstructible ℓ E T).mapIso (Iso.refl _) ≪≫ _ =
    _ ≪≫ Iso.refl _
  simp only [Functor.mapIso_refl, Iso.refl_trans, Iso.trans_refl]

private lemma integralPull_inv_naturality
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    {K L : integralConstructible ℓ E U} (v : K ⟶ L) :
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (h.asOver (Spec (.of
      k)))).map
        (scalarMap (integralScalarConstructible ℓ E U) v) ≫
      (integralConstructiblePullIso ℓ E k h L).inv =
    (integralConstructiblePullIso ℓ E k h K).inv ≫
      scalarMap (integralScalarConstructible ℓ E T)
        ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (h.asOver (Spec (.of k)))).map v) :=
          by
  apply ObjectProperty.hom_ext
  exact (derivedPullIso (integralScalarMap ℓ E) h).inv.naturality v.hom

private lemma integralPull_naturality
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    {K L : integralConstructible ℓ E U} (v : K ⟶ L) :
    scalarMap (integralScalarConstructible ℓ E T)
        ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (h.asOver (Spec (.of k)))).map v) ≫
      integralConstructiblePullHom ℓ E k h L =
    integralConstructiblePullHom ℓ E k h K ≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (h.asOver (Spec (.of
        k)))).map
        (scalarMap (integralScalarConstructible ℓ E U) v) := by
  apply ObjectProperty.hom_ext
  exact (derivedPullIso (integralScalarMap ℓ E) h).hom.naturality v.hom

private lemma bounded_counit_hom_unitBall
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    (K : ProEtale.BoundedConstructible (condensedRingObj (integralCoeff ℓ E) T)) :
    ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E)
      (h.asOver (Spec (.of k)))).counit.app K).hom =
      (derivedUpperStarLowerStarAdjunction (integralCoeff ℓ E) h).counit.app K.obj :=
  (congrArg (fun a ↦ (a.counit.app K).hom)
    (unitBall_adjunction_eq ℓ E k (h.asOver (Spec (.of k))))).trans
    (restricted_counit_hom ℓ k _ (h.asOver (Spec (.of k))) _ K)

/-- The `O̲`-coefficient adjunction `Lf^* ⊣ Rf_*` is the restricted derived adjunction. -/
private lemma unitBall_adjunction_eq {T U : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] (h : T ⟶ U) :
    UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E)
        h =
      Adjunction.restrictFullyFaithful
        (derivedUpperStarLowerStarAdjunction (integralCoeff ℓ E) h.left)
        (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
        (boundedConstructibleUpperStarCompatibility (integralCoeff ℓ E) ℓ h).symm
        (ObjectProperty.liftCompιIso _ _
          (UnitBallRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ
            (continuousIntegers ℓ E) h)).symm :=
  rfl

/-- The counit of the restriction of `Lf^* ⊣ Rf_*` to bounded constructible complexes, along a
proof `hf` that `Rf_*` preserves them, is the derived counit. -/
private lemma restricted_counit_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {T U : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] (h : T ⟶ U)
    (hf : ∀ K : Dᵇc(T.left)⟦Λ⟧,
      boundedConstructible (condensedRingObj Λ U.left) ((R((h.left)_*⟦Λ⟧)).obj K.obj))
    (K : Dᵇc(T.left)⟦Λ⟧) :
    ((Adjunction.restrictFullyFaithful (derivedUpperStarLowerStarAdjunction Λ h.left)
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      (boundedConstructibleUpperStarCompatibility Λ ℓ h).symm
      (ObjectProperty.liftCompιIso _ _ hf).symm).counit.app K).hom =
      (derivedUpperStarLowerStarAdjunction Λ h.left).counit.app K.obj := by
  refine (Adjunction.map_restrictFullyFaithful_counit_app
    (derivedUpperStarLowerStarAdjunction Λ h.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility Λ ℓ h).symm
    (ObjectProperty.liftCompιIso _ _ hf).symm K).trans ?_
  simp [boundedConstructibleUpperStarCompatibility, ObjectProperty.liftCompιIso]
  exact Category.id_comp _

end Diagrams

end MateCalculus

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section General

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

attribute [local irreducible] derivedUpperStarLowerStarAdjunction
  Mod.derivedExtendMapDerivedCategoryAdjunction derivedComapLowerStarIso
  Adjunction.pushHomOfComapIso Adjunction.pullIsoOfComapIso Adjunction.restrictFullyFaithful

omit [FiniteDimensional ℚ_[ℓ] E] in
omit [FiniteDimensional ℚ_[ℓ] E] in
omit [FiniteDimensional ℚ_[ℓ] E] in
section PullSquareCalculation
attribute [local irreducible] integralScalarConstructible
  integralConstructiblePullIso
  boundedConstructibleUpperStar UnitBallRingObj.boundedConstructibleLowerStar
  ContinuousMapRingObj.boundedConstructibleLowerStar

omit [FiniteDimensional ℚ_[ℓ] E] in
omit [FiniteDimensional ℚ_[ℓ] E] in
omit [FiniteDimensional ℚ_[ℓ] E] in
end PullSquareCalculation

end General

section FiniteIntermediateField

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

end FiniteIntermediateField

end AlgebraicGeometry.ProEtale.CondensedRing
