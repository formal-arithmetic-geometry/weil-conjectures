# CartesianChartExchangeAdjunction duplicate retirement

## Reason

This is the listed retirement item in coord/retire-items.tsv, under the human's
coord/changes/retire-sheaf-twins-20261020.md instruction. The copy contains zero
holes. Its complete Lean token sequence, ignoring comments and whitespace, equals
that of WeilConjectures.AlgebraicGeometry.CartesianChartExchangeAdjunction.
That includes all three definitions and eight proved lemmas/theorems. The only
textual differences are the upstream copyright and three explanatory comments.

## Old

The duplicate module was:

```lean
module
public import WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeCoefficients
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeCore
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeSource
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc
-- These comparison helpers are consumed through private proof imports.
set_option linter.privateModule false

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency true
set_option linter.unusedSimpArgs false
set_option linter.privateModule false

private noncomputable def actualAdjunct
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {B T Z X : Scheme.{u}}
    (p : Z ⟶ T) (a : T ⟶ B) (s : Z ⟶ B) (hs : s = p ≫ a)
    (q : Z ⟶ X) (M : Sheaf B.smallEtaleTopology A)
    (F : Sheaf X.smallEtaleTopology A)
    (n : ℕ)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((s)^*[A]).obj M) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (((q)^*[A]).obj F))⟦(n : ℤ)⟧) :
    D+((p)^*[A]).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (((a)^*[A]).obj M)) ⟶
      (D+((q)^*[A]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))⟦(n : ℤ)⟧ :=
  (((p)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app (((a)^*[A]).obj M) ≫
    (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp A p a s hs).inv.app
        M) ≫ z ≫
    (shiftFunctor _ (n : ℤ)).map
      ((((q)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app F)


private lemma comp_single_inv_map
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {X Z Z' : Scheme.{u}}
    (t : Z' ⟶ Z) (q : Z ⟶ X) (q' : Z' ⟶ X) (hq : q' = t ≫ q)
    (F : Sheaf X.smallEtaleTopology A) {C : Type*} [Category C]
    (H : DerivedCategory.Plus (Sheaf Z'.smallEtaleTopology A) ⥤ C) :
    H.map ((((t)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
        (((q)^*[A]).obj F)) ≫
      H.map ((DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp A t q q' hq).inv.app F)) ≫
      H.map ((((q')^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app F) =
    H.map (D+((t)^*[A]).map
      ((((q)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app F)) ≫
      H.map ((upperStarCompDerivedPlus A t q q' hq).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg H.map (comp_single_inv A t q q' hq F)

private noncomputable def rawClassPullback
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {B Z Z' : Scheme.{u}}
    (t : Z' ⟶ Z) (h : Z ⟶ B) (h' : Z' ⟶ B) (w : t ≫ h = h')
    (M : Sheaf B.smallEtaleTopology A) (n : ℕ)
    (G : Sheaf Z.smallEtaleTopology A) (G' : Sheaf Z'.smallEtaleTopology A)
    (φ : ((t)^*[A]).obj G ⟶ G')
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj (((h)^*[A]).obj M) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G)⟦(n : ℤ)⟧) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj (((h')^*[A]).obj M) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G')⟦(n : ℤ)⟧ :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp A t h h' w.symm).hom.app M) ≫
    (((t)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app (((h)^*[A]).obj M) ≫
    D+((t)^*[A]).map z ≫
    (D+((t)^*[A]).commShiftIso (n : ℤ)).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G) ≫
    (shiftFunctor _ (n : ℤ)).map
      ((((t)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map φ)

private lemma rawClassPullback_eq_raw {B Z Z' : Scheme.{u}}
    (t : Z' ⟶ Z) (h : Z ⟶ B) (h' : Z' ⟶ B) (w : t ≫ h = h')
    (n : ℕ) (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G' : Sheaf Z'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ((t)^*[AddCommGrpCat.{u + 1}]).obj G ⟶ G') (V : B.Etale)
    (z : (abelianHigherDirectImageRawPresheaf h n G).obj (op V)) :
    rawClassPullback AddCommGrpCat.{u + 1} t h h' w
      ((abelianComparisonFree B).obj V) n G G' φ z =
    abelianHigherDirectImageRawPullback t h h' w n G G' φ V z := by
  rfl

private noncomputable def actualTransport
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {B T T' Z Z' X : Scheme.{u}}
    {t : Z' ⟶ Z} {p : Z ⟶ T} {p' : Z' ⟶ T'} {b : T' ⟶ T}
    (θ : D+((b)^*[A]) ⋙ D+((p')^*[A]) ⟶ D+((p)^*[A]) ⋙ D+((t)^*[A]))
    (a : T ⟶ B) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (q : Z ⟶ X) (q' : Z' ⟶ X) (hq : q' = t ≫ q)
    (M : Sheaf B.smallEtaleTopology A) (F : Sheaf X.smallEtaleTopology A) (n : ℕ)
    (z : D+((p)^*[A]).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (((a)^*[A]).obj M)) ⟶
      (D+((q)^*[A]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))⟦(n : ℤ)⟧) :=
    D+((p')^*[A]).map
        ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((upperStarComp A b a a' ha).hom.app
              M) ≫
          (((b)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app
            (((a)^*[A]).obj M)) ≫
      θ.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (((a)^*[A]).obj M)) ≫
      D+((t)^*[A]).map z ≫
      (D+((t)^*[A]).commShiftIso (n : ℤ)).hom.app
        (D+((q)^*[A]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
      (shiftFunctor _ (n : ℤ)).map
        ((upperStarCompDerivedPlus A t q q' hq).inv.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))

set_option maxHeartbeats 10000 in
-- Keep elaboration of the expanded transport composite within a small local budget.
private lemma actualTransport_eq
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {B T T' Z Z' X : Scheme.{u}}
    {t : Z' ⟶ Z} {p : Z ⟶ T} {p' : Z' ⟶ T'} {b : T' ⟶ T}
    (θ : D+((b)^*[A]) ⋙ D+((p')^*[A]) ⟶ D+((p)^*[A]) ⋙ D+((t)^*[A]))
    (a : T ⟶ B) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (q : Z ⟶ X) (q' : Z' ⟶ X) (hq : q' = t ≫ q)
    (M : Sheaf B.smallEtaleTopology A) (F : Sheaf X.smallEtaleTopology A) (n : ℕ)
    (z : D+((p)^*[A]).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (((a)^*[A]).obj M)) ⟶
      (D+((q)^*[A]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))⟦(n : ℤ)⟧) :
    actualTransport A (t := t) (p := p) (p' := p') (b := b) θ a a' ha q q' hq M F n z =
    D+((p')^*[A]).map
        ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((upperStarComp A b a a' ha).hom.app
              M) ≫
          (((b)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app
            (((a)^*[A]).obj M)) ≫
      θ.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (((a)^*[A]).obj M)) ≫
      D+((t)^*[A]).map z ≫
      (D+((t)^*[A]).commShiftIso (n : ℤ)).hom.app
        (D+((q)^*[A]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
      (shiftFunctor _ (n : ℤ)).map
        ((upperStarCompDerivedPlus A t q q' hq).inv.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  rfl

private lemma actualAdjunct_pullback
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {B T T' Z Z' X : Scheme.{u}}
    (t : Z' ⟶ Z) (p : Z ⟶ T) (p' : Z' ⟶ T') (b : T' ⟶ T)
    (sq : CommSq t p' p b) (a : T ⟶ B) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (s : Z ⟶ B) (hs : s = p ≫ a) (s' : Z' ⟶ B) (hs' : s' = p' ≫ a')
    (q : Z ⟶ X) (q' : Z' ⟶ X) (hq : q' = t ≫ q)
    (M : Sheaf B.smallEtaleTopology A)
    (F : Sheaf X.smallEtaleTopology A) (n : ℕ)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((s)^*[A]).obj M) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (((q)^*[A]).obj F))⟦(n : ℤ)⟧) :
    actualAdjunct A p' a' s' hs' q'
      M F n
      (rawClassPullback A t s s'
        (by rw [hs', ha, ← Category.assoc p' b a, ← sq.w, Category.assoc, ← hs]) M n _ _
        ((upperStarComp A t q q' hq).inv.app F) z) =
    D+((p')^*[A]).map
        ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((upperStarComp A b a a' ha).hom.app
              M) ≫
          (((b)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app
            (((a)^*[A]).obj M)) ≫
      (pullbackSquareComparison A sq).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (((a)^*[A]).obj M)) ≫
      D+((t)^*[A]).map (actualAdjunct A p a s hs q
          M F n z) ≫
      (D+((t)^*[A]).commShiftIso (n : ℤ)).hom.app
        (D+((q)^*[A]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
      (shiftFunctor _ (n : ℤ)).map
        ((upperStarCompDerivedPlus A t q q' hq).inv.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  dsimp only [actualAdjunct, rawClassPullback]
  simp only [Functor.comp_obj, Functor.map_comp, Category.assoc]
  rw [comp_single_inv_map A t q q' hq F
    (shiftFunctor _ (n : ℤ))]
  rw [← reassoc_of% (Functor.commShiftIso_hom_naturality
    D+((t)^*[A])
    ((((q)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app F) (n : ℤ))]
  rw [← reassoc_of% (square_single_source A t p p' b sq a a' ha s hs s' hs' M)]
  simp only [Functor.map_comp, Category.assoc]



set_option maxHeartbeats 20000 in
-- Bound elaboration while reusing the expanded pullback identity.
private lemma actualAdjunct_pullback_block
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {B T T' Z Z' X : Scheme.{u}}
    (t : Z' ⟶ Z) (p : Z ⟶ T) (p' : Z' ⟶ T') (b : T' ⟶ T)
    (sq : CommSq t p' p b) (a : T ⟶ B) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (s : Z ⟶ B) (hs : s = p ≫ a) (s' : Z' ⟶ B) (hs' : s' = p' ≫ a')
    (q : Z ⟶ X) (q' : Z' ⟶ X) (hq : q' = t ≫ q)
    (M : Sheaf B.smallEtaleTopology A)
    (F : Sheaf X.smallEtaleTopology A) (n : ℕ)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((s)^*[A]).obj M) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (((q)^*[A]).obj F))⟦(n : ℤ)⟧) :
    actualAdjunct A p' a' s' hs' q'
      M F n
      (rawClassPullback A t s s'
        (by rw [hs', ha, ← Category.assoc p' b a, ← sq.w, Category.assoc, ← hs]) M n _ _
        ((upperStarComp A t q q' hq).inv.app F) z) =
    actualTransport A (t := t) (p := p) (p' := p') (b := b)
      (pullbackSquareComparison A sq).hom a a' ha q q' hq M F n
      (actualAdjunct A p a s hs q M F n z) := by
  rw [actualTransport_eq]
  exact actualAdjunct_pullback A t p p' b sq a a' ha s hs s' hs' q q' hq M F n z

private theorem adjunct_mate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : C ⥤ E) (H : D ⥤ F)
    (θ : TwoSquare G L L' H) {A : C} {K : D} (z : L.obj A ⟶ K) :
    G.map (adj.homEquiv A K z) ≫ (mateEquiv adj adj' θ).natTrans.app K =
      adj'.homEquiv (G.obj A) (H.obj K) (θ.natTrans.app A ≫ H.map z) := by
  rw [adj.homEquiv_unit, G.map_comp, Category.assoc]
  have hn := (mateEquiv adj adj' θ).natTrans.naturality z
  simp only [Functor.comp_map] at hn
  rw [hn]
  rw [← Category.assoc, unit_mateEquiv, Category.assoc, ← R'.map_comp,
    adj'.homEquiv_unit]
  rfl

private theorem shifted_adjunct_mate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] [HasShift F ℤ]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    [R.CommShift ℤ] [R'.CommShift ℤ]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : C ⥤ E) (H : D ⥤ F)
    [G.CommShift ℤ] [H.CommShift ℤ] (θ : TwoSquare G L L' H)
    [NatTrans.CommShift (mateEquiv adj adj' θ).natTrans ℤ]
    {A : C} {K : D} (q : ℤ) (z : L.obj A ⟶ K⟦q⟧) :
    G.map (adj.homEquiv A (K⟦q⟧) z ≫ (R.commShiftIso q).hom.app K) ≫
        (G.commShiftIso q).hom.app (R.obj K) ≫
        (shiftFunctor E q).map ((mateEquiv adj adj' θ).natTrans.app K) =
      adj'.homEquiv (G.obj A) ((H.obj K)⟦q⟧)
        (θ.natTrans.app A ≫ H.map z ≫ (H.commShiftIso q).hom.app K) ≫
          (R'.commShiftIso q).hom.app (H.obj K) := by
  have hs := NatTrans.shift_app_comm (mateEquiv adj adj' θ).natTrans q K
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hs
  rw [Functor.map_comp, Category.assoc, hs]
  rw [← Category.assoc, adjunct_mate]
  rw [← Category.assoc, ← adj'.homEquiv_naturality_right, Category.assoc]

private theorem shifted_adjunct_mate_transport
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] [HasShift F ℤ]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    [R.CommShift ℤ] [R'.CommShift ℤ]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : C ⥤ E) (H : D ⥤ F)
    [G.CommShift ℤ] [H.CommShift ℤ] (θ : TwoSquare G L L' H)
    [NatTrans.CommShift (mateEquiv adj adj' θ).natTrans ℤ]
    {A : C} {A' : E} {K : D} {K' : F} (q : ℤ)
    (δ : A' ⟶ G.obj A) (z : L.obj A ⟶ K⟦q⟧) (t : H.obj K ⟶ K') :
    δ ≫ G.map (adj.homEquiv A (K⟦q⟧) z ≫ (R.commShiftIso q).hom.app K) ≫
        (G.commShiftIso q).hom.app (R.obj K) ≫
        (shiftFunctor E q).map
          ((mateEquiv adj adj' θ).natTrans.app K ≫ R'.map t) =
      adj'.homEquiv A' (K'⟦q⟧)
        (L'.map δ ≫ θ.natTrans.app A ≫ H.map z ≫
          (H.commShiftIso q).hom.app K ≫ (shiftFunctor F q).map t) ≫
            (R'.commShiftIso q).hom.app K' := by
  have hm := shifted_adjunct_mate adj adj' G H θ q z
  rw [(shiftFunctor E q).map_comp]
  rw [reassoc_of% hm]
  rw [← R'.commShiftIso_hom_naturality]
  rw [← Category.assoc δ _ _, ← adj'.homEquiv_naturality_left]
  rw [← Category.assoc, ← adj'.homEquiv_naturality_right]
  simp only [Category.assoc]

end AlgebraicGeometry.Etale
```

Its two direct consumers used:

```lean
import all Sheaf.AlgebraicGeometry.CartesianChartExchangeAdjunction
```

## New

Withdraw lean/Sheaf/AlgebraicGeometry/CartesianChartExchangeAdjunction.lean through
deleted.txt, and change the two direct consumers to:

```lean
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeAdjunction
```

The upstream module supplies the same complete implementations. Each consumer
changes its private proof import; Comparison also disables the privateModule
linter, matching the existing private helper modules, because it intentionally
contains only private declarations; every declaration, proof body and
public import in those consumers remains verbatim. No source-library file changes.
Evaluation also receives a proof-only elaboration repair. Its unchanged source
timed out at 60 seconds. A 5000-heartbeat diagnostic isolated unfolding of
DerivedCategory.Plus.injectiveObjectEquivalence, rightDerivedFunctorPlus and chart
isomorphisms during rfl and broad rewrites. An import-only probe completed in 6.6
seconds, so importing the dependency was not the problem. Evaluation now marks
the concrete constructions locally irreducible, explicitly unfolds only the
outer chart isomorphisms, and specializes two proved generic private helpers for
shifted adjunction evaluation and cancellation. This avoids unfolding the concrete
derived-adjunction data. Both existing statements, including visibility and
universes, are unchanged; the helper's new universe is private. No definition
body or global attribute changes. The privateModule linter is disabled there as
well. The revised file compiled without warnings in 12.4 seconds, under the same
60-second limit and default heartbeat settings. No diagnostic options remain.

No DAG node, unit record or quarantined source refers to the retired module;
there is no attachment or dependency to migrate. The unit route stays intact.


### Evaluation proof repair, old file

```lean
module
public import WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback
import all Sheaf.AlgebraicGeometry.CartesianChartExchangeTransport
@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency true

private theorem cartesianChartAdjunct_spec {S X T B : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S)
    (w : g' = a ≫ g) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (V : B.Etale)
    (z : (abelianHigherDirectImageRawPresheaf
      (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g) q
      (((pullback.snd a (pullback.snd f g))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F))).obj (op V)) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      (pullback.snd f g')).derivedPlus.homEquiv _ _
        ((cartesianChartAdjunctIso f g a g' w F q V).hom z) ≫
          (R+((pullback.snd f g')_*[AddCommGrpCat.{u + 1}]).commShiftIso
            (q : ℤ)).hom.app _ =
      (cartesianChartRawAdjunctionIso f g a g' w F q V).hom z := by
  rfl

private theorem chartCohomologyIso_eval {S X B T : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S) (w : g' = a ≫ g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (V : B.Etale) (U : T.Etale) (r : U.left ⟶ V.left)
    (hr : IsPullback r U.hom V.hom a)
    (z : (abelianHigherDirectImageRawPresheaf
      (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g) n
      (((pullback.snd a (pullback.snd f g))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F))).obj (op V)) :
    (cartesianChartCohomologyIso f g a g' w F n V U r hr).hom
      (rawRestrictedCohomologyComparison _ n _ V z) =
    (DerivedCategory.Plus.singleFunctor _ 0).map
        (abelianFreeRepresentablePullbackSquareIso a V U r hr).hom ≫
      (cartesianChartRawAdjunctionIso f g a g' w F n V).hom z := by
  dsimp only [cartesianChartCohomologyIso]
  erw [add_iso_trans_apply, add_iso_trans_apply]
  simp only [Iso.symm_hom]
  erw [Iso.hom_inv_id_apply]
  erw [yoneda_mapIso_apply]
  rfl

end AlgebraicGeometry.Etale
```

### Evaluation proof repair, new file

```lean
module
public import WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback
import all Sheaf.AlgebraicGeometry.CartesianChartExchangeTransport
set_option linter.privateModule false

@[expose] public section
universe u v
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency true

-- Keep the concrete derived constructions folded while specializing generic identities.
attribute [local irreducible] CategoryTheory.Adjunction.derivedPlus
  upperStarLowerStarAdjunction cartesianChartAdjunctIso
  cartesianChartRawAdjunctionIso cartesianChartCohomologyIso

/-- Evaluate the shifted additive adjunction without unfolding the concrete adjunction. -/
private lemma shifted_add_equiv_eval
    {C D : Type*} [Category.{v} C] [Category.{v} D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasShift D ℤ]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.CommShift ℤ]
    (adj : L ⊣ R) (A : C) (K : D) (q : ℤ) (z : L.obj A ⟶ K⟦q⟧) :
    (AddEquiv.toAddCommGrpIso
      (X := AddCommGrpCat.of (L.obj A ⟶ K⟦q⟧))
      (Y := AddCommGrpCat.of (A ⟶ R.obj (K⟦q⟧))) (adj.homAddEquiv A (K⟦q⟧)) ≪≫
      (preadditiveCoyoneda.obj (op A)).mapIso ((R.commShiftIso q).app K)).hom z =
        adj.homEquiv A (K⟦q⟧) z ≫ (R.commShiftIso q).hom.app K := by
  rfl

private theorem cartesianChartAdjunct_spec {S X T B : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S)
    (w : g' = a ≫ g) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (V : B.Etale)
    (z : (abelianHigherDirectImageRawPresheaf
      (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g) q
      (((pullback.snd a (pullback.snd f g))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F))).obj (op V)) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      (pullback.snd f g')).derivedPlus.homEquiv _ _
        ((cartesianChartAdjunctIso f g a g' w F q V).hom z) ≫
          (R+((pullback.snd f g')_*[AddCommGrpCat.{u + 1}]).commShiftIso
            (q : ℤ)).hom.app _ =
      (cartesianChartRawAdjunctionIso f g a g' w F q V).hom z := by
  unfold cartesianChartRawAdjunctionIso
  symm
  refine (add_iso_trans_apply _ _ z).trans ?_
  exact shifted_add_equiv_eval
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (pullback.snd f g')).derivedPlus
    _ _ (q : ℤ) ((cartesianChartAdjunctIso f g a g' w F q V).hom z)

/-- Cancel the first isomorphism before evaluating the remaining two factors. -/
private lemma cancel_iso_eval {A B C D : AddCommGrpCat.{u}}
    (e : A ≅ B) (f : A ≅ C) (g : C ≅ D) (z : A) :
    (e.symm ≪≫ f ≪≫ g).hom (e.hom z) = g.hom (f.hom z) := by
  simp only [add_iso_trans_apply, Iso.symm_hom, Iso.hom_inv_id_apply]

private theorem chartCohomologyIso_eval {S X B T : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S) (w : g' = a ≫ g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (V : B.Etale) (U : T.Etale) (r : U.left ⟶ V.left)
    (hr : IsPullback r U.hom V.hom a)
    (z : (abelianHigherDirectImageRawPresheaf
      (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g) n
      (((pullback.snd a (pullback.snd f g))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F))).obj (op V)) :
    (cartesianChartCohomologyIso f g a g' w F n V U r hr).hom
      (rawRestrictedCohomologyComparison _ n _ V z) =
    (DerivedCategory.Plus.singleFunctor _ 0).map
        (abelianFreeRepresentablePullbackSquareIso a V U r hr).hom ≫
      (cartesianChartRawAdjunctionIso f g a g' w F n V).hom z := by
  have := isIso_rawRestrictedCohomologyComparison
    (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g) n
    (((pullback.snd a (pullback.snd f g))^*[AddCommGrpCat.{u + 1}]).obj
      (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F)) V
  unfold cartesianChartCohomologyIso
  refine (cancel_iso_eval (asIso (rawRestrictedCohomologyComparison _ n _ V))
    (cartesianChartRawAdjunctionIso f g a g' w F n V)
    ((preadditiveYoneda.obj _).mapIso
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
        (abelianFreeRepresentablePullbackSquareIso a V U r hr)).op) z).trans ?_
  exact yoneda_mapIso_apply
    ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
      (abelianFreeRepresentablePullbackSquareIso a V U r hr))
    ((cartesianChartRawAdjunctionIso f g a g' w F n V).hom z)

end AlgebraicGeometry.Etale
```


The Evaluation consumer retains its public theorem signatures; its proof-only helper and local irreducibility attributes keep elaboration below the single-file compile limit.

## Users

These are the three changed modules listed by tools/downstream.py. Neither direct consumer
has a claim in the current shared coordination snapshot; no held module is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeAdjunction | C2 | Withdraw duplicate. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeComparison | unclaimed | Migrate private import; disable privateModule linter. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeTransport | unclaimed | Migrate private import. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeEvaluation | unclaimed | Preserve signatures; repair slow proof elaboration. |

The Comparison, Transport and Evaluation import closures have no duplicate pairs after
this retirement. All three changed consumers are validated individually with lcompile.py.

## Status

landed 20261020T221101-L-4141840 2026-10-20 (merge of deliver/C2/Sheaf.AlgebraicGeometry.CartesianChartExchangeAdjunction)
