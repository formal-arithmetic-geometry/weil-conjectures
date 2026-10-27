/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.Paper.TowerGeometricPurityData
import Sheaf.Paper.TowerIsomorphismPullback
import Sheaf.Paper.TowerPurityPresentationRetagging
import Sheaf.Paper.TowerSemilinearPurityFactors

/-! # Assembly of the geometric tower purity result

Source: latest blueprint equivariance of purity and trace, Steps 1 and 5.
(blueprint: lem-pur-isomorphism-purity-assembly).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [local irreducible] AlgebraicGeometry.ProEtale.SpGeometricPurity.exchange
  AlgebraicGeometry.ProEtale.SpGeometricPurity.mate
  AlgebraicGeometry.ProEtale.SpGeometricPurity.pullRealization

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures

private theorem tensor_factor_square
    {C D : Type*} [Category* C] [Category* D]
    (T : C × C ⥤ C) (T' : D × D ⥤ D) (P : C ⥤ D)
    (μ : T ⋙ P ≅ (P.prod P) ⋙ T')
    {A L W B : C} {A' L' W' B' : D}
    (a : L ⟶ W) (a' : L' ⟶ W') (r : P.obj L ⟶ L')
    (h : P.obj A ⟶ A') (u : P.obj W ⟶ W')
    (m : T.obj (A, W) ⟶ B) (m' : T'.obj (A', W') ⟶ B')
    (e : P.obj B ⟶ B')
    (ha : P.map a ≫ u = r ≫ a')
    (hm : P.map m ≫ e = μ.hom.app (A, W) ≫ T'.map (Prod.mkHom h u) ≫ m') :
    P.map (T.map (Prod.mkHom (𝟙 A) a) ≫ m) ≫ e =
      μ.hom.app (A, L) ≫ T'.map (Prod.mkHom h r) ≫
        T'.map (Prod.mkHom (𝟙 A') a') ≫ m' := by
  rw [Functor.map_comp, Category.assoc, hm]
  have hn := μ.hom.naturality (Prod.mkHom (𝟙 A) a)
  change P.map (T.map (Prod.mkHom (𝟙 A) a)) ≫ μ.hom.app (A, W) =
    μ.hom.app (A, L) ≫ T'.map (Prod.mkHom (P.map (𝟙 A)) (P.map a)) at hn
  rw [P.map_id] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  have hp : Prod.mkHom (𝟙 (P.obj A)) (P.map a) ≫ Prod.mkHom h u =
      Prod.mkHom h r ≫ Prod.mkHom (𝟙 A') a' := by
    apply Prod.ext
    · simp
    · exact ha
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun v ↦ μ.hom.app (A, L) ≫ T'.map v ≫ m') hp

private theorem mate_component
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {F : A ⥤ B} {G : B ⥤ A} {F' : C ⥤ D} {G' : D ⥤ C}
    {Q : A ⥤ C} {P : B ⥤ D} (adj : F ⊣ G) (adj' : F' ⊣ G')
    (α : TwoSquare Q F F' P) (K : B) :
    (mateEquiv adj adj' α).natTrans.app K =
      adj'.homEquiv _ _ (α.natTrans.app (G.obj K) ≫ P.map (adj.counit.app K)) := by
  simp [mateEquiv, Adjunction.homEquiv_unit]
namespace AlgebraicGeometry.ProEtale.SpGeometricPurity
/-- The two constituent base-change equations imply the full isomorphism-square
purity result, with the given counit mate and the fixed strict root comparison.
Source: equivariance Step 1, substitution of purity-bc-factors (1)--(2), and Step 5.
(blueprint: lem-pur-isomorphism-purity-assembly).

Proof: Obtain pullback domains, normalization and the strict root map from the exact
isomorphism inverse image. Compare the two normalized presentations by Retagging.
Use semilinear_purity_factors for the orientation and tensor-map equations. Tensor
pullback naturality and functoriality combine them into the purity square. Cancel
pulled-back purity to get conjugation. It proves mate invertibility by reflection
through the fully faithful realization. Naturality follows by conjugating the
natural mate with the natural purity isomorphisms and realization counit. The mate
component formula is the adjunction Hom transpose. Normalization of the four
composites follows by applying the pullback preservation and a's two normalization
fields in order. -/
theorem isomorphism_purity_result
    (S : PurityFiniteSetting.{u})
    (b : SpTowerShriek.Base S.coefficients.l S.extension)
    (o : SpTowerShriek.Operations S.coefficients.l S.extension b)
    (q : SpTowerCalculus.Coordinates S.coefficients.l S.extension b)
    {X Z Y : AlgebraicGeometry.Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
  (d : ℕ) (w : SpChartAdmissibility.Twists S.coefficients.l S.extension X)
  (hF : ∀ K : SpTowerCalculus.C S.coefficients.l S.extension b q X,
    spConstructibleTorTowers S.coefficients.l S.extension Y (q.abelian Y)
      ((SpTowerCalculus.F S.coefficients.l S.extension b o q (SpTowerGamma.factorization j p)).obj
        K.obj))
  (G : SpTowerCalculus.C S.coefficients.l S.extension b q Y ⥤ SpTowerCalculus.C S.coefficients.l
    S.extension b q X)
  (adj : SpTowerGluing.support S.coefficients.l S.extension b o q (SpTowerGamma.factorization j p)
    hF ⊣ G)
  (lv : SpTowerGluing.Levels S.coefficients.l S.extension b o q (SpTowerGamma.factorization j p) hF
    G adj)
  (a : SpTowerGamma.Purity S.coefficients.l S.extension b o q j p d w hF G adj lv)
  [AlgebraicGeometry.Scheme.Over X (Spec (.of S.field.k))]
  [AlgebraicGeometry.Scheme.Over Y (Spec (.of S.field.k))]
  [IsSeparated (X ↘ Spec (.of S.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of S.field.k))] [QuasiCompact (X ↘ Spec (.of S.field.k))]
  [IsSeparated (Y ↘ Spec (.of S.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of S.field.k))] [QuasiCompact (Y ↘ Spec (.of S.field.k))]
  [(j ≫ p).IsOver (Spec (.of S.field.k))] [hsm : SmoothOfRelativeDimension d (j ≫ p)]
  (gX : X ⟶ X) (gY : Y ⟶ Y) [hGX : IsIso gX] [hGY : IsIso gY]
  (sq : IsPullback gX (j ≫ p) (j ≫ p) gY)
  (z : SpTowerCalculus.FiniteCoordinates S.coefficients.l S.extension)
  (h : SpTowerCalculus.Preservation S.coefficients.l S.extension S.field.k b o q)
  (cal : SpTowerCalculus.Calculus S.coefficients.l S.extension S.field.k b o q z h)
  (x : SpTowerShriek.OpenExchange S.coefficients.l S.extension b o)
  (laws : SpTowerShriek.Laws S.coefficients.l S.extension b o x) :
    Nonempty (Result S.coefficients.l S.extension b o q j p d w hF G adj lv a S.field.k gX gY sq z h
      cal x) := by
  classical
  obtain ⟨hx, hnX, hrX⟩ := isomorphism_tower_pullback S.coefficients.l S.extension b o q gX
  obtain ⟨hy, hnY, _⟩ := isomorphism_tower_pullback S.coefficients.l S.extension b o q gY
  obtain ⟨t⟩ := hrX w a.roots
  have hr := purity_presentation_retagging S b o q j p d w hF G adj lv a
  obtain ⟨hb, u, hu, ht⟩ := semilinear_purity_factors S b o q j p d w hF G adj lv a
    gX gY sq z h cal x laws hx hy t hr
  let F := SpTowerGluing.support S.coefficients.l S.extension b o q (SpTowerGamma.factorization j p)
    hF
  let PX := Q S.coefficients.l S.extension b o q gX hx
  let PY := P S.coefficients.l S.extension b o q gY hy
  let RX := SpTowerGamma.realization S.coefficients.l S.extension b q X
  let pull := SpTowerShriek.pull S.coefficients.l S.extension b (o.geometry gX)
  let H := SpTowerGamma.source S.coefficients.l S.extension b o q (j ≫ p) w d
  let e := mate S.coefficients.l S.extension b o q S.field.k (j ≫ p) gX gY sq
    (SpTowerGamma.factorization j p)
    z h cal x hx hy hF G adj hb
  let γ : H ≅ G ⋙ RX := NatIso.ofComponents
    (fun K ↦ purityIso S.coefficients.l S.extension b o q j p d w hF G adj lv a K)
    (fun v ↦ a.naturality _ _ v)
  let cX : PX ⋙ RX ≅ RX ⋙ pull := NatIso.ofComponents
    (fun K ↦ pullRealization S.coefficients.l S.extension b o q gX hx K)
    (fun v ↦ by
      simpa only [PX, Q, RX, SpTowerGamma.realization, SpTowerCalculus.etalePullback,
        SpTowerCalculus.inclusion, pullRealization, Functor.comp_map, Functor.comp_obj,
        Functor.id_map, ObjectProperty.ι_obj_lift_map, Iso.app_hom] using
        (SpTowerCalculus.realization S.coefficients.l S.extension b X
          (q.abelian X)).counitIso.hom.naturality (pull.map (RX.map v)))
  let er : (G ⋙ RX) ⋙ pull ⟶ PY ⋙ G ⋙ RX :=
    Functor.whiskerLeft G cX.inv ≫ Functor.whiskerRight e RX
  have hsquare (K : SpTowerCalculus.C S.coefficients.l S.extension b q Y) :
      pull.map (γ.hom.app K) ≫ er.app K =
        (sourceComparison S.coefficients.l S.extension b o q (j ≫ p) gX gY sq hy w a.roots t d
          K).hom ≫
          γ.hom.app (PY.obj K) := by
    simpa only [γ, purityIso, asIso_hom, SpTowerGamma.gamma, er, cX, RX, e, PY, H,
      SpTowerGamma.source, SpTowerGamma.tensorSource, Prod.sectL, Functor.comp_obj,
      NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, sourceComparison,
      Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom, Category.assoc] using
      (tensor_factor_square
      (SpTowerShriek.tensor S.coefficients.l S.extension b X) (SpTowerShriek.tensor S.coefficients.l
        S.extension b X)
      pull (o.geometry gX).tensorPullback a.orientation.hom a.orientation.hom
      (orderedRoots S.coefficients.l S.extension b o t d).hom _ u _ _ _ hu (ht K))
  have hconj (K : SpTowerCalculus.C S.coefficients.l S.extension b q Y) :
      er.app K = (pull.mapIso (γ.app K)).inv ≫
        (sourceComparison S.coefficients.l S.extension b o q (j ≫ p) gX gY sq hy w a.roots t d
          K).hom ≫
          γ.hom.app (PY.obj K) := by
    apply (cancel_epi (pull.mapIso (γ.app K)).hom).1
    simp only [Iso.hom_inv_id_assoc]
    simpa only [Functor.mapIso_hom, Iso.app_hom] using hsquare K
  let sourceMap : H ⋙ pull ⟶ PY ⋙ H :=
    Functor.whiskerRight γ.hom pull ≫ er ≫ Functor.whiskerLeft PY γ.inv
  have sourceMap_eq (K : SpTowerCalculus.C S.coefficients.l S.extension b q Y) :
      sourceMap.app K =
        (sourceComparison S.coefficients.l S.extension b o q (j ≫ p) gX gY sq hy w a.roots t d
          K).hom := by
    apply (cancel_mono (γ.app (PY.obj K)).hom).1
    simpa only [sourceMap, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.assoc, Iso.inv_hom_id_app,
      Functor.comp_obj, Iso.app_hom, Category.comp_id] using hsquare K
  have hRX : RX.FullyFaithful :=
    (spConstructibleTorTowers S.coefficients.l S.extension X (q.abelian X)).fullyFaithfulι.comp
      (SpTowerCalculus.realization S.coefficients.l S.extension b X
        (q.abelian X)).fullyFaithfulFunctor
  have he : IsIso e := by
    have hei (K : SpTowerCalculus.C S.coefficients.l S.extension b q Y) : IsIso (e.app K) := by
      have her : IsIso (er.app K) := by
        rw [hconj K]
        infer_instance
      have hreal : IsIso (RX.map (e.app K)) := by
        exact (isIso_comp_left_iff (cX.inv.app (G.obj K)) _).mp her
      exact hRX.isIso_of_isIso_map (e.app K)
    let := hei
    exact NatIso.isIso_of_isIso_app e
  refine ⟨{
    pullX := hx
    pullY := hy
    roots := t
    retagging := hr
    exchange_iso := hb
    mate_iso := he
    support_normalized := ?_
    exceptional_normalized := ?_
    transpose := ?_
    source_naturality := ?_
    purity_square := hsquare
    conjugation := hconj }⟩
  · intro M hM
    exact ⟨hnY (F.obj M) (a.support_normalized M hM),
      a.support_normalized (PX.obj M) (hnX M hM)⟩
  · intro K hK
    exact ⟨hnX (G.obj K) (a.exceptional_normalized K hK),
      a.exceptional_normalized (PY.obj K) (hnY K hK)⟩
  · intro K
    unfold mate
    exact mate_component adj adj _ K
  · intro K L v
    simpa only [sourceMap_eq, Functor.comp_map] using sourceMap.naturality v

end AlgebraicGeometry.ProEtale.SpGeometricPurity
