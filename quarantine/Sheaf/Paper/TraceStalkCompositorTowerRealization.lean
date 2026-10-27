/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q52 and K9
-/
module

public import Sheaf.Paper.TraceStalkCompositorTowerData
import Sheaf.Paper.TraceStrictStalkTowers
import Sheaf.Paper.TraceStalkTowerDescent

/-! # Assembly of normalized stalk compositors

The strict finite diagram and its derived descent are separated below the original
existence theorem. Integral composition, iteration and unit follow by cancellation
and counit naturality with the published comparison definitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem unitNormalization {C : Type*} [Category C] {B : Type*} [Category B]
    (F : C ⥤ B) {X Y Z W : C} {T : B} (a : X ≅ Y) (b : Y ≅ Z)
    (c : W ≅ Z) (s : F.obj Y ⟶ T) :
    F.map a.hom ≫ s =
      F.map (a ≪≫ b ≪≫ c.symm).hom ≫ F.map c.hom ≫ F.map b.inv ≫ s := by
  simp

private theorem counitTransport {A B : Type*} [Category A] [Category B]
    (R : A ⥤ B) (L : B ⥤ A) (ε : L ⋙ R ⟶ 𝟭 B)
    {X W : A} {Y Z T : B} (a : X ⟶ L.obj Z) (b : W ⟶ L.obj Y)
    (c : X ⟶ W) (s : Z ⟶ T) (t : Y ⟶ T)
    (hc : c ≫ b ≫ L.map t = a ≫ L.map s) :
    R.map c ≫ R.map b ≫ ε.app Y ≫ t = R.map a ≫ ε.app Z ≫ s := by
  have ht := ε.naturality t
  have hs := ε.naturality s
  dsimp only [Functor.comp_map, Functor.id_map] at ht hs
  rw [← ht, ← hs]
  simp only [← R.map_comp, ← Category.assoc]
  exact congrArg (fun f ↦ R.map f ≫ ε.app T) ((Category.assoc _ _ _).trans hc)

private theorem realizationTransport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (R : A ⥤ B) (U : A ⥤ C) (V : B ⥤ C) (F : C ⥤ D) (G : B ⥤ D)
    (ρ : U ≅ R ⋙ V) (σ : V ⋙ F ≅ G)
    {X Y : A} {Z T : B} (c : X ⟶ Y) (a : R.obj X ⟶ Z) (b : R.obj Y ⟶ T)
    (s : Z ⟶ T) (hc : R.map c ≫ b = a ≫ s) :
    F.map (U.map c) ≫ F.map (ρ.hom.app Y) ≫ F.map (V.map b) ≫ σ.hom.app T =
      F.map (ρ.hom.app X) ≫ F.map (V.map a) ≫ σ.hom.app Z ≫ G.map s := by
  have hρ := ρ.hom.naturality c
  have hσ := σ.hom.naturality s
  dsimp only [Functor.comp_map] at hρ hσ
  rw [← hσ]
  simp only [← Category.assoc, ← F.map_comp]
  rw [hρ]
  simp only [Category.assoc, ← V.map_comp, hc]

private theorem realizationTransport₂
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (R : A ⥤ B) (U : A ⥤ C) (V : B ⥤ C) (F : C ⥤ D) (G : B ⥤ D)
    (ρ : U ≅ R ⋙ V) (σ : V ⋙ F ≅ G)
    {X Y : A} {Z W T : B} (c : X ⟶ Y) (a : R.obj X ⟶ Z) (b : R.obj Y ⟶ W)
    (s : Z ⟶ T) (t : W ⟶ T) (hc : R.map c ≫ b ≫ t = a ≫ s) :
    F.map (U.map c) ≫ F.map (ρ.hom.app Y) ≫ F.map (V.map b) ≫
        σ.hom.app W ≫ G.map t =
      F.map (ρ.hom.app X) ≫ F.map (V.map a) ≫ σ.hom.app Z ≫ G.map s := by
  have h := realizationTransport R U V F G ρ σ c (a ≫ s) (b ≫ t) (𝟙 _)
    (by simpa only [Category.comp_id] using hc)
  have ht := σ.hom.naturality t
  have hs := σ.hom.naturality s
  dsimp only [Functor.comp_map] at ht hs
  simp only [Functor.map_comp, G.map_id, Category.comp_id, Category.assoc] at h
  simp only [← Category.assoc] at h ⊢
  calc
    _ = (F.map (U.map c) ≫ F.map (ρ.hom.app Y) ≫ F.map (V.map b)) ≫
        (F.map (V.map t) ≫ σ.hom.app T) := by rw [ht]; simp only [Category.assoc]
    _ = (F.map (ρ.hom.app X) ≫ F.map (V.map a)) ≫
        (F.map (V.map s) ≫ σ.hom.app T) := by simpa only [Category.assoc] using h
    _ = _ := by rw [hs]; simp only [Category.assoc]


variable (D : FiniteFieldDatum.{u}) (I : IntegralComparisonSystem.{u} l)
  (S : TrfStalkCompositorTowerData l E D I)

private theorem pointUnit
    (hn : ∀ {X : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
      (v : Spec (.of D.k) ⟶ X) (K : sfIntegralConstructibleCategory l E X),
      (S.integral v).hom.app K =
        (pointFibreIntegralAmbient D l E).map
            (((I.coefficient E).pullback v).realization.hom.app K.obj) ≫
          (S.sections v).hom.app (((I.coefficient E).system X).reduction.obj K.obj))
    [hS : ∀ z : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField z)]
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (S.integral (𝟙 (Spec (.of D.k)))).hom.app N =
      (pointFibreIntegralAmbient D l E).map
          (@integralComparisonUnit l _ E _ _ _ I (Spec (.of D.k)) hS N).hom ≫
        (pointFibreIntegralAmbient D l E).map
          (((I.coefficient E).system (Spec (.of D.k))).adjunction.unit.app N.obj) ≫
        (pointFibreIntegralAmbient D l E).map
          ((coefficientSequenceLimit l E _).map
            ((integralComparisonSystemUnit l E _).inv.app
              (((I.coefficient E).system _).reduction.obj N.obj))) ≫
        (S.sections (𝟙 (Spec (.of D.k)))).hom.app
          (((I.coefficient E).system _).reduction.obj N.obj) := by
  rw [hn]
  let h := (I.coefficient E).complete (Spec (.of D.k)) N
  exact unitNormalization (pointFibreIntegralAmbient D l E)
    (((I.coefficient E).pullback (𝟙 (Spec (.of D.k)))).realization.app N.obj)
    ((coefficientSequenceLimit l E _).mapIso
      ((integralComparisonSystemUnit l E _).app
        (((I.coefficient E).system _).reduction.obj N.obj)))
    (asIso (((I.coefficient E).system _).adjunction.unit.app N.obj)) _

private theorem iteration
    (_hn : ∀ {X : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
      (v : Spec (.of D.k) ⟶ X) (K : sfIntegralConstructibleCategory l E X),
      (S.integral v).hom.app K =
        (pointFibreIntegralAmbient D l E).map
            (((I.coefficient E).pullback v).realization.hom.app K.obj) ≫
          (S.sections v).hom.app (((I.coefficient E).system X).reduction.obj K.obj)) :
    ∀ {X Y Z : Scheme.{u}}
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    [hS : ∀ z : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField z)]
    (h : Z ⟶ Y) (f : Y ⟶ X) (w : Spec (.of D.k) ⟶ Z)
    (K : sfIntegralConstructibleCategory l E X),
    (trfCompletedPointFibre l E D w).map
        (@integralComparisonComposition l _ E _ _ _ I X Y Z hX hY hZ h f K).hom ≫
        @trfNestedStalkRealization l _ E _ _ _ D I S Y Z hY hZ hS h w
          ((constructibleIntegralPullback l E f).obj K) ≫
        (S.realization w).map
          ((integralComparisonDerivedSequencePullback l E h).map
            ((integralComparisonPullbackCounit l E f
              ((I.coefficient E).system X) ((I.coefficient E).system Y)
              ((I.coefficient E).roos Y) ((I.coefficient E).pullback f)).app K.obj)) =
      @trfNestedStalkRealization l _ E _ _ _ D I S X Z hX hZ hS (h ≫ f) w K ≫
        (S.realization w).map
          ((integralComparisonSystemComposition l E h f).hom.app
            (((I.coefficient E).system X).reduction.obj K.obj)) := by
  intro X Y Z hX hY hZ hS h f w K
  let k := (integralComparisonPullbackCounit l E f
    ((I.coefficient E).system X) ((I.coefficient E).system Y)
    ((I.coefficient E).roos Y) ((I.coefficient E).pullback f)).app K.obj
  let ch := @integralComparisonComposition l _ E _ _ _ I X Y Z hX hY hZ h f K
  let a := ((I.coefficient E).pullback (h ≫ f)).realization.app K.obj
  let b := ((I.coefficient E).pullback h).realization.app
    ((integralDerivedPullback l E f).obj K.obj)
  let s := (integralComparisonSystemComposition l E h f).hom.app
    (((I.coefficient E).system X).reduction.obj K.obj)
  let t := (integralComparisonDerivedSequencePullback l E h).map k
  have hc : ch.hom ≫ b.hom ≫ (coefficientSequenceLimit l E Z).map t =
      a.hom ≫ (coefficientSequenceLimit l E Z).map s := by
    change ch.hom ≫ (integralComparisonEta l E I h f K).hom = _
    change (a ≪≫ (coefficientSequenceLimit l E Z).mapIso
      ((integralComparisonSystemComposition l E h f).app
        (((I.coefficient E).system X).reduction.obj K.obj)) ≪≫
        (integralComparisonEta l E I h f K).symm).hom ≫ _ = _
    simp [a, s]
  have hr := counitTransport ((I.coefficient E).system Z).reduction
    (coefficientSequenceLimit l E Z) ((I.coefficient E).system Z).adjunction.counit
    a.hom b.hom ch.hom s t hc
  dsimp only [a, b, Iso.app_hom, Functor.comp_obj] at hr
  have ht := realizationTransport₂ ((I.coefficient E).system Z).reduction
    (integralDerivedPullback l E w)
    (integralComparisonDerivedSequencePullback l E w ⋙
      coefficientSequenceLimit l E (Spec (.of D.k)))
    (pointFibreIntegralAmbient D l E) (S.realization w)
    ((I.coefficient E).pullback w).realization (S.sections w)
    ch.hom
    ((integralComparisonPullbackCounit l E (h ≫ f)
      ((I.coefficient E).system X) ((I.coefficient E).system Z)
      ((I.coefficient E).roos Z) ((I.coefficient E).pullback (h ≫ f))).app K.obj)
    ((integralComparisonPullbackCounit l E h
      ((I.coefficient E).system Y) ((I.coefficient E).system Z)
      ((I.coefficient E).roos Z) ((I.coefficient E).pullback h)).app
        ((integralDerivedPullback l E f).obj K.obj)) s t
    (by simpa only [integralComparisonPullbackCounit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc,
      Functor.comp_obj] using hr)
  simpa only [trfNestedStalkRealization, integralComparisonEta, Iso.trans_hom,
    Functor.mapIso_hom, asIso_hom, trfCompletedPointFibre, Functor.comp_map,
    Functor.map_comp, Category.assoc, t, k, s, ch, Iso.app_hom,
    constructibleIntegralPullback, ObjectProperty.lift, ObjectProperty.ι_obj,
    Functor.comp_obj] using ht

private theorem trf_map_compositor_cancel {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {a b c d : A} {z : B}
    (e : a ≅ b) (f : b ≅ c) (g : d ≅ c) (t : F.obj b ⟶ z) :
    F.map (e ≪≫ f ≪≫ g.symm).inv ≫ F.map e.hom ≫ t =
      F.map g.hom ≫ F.map f.inv ≫ t := by
  simp

private theorem trf_integralCompositor (D : FiniteFieldDatum.{u})
    (I : IntegralComparisonSystem.{u} l) (S : TrfStalkCompositorTowerData l E D I)
    (h : TrfStalkTowerDescentLaws l E D I S)
    {X Y : Scheme.{u}}
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hS : ∀ z : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField z)]
    (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y) (K : sfIntegralConstructibleCategory l E X) :
    (pointFibreIntegralAmbient D l E).map
        (@integralComparisonComposition l _ E _ _ _ I X Y
          (Spec (.of D.k)) hX hY hS v f K).inv ≫
        (S.integral (v ≫ f)).hom.app K =
      @trfNestedStalkRealization l _ E _ _ _ D I S X Y hX hY hS f v K ≫
        (S.comparison f v).hom.app (((I.coefficient E).system X).reduction.obj K.obj) := by
  rw [h.integralNormalized]
  calc
    _ = (pointFibreIntegralAmbient D l E).map
          (@integralComparisonEta l _ E _ _ _ I X Y
            (Spec (.of D.k)) hX hY hS v f K).hom ≫
        (pointFibreIntegralAmbient D l E).map
          ((coefficientSequenceLimit l E _).map
            ((integralComparisonSystemComposition l E v f).inv.app
              (((I.coefficient E).system X).reduction.obj K.obj))) ≫
        (S.sections (v ≫ f)).hom.app
          (((I.coefficient E).system X).reduction.obj K.obj) := by
      exact trf_map_compositor_cancel (pointFibreIntegralAmbient D l E)
        (((I.coefficient E).pullback (v ≫ f)).realization.app K.obj)
        ((coefficientSequenceLimit l E _).mapIso
          ((integralComparisonSystemComposition l E v f).app
            (((I.coefficient E).system X).reduction.obj K.obj)))
        (@integralComparisonEta l _ E _ _ _ I X Y
          (Spec (.of D.k)) hX hY hS v f K) _
    _ = _ := by
      rw [h.sectionsComposition]
      exact (Category.assoc _ _ _).symm

/-- The specified stalk compositor is realized by the finite germ comparison on
one whole quotient diagram, with finite section coordinates, iterated pullback,
identity, and automorphism reparametrization compatible before realization.
Source: Stacks sites.tex, Tag 0F4F; blueprint main-20261015,
thm-trf-l-function-euler-product.proof.md, Step 1, Local powers (b)
(blueprint: lem-trf-stalk-compositor-tower-realization).

Proof:
1. Use lem-trf-bounded-quotient-stalk-realization for the simultaneous good-truncation
   zigzag of any flat-term K-flat representative, in its common cohomological interval.
   Exact finite pullback preserves both arrows. No bound on K-flat terms or Tor
   amplitude is used. The same zigzag serves every map in the diagram.
2. Apply lem-trf-proetale-pullback-stalk-coherence degreewise. A pullback germ
   (U,u,V,theta,x) goes to [V,pr_V theta u,x]. Differential, chain maps and actual
   quotient transitions change only x, proving strict naturality on whole systems.
   Normalize finite evaluation by its inverse-image unit on the same generators.
3. In the finite composition law put the middle geometric map v and the identity
   geometric point of s. Identify the identity stalk with sections by the initial
   neighbourhood (s,id). This gives finiteSections, hence the coordinate map
   e_fv inverse composed with c composed with e_v. All equalities retain transitions.
4. For a strict tower map A, its cone map sends (b,a) to (product(A)b,product(A)a).
   Strictness commutes with 1-shift, and the chain equation gives the signed
   differential (-db-(1-shift)a,da). This construction preserves identity and
   composition and sends the strict squares to cone squares without cross terms.
5. Use lem-trf-integral-pullback-comparison-realization with identical coefficient
   extension. Eta is its entire-tower counit comparison, and the defining formula
   eta chi = realization(chi_fin) gives integralCompositor after point sections and
   the e comparisons. Invert these isomorphisms to get the required direction.
   lem-pur-integral-operations-preserve-constructible supplies all nested domains.
6. At w apply the finite composition law to h,f. Both routes on a double germ give
   [V,pr_V theta2 pr_W theta1 u,x]. Replacing x by its quotient image gives the
   strict tower equation finiteComposition, not only its separate derived levels.
7. The specified integral system compositor identifies that last finite factor with
   J_w(chi_h,f). Use the same counit comparisons for all iterates. The finite unit
   is the identity tower under the inverse-image unit; integral completeness gives
   the identity point normalization J_id(N)=Fib_s(N).
8. Reindex every pointed neighbourhood by Spec(alpha), leaving x fixed. The two
   routes in the comparison square give [V,pr_V theta u Spec(alpha),x]. This
   respects the same differential and transitions and yields reparamSquare.
9. Apply the diagonal cone functor and the specified comparisons to this whole
   square. comparisonFactors and reparamFactors give realizedReparam. The two
   cone coordinates retain the same reindexing and no extra homotopy term appears.
10. Chain-map naturality descends through the ordinary localization by
    lem-weil-pbc-localization-universal-property. Invert the squares for
    quasi-isomorphisms and compose them for roofs. The resolution invariance of
    lem-pur-integral-operations-well-defined gives independence of representatives
    and naturality for arbitrary integral derived morphisms. The presentation
    identity in TrfStalkCompositorQuotientCompatible identifies these with the
    e_v,P of lem-trf-bounded-quotient-stalk-realization for every presentation. -/
theorem trfStalkCompositorTowerRealization (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    ∃ (I : IntegralComparisonSystem.{u} l) (S : TrfStalkCompositorTowerData l E D I),
      IntegralComparisonRealizationCoherence l E E (AlgHom.id ℚ_[l] E) I ∧
        TrfStalkCompositorTowerCoherent l E D I S ∧
          TrfStalkCompositorQuotientCompatible l E D I S := by
  obtain ⟨I, hI⟩ := integralPullbackComparisonRealization l E E (AlgHom.id ℚ_[l] E)
  obtain ⟨T, hT⟩ := trfStrictStalkTowers l E D
  obtain ⟨S, hS, hD, hQ⟩ := trfStalkTowerDescent l E D hl I hI T hT
  have hF : TrfStrictStalkTowerCoherent l E D (S.toStrict l E) := by
    rw [hS]
    exact hT
  refine ⟨I, S, hI, ?_, hQ⟩
  exact
    { finiteUnit := hF.finiteUnit
      finiteGerm := hF.finiteGerm
      pointGerm := hF.pointGerm
      sectionGerm := hF.sectionGerm
      comparisonFactors := hD.comparisonFactors
      sectionsFactors := hD.sectionsFactors
      integralNormalized := hD.integralNormalized
      finiteSections := hF.finiteSections
      finiteComposition := hF.finiteComposition
      finiteIdentity := hF.finiteIdentity
      reparamGerm := hF.reparamGerm
      reparamSquare := hF.reparamSquare
      integralCompositor := trf_integralCompositor l E D I S hD
      reparamFactors := hD.reparamFactors
      realizedReparam := hD.realizedReparam
      integralIteration := iteration l E D I S hD.integralNormalized
      realizedIdentity := hD.realizedIdentity
      integralPointUnit := pointUnit l E D I S hD.integralNormalized }

end WeilConjectures
