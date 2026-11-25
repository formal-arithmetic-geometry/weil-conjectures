/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
public import WeilConjectures.TraceFormula.CounitRealization.CounitRealizationSubstitution
public import WeilConjectures.TraceFormula.Supporting.EffectiveComparisonRealizationModels
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.TraceFormula.Supporting.AmbientComparisonSystemExistence
import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible

/-! # Counit scalar comparison in normalized word coordinates

We show that for simultaneous normalized models, the scalar-extension/pullback comparison is
computed in word coordinates by explicit, natural isomorphisms
(`podCounitScalarWordCoordinates`).

## Implementation details

All comparisons are morphisms of entire derived quotient systems. The primitive models retain the
generator and K-injective normalization on every simultaneous flat-term K-flat presentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory AlgebraicGeometry
open WeilConjectures.CounitRealization
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]

/-- The models of an integral comparison system `D`, viewed as word models: systems, Roos
comparisons, pullbacks and scalar extensions are those of `D`. -/
def podCounitWordModels (D : IntegralComparisonSystem.{u} l) : Models.{u} l where
  system a := (D.coefficient a.coefficient.carrier).system a.scheme
  roos a := (D.coefficient a.coefficient.carrier).roos a.scheme
  pullback E {_ _} _ _ f := (D.coefficient E.carrier).pullback f
  scalar E L ι X := (D.scalar E.carrier L.carrier ι).model X

variable (D : IntegralComparisonSystem.{u} l)
  (E L : Coefficient.{u} l) (ι : E.carrier →ₐ[ℚ_[l]] L.carrier)
  {X Y : Scheme.{u}}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)] (g : X ⟶ Y)

/-- The source coordinate: the scalar extension of the pullback realization map, followed by the
primitive scalar comparison at the pullback of `R(K)`. -/
def podCounitScalarBetaA (K : DerivedCategory (scalarReductionSource l E.carrier Y)) :
    (integralScalarExtensionOfUniverses l E.carrier L.carrier ι X).obj
        ((integralDerivedPullback l E.carrier g).obj K) ⟶
      (coefficientSequenceLimit l L.carrier X).obj
        ((integralComparisonDerivedSequenceScalar l E.carrier L.carrier ι X).obj
          ((integralComparisonDerivedSequencePullback l E.carrier g).obj
            (((D.coefficient E.carrier).system Y).reduction.obj K))) :=
  (integralScalarExtensionOfUniverses l E.carrier L.carrier ι X).map
      (((D.coefficient E.carrier).pullback g).realization.hom.app K) ≫
    (Primitive.scalar E L ι X).comparison (podCounitWordModels l D)
      ((integralComparisonDerivedSequencePullback l E.carrier g).obj
        (((D.coefficient E.carrier).system Y).reduction.obj K))

/-- The target coordinate: the pullback of the scalar realization map, followed by the primitive
pullback comparison at the scalar extension of `R(K)`. -/
def podCounitScalarBetaB (K : DerivedCategory (scalarReductionSource l E.carrier Y)) :
    (integralDerivedPullback l L.carrier g).obj
        ((integralScalarExtensionOfUniverses l E.carrier L.carrier ι Y).obj K) ⟶
      (coefficientSequenceLimit l L.carrier X).obj
        ((integralComparisonDerivedSequencePullback l L.carrier g).obj
          ((integralComparisonDerivedSequenceScalar l E.carrier L.carrier ι Y).obj
            (((D.coefficient E.carrier).system Y).reduction.obj K))) :=
  (integralDerivedPullback l L.carrier g).map
      (((D.scalar E.carrier L.carrier ι).model Y).realization.hom.app K) ≫
    (Primitive.pullback L g).comparison (podCounitWordModels l D)
      ((integralComparisonDerivedSequenceScalar l E.carrier L.carrier ι Y).obj
        (((D.coefficient E.carrier).system Y).reduction.obj K))

/-- A derived coefficient system is effective if it is normalized, its limit is
constructible-complete, and the counit of the completion adjunction is invertible on it. -/
def IsPodCounitEffectiveSystem (F : Coefficient.{u} l) (W : Scheme.{u})
    (C : coefficientSequenceDerived l F.carrier W) : Prop :=
  IsNormalizedCoefficientSequence l F.carrier W C ∧
    sfIntegralConstructible l F.carrier W ((coefficientSequenceLimit l F.carrier W).obj C) ∧
    IsIso (((D.coefficient F.carrier).system W).adjunction.counit.app C)

attribute [local irreducible] IsPodCounitEffectiveSystem

/-- The scalar/pullback word-coordinate identity: all intermediate systems are effective, the
completion unit and both coordinates `podCounitScalarBetaA`, `podCounitScalarBetaB` are
invertible, the comparison `integralComparisonScalar` intertwines them, and both coordinates are
natural on constructible inputs. -/
structure PodCounitScalarWordCoordinates : Prop where
  /-- C = R(K) is normalized and effective. -/
  initial : ∀ K : sfIntegralConstructibleCategory l E.carrier Y,
    IsPodCounitEffectiveSystem l D E Y
      (((D.coefficient E.carrier).system Y).reduction.obj K.obj)
  /-- The first pullback intermediate U_E C is effective. -/
  pullback : ∀ K : sfIntegralConstructibleCategory l E.carrier Y,
    IsPodCounitEffectiveSystem l D E X
      ((integralComparisonDerivedSequencePullback l E.carrier g).obj
        (((D.coefficient E.carrier).system Y).reduction.obj K.obj))
  /-- The first scalar intermediate S_Y C is effective. -/
  scalar : ∀ K : sfIntegralConstructibleCategory l E.carrier Y,
    IsPodCounitEffectiveSystem l D L Y
      ((integralComparisonDerivedSequenceScalar l E.carrier L.carrier ι Y).obj
        (((D.coefficient E.carrier).system Y).reduction.obj K.obj))
  /-- A = S_X U_E C is effective, including its entire-system counit. -/
  sourceWord : ∀ K : sfIntegralConstructibleCategory l E.carrier Y,
    IsPodCounitEffectiveSystem l D L X
      ((integralComparisonDerivedSequenceScalar l E.carrier L.carrier ι X).obj
        ((integralComparisonDerivedSequencePullback l E.carrier g).obj
          (((D.coefficient E.carrier).system Y).reduction.obj K.obj)))
  /-- B = U_L S_Y C is effective, including its entire-system counit. -/
  targetWord : ∀ K : sfIntegralConstructibleCategory l E.carrier Y,
    IsPodCounitEffectiveSystem l D L X
      ((integralComparisonDerivedSequencePullback l L.carrier g).obj
        ((integralComparisonDerivedSequenceScalar l E.carrier L.carrier ι Y).obj
          (((D.coefficient E.carrier).system Y).reduction.obj K.obj)))
  /-- The actual completion unit K -> L R K is invertible. -/
  unit : ∀ K : sfIntegralConstructibleCategory l E.carrier Y,
    IsIso (((D.coefficient E.carrier).system Y).adjunction.unit.app K.obj)
  /-- Both explicitly prescribed coordinates are invertible. -/
  coordinates : ∀ K : sfIntegralConstructibleCategory l E.carrier Y,
    IsIso (podCounitScalarBetaA l D E L ι g K.obj) ∧
      IsIso (podCounitScalarBetaB l D E L ι g K.obj)
  /-- The comparison `integralComparisonScalar` intertwines the two coordinates. -/
  comparison : ∀ K : sfIntegralConstructibleCategory l E.carrier Y,
    (integralComparisonScalar l E.carrier L.carrier ι D g K).hom ≫
        podCounitScalarBetaB l D E L ι g K.obj =
      podCounitScalarBetaA l D E L ι g K.obj ≫
        (coefficientSequenceLimit l L.carrier X).map
          ((integralComparisonSystemScalarPullback l E.carrier L.carrier ι g).hom.app
            (((D.coefficient E.carrier).system Y).reduction.obj K.obj))
  /-- Naturality of beta_A for every derived morphism of constructible inputs. -/
  naturalityA : ∀ (K K' : sfIntegralConstructibleCategory l E.carrier Y) (φ : K ⟶ K'),
    (integralScalarExtensionOfUniverses l E.carrier L.carrier ι X).map
        ((integralDerivedPullback l E.carrier g).map φ.hom) ≫
        podCounitScalarBetaA l D E L ι g K'.obj =
      podCounitScalarBetaA l D E L ι g K.obj ≫
        (coefficientSequenceLimit l L.carrier X).map
          ((integralComparisonDerivedSequenceScalar l E.carrier L.carrier ι X).map
            ((integralComparisonDerivedSequencePullback l E.carrier g).map
              (((D.coefficient E.carrier).system Y).reduction.map φ.hom)))
  /-- Naturality of beta_B, with the target word in the indicated order. -/
  naturalityB : ∀ (K K' : sfIntegralConstructibleCategory l E.carrier Y) (φ : K ⟶ K'),
    (integralDerivedPullback l L.carrier g).map
        ((integralScalarExtensionOfUniverses l E.carrier L.carrier ι Y).map φ.hom) ≫
        podCounitScalarBetaB l D E L ι g K'.obj =
      podCounitScalarBetaB l D E L ι g K.obj ≫
        (coefficientSequenceLimit l L.carrier X).map
          ((integralComparisonDerivedSequencePullback l L.carrier g).map
            ((integralComparisonDerivedSequenceScalar l E.carrier L.carrier ι Y).map
              (((D.coefficient E.carrier).system Y).reduction.map φ.hom)))

private theorem roos_unique (F : Coefficient.{u} l) (W : Scheme.{u})
    (ρ ρ' : IntegralComparisonRoosModel l F.carrier W) : ρ = ρ' := by
  suffices h : ρ.comparison = ρ'.comparison by
    cases ρ
    cases ρ'
    cases h
    rfl
  apply Iso.ext_inv
  apply NatTrans.ext
  funext C
  obtain ⟨I, hI, q, _, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective C
  have : QuasiIso q := hq
  have : IsIso ((DerivedCategory.Q ⋙ coefficientConstantTowerLimit l F.carrier W).map q) := by
    change IsIso ((coefficientConstantTowerLimit l F.carrier W).map (DerivedCategory.Q.map q))
    infer_instance
  have hi : ρ.comparison.app I = ρ'.comparison.app I := by
    apply Iso.ext
    exact (ρ.computes I).trans (ρ'.computes I).symm
  apply (cancel_mono ((DerivedCategory.Q ⋙ coefficientConstantTowerLimit l F.carrier W).map q)).1
  rw [← ρ.comparison.inv.naturality q, ← ρ'.comparison.inv.naturality q]
  exact congrArg (fun z ↦
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      integralOperationsRoosFunctor ⋙ DerivedCategory.Q).map q ≫ z) (congrArg Iso.inv hi)

private theorem reduction_iso_evaluation (F : Coefficient.{u} l) (W : Scheme.{u})
    (S T : CoefficientDerivedSystemCalculus l F.carrier W)
    (K : DerivedCategory (scalarReductionSource l F.carrier W)) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l F.carrier W n).map
        ((S.adjunction.leftAdjointUniq T.adjunction).hom.app K) ≫
      (T.reductionEvaluation n).hom.app K = (S.reductionEvaluation n).hom.app K := by
  let V := coefficientSequenceDerivedEvaluation l F.carrier W n
  let R := coefficientFiniteDerivedRestriction l F.carrier W n
  let α := S.adjunction.leftAdjointUniq T.adjunction
  have he : (S.reductionEvaluation n).inv.app K ≫ V.map (α.hom.app K) =
      (T.reductionEvaluation n).inv.app K := by
    apply ((coefficientFiniteAdjunction l F.carrier W n).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, R.map_comp,
      ← Category.assoc, ← S.unit_projection]
    have hp := (coefficientSequenceProjection l F.carrier W n).naturality (α.hom.app K)
    dsimp only [Functor.comp_map] at hp
    rw [Category.assoc, ← hp, ← Category.assoc]
    rw [Adjunction.unit_leftAdjointUniq_hom_app, T.unit_projection]
  apply (cancel_epi ((S.reductionEvaluation n).inv.app K)).1
  simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using
    congrArg (fun f ↦ f ≫ (T.reductionEvaluation n).hom.app K) he

private theorem completion_normalized (F : Coefficient.{u} l) (W : Scheme.{u})
    [∀ x : W, Invertible (l : W.residueField x)]
    (S : CoefficientDerivedSystemCalculus l F.carrier W)
    (ρ : IntegralComparisonRoosModel l F.carrier W) :
    IsEffectiveComparisonCompletionNormalized l F.carrier W S ρ := by
  obtain ⟨T⟩ := effectiveComparisonRealizationModels.{u} l
  let S₀ := T.system F.carrier W
  let α := S₀.adjunction.leftAdjointUniq S.adjunction
  have hρ : T.roos F.carrier W = ρ := roos_unique l F W _ _
  intro P C e κ hp hc
  have hp₀ : CoefficientReductionPresentation l F.carrier W
      S₀.toCoefficientDerivedSystemReduction P.obj P.property.1 C
      (α.app (DerivedCategory.Q.obj P.obj) ≪≫ e) κ := by
    refine ⟨?_, hp.2⟩
    intro n
    dsimp only [CoefficientComparisonEquation, Iso.trans_hom, Iso.app_hom]
    rw [Functor.map_comp, Category.assoc, hp.1 n, ← Category.assoc,
      reduction_iso_evaluation]
  have hc₀ : IsIntegralComparisonPresentationCoherent l F.carrier W S₀ P.obj C
      (α.app (DerivedCategory.Q.obj P.obj) ≪≫ e) κ := by
    have hu : S₀.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceLimit l F.carrier W).map
          ((α.app (DerivedCategory.Q.obj P.obj)).hom ≫ e.hom) =
        S.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫
          (coefficientSequenceLimit l F.carrier W).map e.hom := by
      dsimp only [Iso.app_hom]
      rw [Functor.map_comp, ← Category.assoc,
        Adjunction.unit_leftAdjointUniq_hom_app]
    unfold IsIntegralComparisonPresentationCoherent at hc ⊢
    obtain ⟨b, hb, he⟩ := hc
    refine ⟨b, hb, ?_⟩
    dsimp only [Iso.trans_hom]
    rw [hu]
    exact he
  obtain ⟨v, hv, hz, he⟩ := T.completion_normalization F.carrier W P C
    (α.app (DerivedCategory.Q.obj P.obj) ≪≫ e) κ hp₀ hc₀
  refine ⟨v, hv, hz, ?_⟩
  rw [hρ] at he
  dsimp only [Iso.trans_hom, Iso.app_hom] at he
  rw [Functor.map_comp, ← Category.assoc, ← Category.assoc,
    Adjunction.unit_leftAdjointUniq_hom_app] at he
  simpa only [Category.assoc] using he

private theorem primitive_effective (M : Models.{u} l)
    {a b : Location.{u} l} (O : Primitive l a b)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    (hN : IsNormalizedCoefficientSequence l a.coefficient.carrier a.scheme C)
    (hC : sfIntegralConstructible l a.coefficient.carrier a.scheme
      ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C)) :
    IsNormalizedCoefficientSequence l b.coefficient.carrier b.scheme (O.system.obj C) ∧
      sfIntegralConstructible l b.coefficient.carrier b.scheme
        ((coefficientSequenceLimit l b.coefficient.carrier b.scheme).obj (O.system.obj C)) ∧
      IsIso ((M.system b).adjunction.counit.app (O.system.obj C)) := by
  have laws := (counitRealizationSubstitution l M).1
  have : IsIso ((M.system a).adjunction.counit.app C) := laws.counit a C hN
  have hi : IsIso (O.comparison M C) := by
    dsimp only [Primitive.comparison]
    infer_instance
  have hc : sfIntegralConstructible l b.coefficient.carrier b.scheme
      (O.completed.obj ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C)) := by
    cases O with
    | pullback F f =>
      exact ((integralOperations_preserve_constructible l F.carrier f).1 _ hC).1
    | scalar F G i W =>
      exact sfIntegralScalarExtension_constructible (l + 1) l (by omega)
        F.carrier G.carrier i W _ hC
  have ht := (sfIntegralConstructible l b.coefficient.carrier b.scheme).prop_of_iso
    (asIso (O.comparison M C)) hc
  have hn : IsNormalizedCoefficientSequence l b.coefficient.carrier b.scheme
      (O.system.obj C) := (laws.invertible (.atom O) C hN ⟨hC, ht⟩).2
  exact ⟨hn, ht, laws.counit b _ hn⟩

private theorem coordinate_eq
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (R : A ⥤ B) (O : B ⥤ C) (L : C ⥤ D) (H : A ⥤ D)
    (b : H ⟶ R ⋙ O ⋙ L) {P Q : A} {N : B} (f : P ⟶ Q) (e : R.obj Q ⟶ N) :
    H.map f ≫ (b.app Q ≫ L.map (O.map e)) =
      b.app P ≫ L.map (O.map (R.map f ≫ e)) := by
  rw [← Category.assoc, b.naturality]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]

private theorem coordinate_naturality
    {A B C D F G : Type*} [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* F] [Category* G]
    (R : A ⥤ B) (U : B ⥤ C) (J : C ⥤ D) (T : D ⥤ C)
    (S : C ⥤ F) (L : F ⥤ G) (Uh : A ⥤ D) (Sh : D ⥤ G)
    (bU : Uh ⟶ R ⋙ U ⋙ J) (bS : Sh ⟶ T ⋙ S ⋙ L) (e : J ⋙ T ⟶ 𝟭 C)
    {K K' : A} (f : K ⟶ K') :
    Sh.map (Uh.map f) ≫
        (Sh.map (bU.app K') ≫ bS.app (J.obj (U.obj (R.obj K'))) ≫
          L.map (S.map (e.app (U.obj (R.obj K'))))) =
      (Sh.map (bU.app K) ≫ bS.app (J.obj (U.obj (R.obj K))) ≫
          L.map (S.map (e.app (U.obj (R.obj K))))) ≫
        L.map (S.map (U.map (R.map f))) := by
  let r : J ⋙ Sh ⟶ S ⋙ L :=
    Functor.whiskerLeft J bS ≫ Functor.whiskerRight (Functor.whiskerRight e S) L
  let b : Uh ⋙ Sh ⟶ R ⋙ U ⋙ S ⋙ L :=
    Functor.whiskerRight bU Sh ≫ Functor.whiskerLeft (R ⋙ U) r
  simpa only [b, r, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_map, Functor.comp_obj] using b.naturality f

private theorem betaA_eq_lambda (K : sfIntegralConstructibleCategory l E.carrier Y) :
    podCounitScalarBetaA l D E L ι g K.obj =
      (integralComparisonLambda l E.carrier L.carrier ι D g K).hom := by
  dsimp only [podCounitScalarBetaA, Primitive.comparison, Primitive.model,
    Primitive.system, Primitive.completed, podCounitWordModels, integralComparisonLambda,
    Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, asIso_hom, integralComparisonPullbackCounit,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  exact coordinate_eq _ _ _ _ _ _ _

private theorem betaB_eq_mu (K : sfIntegralConstructibleCategory l E.carrier Y) :
    podCounitScalarBetaB l D E L ι g K.obj =
      (integralComparisonMu l E.carrier L.carrier ι D g K).hom ≫
        (coefficientSequenceLimit l L.carrier X).map
          ((integralComparisonSystemScalarPullback l E.carrier L.carrier ι g).hom.app
            (((D.coefficient E.carrier).system Y).reduction.obj K.obj)) := by
  dsimp only [podCounitScalarBetaB, Primitive.comparison, Primitive.model,
    Primitive.system, Primitive.completed, podCounitWordModels, integralComparisonMu, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, asIso_hom, integralComparisonScalarCounit,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.symm_hom, Functor.mapIso_inv, Iso.app_inv]
  rw [Category.assoc, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact coordinate_eq _ _ _ _ _ _ _

/-- There is an integral comparison system whose models satisfy the quotient-augmentation
completion normalization, and for every integral comparison system `D`, every coefficient
extension `ι : E → L` and every isomorphism `g : X ⟶ Y`, the scalar/pullback word-coordinate
identity `PodCounitScalarWordCoordinates l D E L ι g` holds. -/
theorem podCounitScalarWordCoordinates (l : ℕ) [Fact l.Prime] :
    (∃ D : IntegralComparisonSystem.{u} l,
      ∀ (F : Coefficient.{u} l) (W : Scheme.{u})
        [∀ x : W, Invertible (l : W.residueField x)],
        IsEffectiveComparisonCompletionNormalized l F.carrier W
          ((D.coefficient F.carrier).system W) ((D.coefficient F.carrier).roos W)) ∧
      ∀ (D : IntegralComparisonSystem.{u} l)
        (E L : Coefficient.{u} l) (ι : E.carrier →ₐ[ℚ_[l]] L.carrier)
        {X Y : Scheme.{u}}
        [∀ x : X, Invertible (l : X.residueField x)]
        [∀ y : Y, Invertible (l : Y.residueField y)] (g : X ⟶ Y) [IsIso g],
        PodCounitScalarWordCoordinates l D E L ι g := by
  classical
  refine ⟨?_, ?_⟩
  · obtain ⟨D⟩ := ambientComparisonSystem_exists.{u} l
    refine ⟨D, ?_⟩
    intro F W hW
    exact completion_normalized l F W _ _
  · intro D E L ι X Y hX hY g hg
    let M := podCounitWordModels l D
    have laws := (counitRealizationSubstitution l M).1
    have h0 (K : sfIntegralConstructibleCategory l E.carrier Y) :
        IsPodCounitEffectiveSystem l D E Y
          (((D.coefficient E.carrier).system Y).reduction.obj K.obj) := by
      unfold IsPodCounitEffectiveSystem
      have hu := (D.coefficient E.carrier).complete Y K
      have hn : IsNormalizedCoefficientSequence l E.carrier Y
          (((D.coefficient E.carrier).system Y).reduction.obj K.obj) :=
        ((D.coefficient E.carrier).system Y).reduction_normalized K.obj
      exact ⟨hn, (sfIntegralConstructible l E.carrier Y).prop_of_iso
        (asIso (((D.coefficient E.carrier).system Y).adjunction.unit.app K.obj)) K.property,
        laws.counit ⟨E, Y, hY⟩ _ hn⟩
    have initial := h0
    unfold IsPodCounitEffectiveSystem at h0
    have hp (K : sfIntegralConstructibleCategory l E.carrier Y) :=
      primitive_effective l M (Primitive.pullback E g) _ (h0 K).1 (h0 K).2.1
    have hs (K : sfIntegralConstructibleCategory l E.carrier Y) :=
      primitive_effective l M (Primitive.scalar E L ι Y) _ (h0 K).1 (h0 K).2.1
    refine ⟨initial, ?_, ?_, ?_, ?_, (D.coefficient E.carrier).complete Y, ?_, ?_, ?_, ?_⟩
    · intro K
      unfold IsPodCounitEffectiveSystem
      exact hp K
    · intro K
      unfold IsPodCounitEffectiveSystem
      exact hs K
    · intro K
      unfold IsPodCounitEffectiveSystem
      exact primitive_effective l M (Primitive.scalar E L ι X) _ (hp K).1 (hp K).2.1
    · intro K
      unfold IsPodCounitEffectiveSystem
      exact primitive_effective l M (Primitive.pullback L g) _ (hs K).1 (hs K).2.1
    · intro K
      rw [betaA_eq_lambda, betaB_eq_mu]
      exact ⟨inferInstance, inferInstance⟩
    · intro K
      rw [betaA_eq_lambda, betaB_eq_mu]
      simp only [integralComparisonScalar, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Iso.inv_hom_id_assoc]
    · intro K K' φ
      exact coordinate_naturality _ _ _ _ _ _ _ _ _ _ _ φ.hom
    · intro K K' φ
      exact coordinate_naturality _ _ _ _ _ _ _ _ _ _ _ φ.hom

end WeilConjectures
