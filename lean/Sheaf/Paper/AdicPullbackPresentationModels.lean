/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.Paper.PbcActualStrictPullback
public import Sheaf.Paper.CompletedTowerPullback
public import Sheaf.Paper.CompletedPullbackReduction
public import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
public import Sheaf.Paper.CompletedRlimFunctor
public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Mathlib.CategoryTheory.Adjunction.Mates

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Paper.FiniteQuotientTransitionCompatibility
import all Sheaf.Algebra.Homology.DiagramKFlatReplacements
import all Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Sheaf.Paper.ReductionPullbackDerivedTower
import all Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
import all Sheaf.Paper.OpenImmersionTensorPiece
/-!
# Normalized models for adic pullback presentations

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-cbc,
lem-cbc-completed-extension-zero-comparison.proof.md; Stacks Tags 05S7 and 03DI.
(blueprint: lem-cbc-adic-pullback-presentation-models).

The coefficient uniqueness statement first identifies both presentations with the published
coefficient map. The subsequent statements use these identifications to write both universal
pairs over the same ordinary functor. No invertibility of the completed coefficient map is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u c v
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory Opposite
open scoped ZeroObject

-- A normalized comparison on resolving objects descends through fully faithful restriction.
/-- Counit normalization on a family of representatives, written in arbitrary categories.
Source: Stacks Tag 05S7, normalization of comparisons of derived functors
(blueprint: lem-cbc-adic-pullback-presentation-models). -/
def CategoryTheory.Functor.HasRepresentativeNormalization
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    (L : C ⥤ E) (T : D ⥤ F) (H : E ⥤ F) (G : C ⥤ D)
    {I : Type*} (good : I → Prop)
    (q : I → C) (k : I → D) (p : I → E) (z : I → F)
    (a : ∀ i, L.obj (q i) ⟶ p i) (c : ∀ i, T.obj (k i) ⟶ z i)
    (f : ∀ i, G.obj (q i) ⟶ k i) (l : ∀ i, H.obj (p i) ⟶ z i)
    (b : L ⋙ H ≅ G ⋙ T) : Prop :=
  ∀ i, good i → H.map (a i) ≫ l i = b.hom.app (q i) ≫ T.map (f i) ≫ c i

private theorem constantNormalizationTransport
    {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {A A' A'' : C} {B B' C₀ C₀' Z : D}
    (s : A ≅ A') (t : B ≅ B') (r : C₀ ⟶ C₀')
    (a : A' ⟶ A'') (ε : A ⟶ A'') (l : H.obj A'' ⟶ Z)
    (k : B ⟶ C₀) (k' : B' ⟶ C₀') (c : C₀' ⟶ Z) (τ : C₀ ⟶ Z)
    (hs : s.hom ≫ a = ε) (ht : r ≫ c = τ) (hn : k ≫ r = t.hom ≫ k')
    (b : H.obj A ⟶ B) :
    (H.map ε ≫ l = b ≫ k ≫ τ) ↔
      (H.map a ≫ l = (H.map s.inv ≫ b ≫ t.hom) ≫ k' ≫ c) := by
  rw [← hs, H.map_comp, Category.assoc, ← ht, ← Category.assoc k,
    hn, Category.assoc]
  rw [← cancel_epi (H.map s.hom)]
  simp only [Category.assoc, ← H.map_comp_assoc, Iso.hom_inv_id]
  simp

private theorem constantNormalizationTransportNat
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {L L' : C ⥤ E} {T T' : D ⥤ F} (H : E ⥤ F) (G : C ⥤ D)
    (s : L ≅ L') (t : T ≅ T') {I : Type*} (good : I → Prop)
    (q : I → C) (k : I → D) (p : I → E) (z : I → F)
    (a : ∀ i, L.obj (q i) ⟶ p i) (a' : ∀ i, L'.obj (q i) ⟶ p i)
    (c : ∀ i, T.obj (k i) ⟶ z i) (c' : ∀ i, T'.obj (k i) ⟶ z i)
    (f : ∀ i, G.obj (q i) ⟶ k i) (l : ∀ i, H.obj (p i) ⟶ z i)
    (hs : ∀ i, s.hom.app (q i) ≫ a' i = a i)
    (ht : ∀ i, t.hom.app (k i) ≫ c' i = c i) (b : L ⋙ H ≅ G ⋙ T) :
    (∀ i, good i → H.map (a i) ≫ l i = b.hom.app (q i) ≫ T.map (f i) ≫ c i) ↔
    (∀ i, good i → H.map (a' i) ≫ l i =
      (Functor.isoWhiskerRight s.symm H ≪≫ b ≪≫
        Functor.isoWhiskerLeft G t).hom.app (q i) ≫ T'.map (f i) ≫ c' i) := by
  have h (i : I) := constantNormalizationTransport H (s.app (q i))
    (t.app (G.obj (q i))) (t.hom.app (k i)) (a' i) (a i) (l i)
    (T.map (f i)) (T'.map (f i)) (c' i) (c i) (hs i) (ht i)
    (t.hom.naturality (f i)) (b.hom.app (q i))
  constructor
  · intro hb i hi
    simpa only [Iso.app_hom, Iso.app_inv, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app] using (h i).1 (hb i hi)
  · intro hb i hi
    apply (h i).2
    simpa only [Iso.app_hom, Iso.app_inv, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app] using hb i hi

private theorem isoConjugate_unique
    {C : Type*} [Category* C] {A A' B B' : C} (a : A ≅ A') (z : B ≅ B')
    (P : (A ≅ B) → Prop) (Q : (A' ≅ B') → Prop)
    (h : ∀ b, P b ↔ Q (a.symm ≪≫ b ≪≫ z)) (c : A' ≅ B') (hc : Q c)
    (hu : ∀ b, Q b → b = c) :
    P (a ≪≫ c ≪≫ z.symm) ∧ ∀ b, P b → b = a ≪≫ c ≪≫ z.symm := by
  constructor
  · apply (h _).2
    simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id,
      Iso.trans_refl] using hc
  · intro b hb
    have he := congrArg (fun c ↦ a ≪≫ c ≪≫ z.symm) (hu _ ((h b).1 hb))
    simpa only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.self_symm_id,
      Iso.trans_refl] using he

private theorem normalizedComparison
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (Q : C ⥤ D) (P : ObjectProperty C)
    (ff : ((whiskeringLeft P.FullSubcategory D E).obj (P.ι ⋙ Q)).FullyFaithful)
    (F G : D ⥤ E) (H : C ⥤ E) (α : Q ⋙ F ⟶ H) (β : Q ⋙ G ⟶ H)
    (ha : ∀ X, P X → IsIso (α.app X)) (hb : ∀ X, P X → IsIso (β.app X)) :
    ∃! e : F ≅ G, ∀ X, P X → α.app X = e.hom.app (Q.obj X) ≫ β.app X := by
  let a : P.ι ⋙ Q ⋙ F ≅ P.ι ⋙ H :=
    NatIso.ofComponents (fun X ↦ @asIso _ _ _ _ (α.app X.obj) (ha X.obj X.property))
      (fun f ↦ α.naturality f.hom)
  let b : P.ι ⋙ Q ⋙ G ≅ P.ι ⋙ H :=
    NatIso.ofComponents (fun X ↦ @asIso _ _ _ _ (β.app X.obj) (hb X.obj X.property))
      (fun f ↦ β.naturality f.hom)
  let e := ff.preimageIso (a ≪≫ b.symm)
  have he (X : P.FullSubcategory) :
      e.hom.app (Q.obj X.obj) = (a ≪≫ b.symm).hom.app X :=
    congrArg (fun z ↦ z.app X) (ff.map_preimage (a ≪≫ b.symm).hom)
  have hs : ∀ X, P X → α.app X = e.hom.app (Q.obj X) ≫ β.app X := by
    intro X hX
    rw [he ⟨X, hX⟩]
    have := hb X hX
    simp [a, b]
  refine ⟨e, hs, ?_⟩
  intro e' he'
  apply Iso.ext
  apply ff.map_injective
  ext X
  change e'.hom.app (Q.obj X.obj) = e.hom.app (Q.obj X.obj)
  have := hb X.obj X.property
  exact (cancel_mono (β.app X.obj)).1
    ((he' X.obj X.property).symm.trans (hs X.obj X.property))

private def complexCounit
    {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ L ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C).symm L).hom ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ)) ε ≫
    (Functor.associator _ _ _).inv ≫
    (Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ))
      DerivedCategory.Qh).hom ≫
    (Functor.associator _ _ _).hom ≫
    (Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso D)).hom

private theorem complexCounit_app
    {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex C ℤ) :
    (complexCounit F L ε).app P = Functor.leftDerivedCounitOnComplex F L ε P := by
  simp [complexCounit, Functor.leftDerivedCounitOnComplex]

private theorem derivedComplexCounit_isIso
    {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex C ℤ)
    [IsIso (ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P))] :
    IsIso (Functor.leftDerivedCounitOnComplex F L ε P) := by
  unfold Functor.leftDerivedCounitOnComplex
  infer_instance

private theorem evaluationComplex_eq
    {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (n : ℕ) (P : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) :
    (((CategoryTheory.evaluation ℕᵒᵖ D).obj (op n)).mapHomologicalComplex (.up ℤ)).obj
        ((((Functor.whiskeringRight ℕᵒᵖ C D).obj F).mapHomologicalComplex (.up ℤ)).obj P) =
      (F.mapHomologicalComplex (.up ℤ)).obj
        ((((CategoryTheory.evaluation ℕᵒᵖ C).obj (op n)).mapHomologicalComplex (.up ℤ)).obj
          P) := by
  rfl

private def evaluationComplexIso
    {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (((Functor.whiskeringRight ℕᵒᵖ C D).obj F).mapHomologicalComplex (.up ℤ)) ⋙
      ((CategoryTheory.evaluation ℕᵒᵖ D).obj (op n)).mapHomologicalComplex (.up ℤ) ≅
      ((CategoryTheory.evaluation ℕᵒᵖ C).obj (op n)).mapHomologicalComplex (.up ℤ) ⋙
        F.mapHomologicalComplex (.up ℤ) :=
  NatIso.ofComponents (fun P ↦ eqToIso (evaluationComplex_eq F n P))
    (by
      intro P P' f
      simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl)

private def EvaluationNormalization
    {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (F : C ⥤ D) [F.Additive]
    (FT : (ℕᵒᵖ ⥤ C) ⥤ (ℕᵒᵖ ⥤ D)) [FT.Additive]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (T : DerivedCategory (ℕᵒᵖ ⥤ C) ⥤ DerivedCategory (ℕᵒᵖ ⥤ D))
    (τ : DerivedCategory.Qh ⋙ T ⟶
      FT.mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (n : ℕ)
    (e : FT.mapHomologicalComplex (.up ℤ) ⋙
      ((CategoryTheory.evaluation ℕᵒᵖ D).obj (op n)).mapHomologicalComplex (.up ℤ) ≅
      ((CategoryTheory.evaluation ℕᵒᵖ C).obj (op n)).mapHomologicalComplex (.up ℤ) ⋙
        F.mapHomologicalComplex (.up ℤ))
    (good : ObjectProperty (CochainComplex (ℕᵒᵖ ⥤ C) ℤ))
    (v : T ⋙ ((CategoryTheory.evaluation ℕᵒᵖ D).obj (op n)).mapDerivedCategory ≅
      ((CategoryTheory.evaluation ℕᵒᵖ C).obj (op n)).mapDerivedCategory ⋙ L) : Prop :=
  ∀ P, good P →
    (((CategoryTheory.evaluation ℕᵒᵖ D).obj (op n)).mapDerivedCategory).map
        (Functor.leftDerivedCounitOnComplex
          FT T τ P) ≫
      ((CategoryTheory.evaluation ℕᵒᵖ D).obj (op n)).mapDerivedCategoryFactors.hom.app
        ((FT.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (e.hom.app P) =
    v.hom.app (DerivedCategory.Q.obj P) ≫
      L.map (((CategoryTheory.evaluation ℕᵒᵖ C).obj (op n)).mapDerivedCategoryFactors.hom.app
        P) ≫
      Functor.leftDerivedCounitOnComplex F L ε
        ((((CategoryTheory.evaluation ℕᵒᵖ C).obj (op n)).mapHomologicalComplex (.up ℤ)).obj P)

private theorem evaluationNormalization_exists
    {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (F : C ⥤ D) [F.Additive]
    (FT : (ℕᵒᵖ ⥤ C) ⥤ (ℕᵒᵖ ⥤ D)) [FT.Additive]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (T : DerivedCategory (ℕᵒᵖ ⥤ C) ⥤ DerivedCategory (ℕᵒᵖ ⥤ D))
    (τ : DerivedCategory.Qh ⋙ T ⟶
      FT.mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (n : ℕ)
    (e : FT.mapHomologicalComplex (.up ℤ) ⋙
      ((CategoryTheory.evaluation ℕᵒᵖ D).obj (op n)).mapHomologicalComplex (.up ℤ) ≅
      ((CategoryTheory.evaluation ℕᵒᵖ C).obj (op n)).mapHomologicalComplex (.up ℤ) ⋙
        F.mapHomologicalComplex (.up ℤ))
    (good : ObjectProperty (CochainComplex (ℕᵒᵖ ⥤ C) ℤ))
    (res : ∀ K : CochainComplex (ℕᵒᵖ ⥤ C) ℤ,
      ∃ (P : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) (p : P ⟶ K), good P ∧ QuasiIso p)
    (hε : ∀ P, good P → IsIso (ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj
      ((((CategoryTheory.evaluation ℕᵒᵖ C).obj (op n)).mapHomologicalComplex (.up ℤ)).obj P))))
    (hτ : ∀ P, good P → IsIso (τ.app ((HomotopyCategory.quotient (ℕᵒᵖ ⥤ C) (.up ℤ)).obj P))) :
    ∃! v : T ⋙ ((CategoryTheory.evaluation ℕᵒᵖ D).obj (op n)).mapDerivedCategory ≅
      ((CategoryTheory.evaluation ℕᵒᵖ C).obj (op n)).mapDerivedCategory ⋙ L,
      EvaluationNormalization F FT L ε T τ n e good v := by
  classical
  let EY := (CategoryTheory.evaluation ℕᵒᵖ C).obj (op n)
  let EX := (CategoryTheory.evaluation ℕᵒᵖ D).obj (op n)
  let ffc := cochainRepresentativeWhiskering good res (DerivedCategory D)
  let α : DerivedCategory.Q ⋙ T ⋙ EX.mapDerivedCategory ⟶
      EY.mapHomologicalComplex (.up ℤ) ⋙ F.mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (complexCounit FT T τ) EX.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (FT.mapHomologicalComplex (.up ℤ))
        EX.mapDerivedCategoryFactors.hom ≫
      (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight e DerivedCategory.Q).hom ≫
      (Functor.associator _ _ _).hom
  let β : DerivedCategory.Q ⋙ EY.mapDerivedCategory ⋙ L ⟶
      EY.mapHomologicalComplex (.up ℤ) ⋙ F.mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
    (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight EY.mapDerivedCategoryFactors L).hom ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (EY.mapHomologicalComplex (.up ℤ)) (complexCounit F L ε)
  have ha (P) (hP : good P) : IsIso (α.app P) := by
    let := hτ P hP
    have := derivedComplexCounit_isIso FT T τ P
    have : IsIso ((complexCounit FT T τ).app P) := by
      rw [complexCounit_app]; infer_instance
    dsimp [α]
    infer_instance
  have hb (P) (hP : good P) : IsIso (β.app P) := by
    let := hε P hP
    have := derivedComplexCounit_isIso F L ε
      ((EY.mapHomologicalComplex (.up ℤ)).obj P)
    have : IsIso ((complexCounit F L ε).app
        ((EY.mapHomologicalComplex (.up ℤ)).obj P)) := by
      rw [complexCounit_app]; infer_instance
    dsimp [β]
    infer_instance
  obtain ⟨v, hv, huv⟩ := normalizedComparison DerivedCategory.Q good ffc
    (T ⋙ EX.mapDerivedCategory) (EY.mapDerivedCategory ⋙ L)
    (EY.mapHomologicalComplex (.up ℤ) ⋙ F.mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q) α β ha hb
  have heq (v : T ⋙ EX.mapDerivedCategory ≅ EY.mapDerivedCategory ⋙ L) :
      (∀ P, good P → α.app P = v.hom.app (DerivedCategory.Q.obj P) ≫ β.app P) ↔
        EvaluationNormalization F FT L ε T τ n e good v := by
    simp only [α, β, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom,
      complexCounit_app, Category.id_comp, Category.comp_id]
    rfl
  exact ⟨v, (heq v).1 hv, fun v' hv' ↦ huv v' ((heq v').2 hv')⟩

private theorem counit_isIso_of_iso
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (Q : C ⥤ D) (H : C ⥤ E) (L L' : D ⥤ E)
    (ε : Q ⋙ L ⟶ H) (ε' : Q ⋙ L' ⟶ H)
    (s : L ≅ L') (hs : Functor.whiskerLeft Q s.hom ≫ ε' = ε)
    (P : C) (h : IsIso (ε'.app P)) : IsIso (ε.app P) := by
  let := h
  have hh := congr_app hs P
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hh
  rw [← hh]
  infer_instance

private theorem evaluationNormalization_of_canonical
    {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (F : C ⥤ D) [F.Additive]
    (FT : (ℕᵒᵖ ⥤ C) ⥤ (ℕᵒᵖ ⥤ D)) [FT.Additive]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (T : DerivedCategory (ℕᵒᵖ ⥤ C) ⥤ DerivedCategory (ℕᵒᵖ ⥤ D))
    (τ : DerivedCategory.Qh ⋙ T ⟶
      FT.mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (L₀ : DerivedCategory C ⥤ DerivedCategory D)
    (ε₀ : DerivedCategory.Qh ⋙ L₀ ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (T₀ : DerivedCategory (ℕᵒᵖ ⥤ C) ⥤ DerivedCategory (ℕᵒᵖ ⥤ D))
    (τ₀ : DerivedCategory.Qh ⋙ T₀ ⟶ FT.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (s : L ≅ L₀) (t : T ≅ T₀)
    (hs : Functor.whiskerLeft DerivedCategory.Qh s.hom ≫ ε₀ = ε)
    (ht : Functor.whiskerLeft DerivedCategory.Qh t.hom ≫ τ₀ = τ)
    (n : ℕ)
    (e : FT.mapHomologicalComplex (.up ℤ) ⋙
      ((CategoryTheory.evaluation ℕᵒᵖ D).obj (op n)).mapHomologicalComplex (.up ℤ) ≅
      ((CategoryTheory.evaluation ℕᵒᵖ C).obj (op n)).mapHomologicalComplex (.up ℤ) ⋙
        F.mapHomologicalComplex (.up ℤ))
    (good : ObjectProperty (CochainComplex (ℕᵒᵖ ⥤ C) ℤ))
    (res : ∀ K : CochainComplex (ℕᵒᵖ ⥤ C) ℤ,
      ∃ (P : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) (p : P ⟶ K), good P ∧ QuasiIso p)
    (hε₀ : ∀ P, good P → IsIso (ε₀.app ((HomotopyCategory.quotient C (.up ℤ)).obj
      ((((CategoryTheory.evaluation ℕᵒᵖ C).obj (op n)).mapHomologicalComplex (.up ℤ)).obj P))))
    (hτ₀ : ∀ P, good P → IsIso (τ₀.app ((HomotopyCategory.quotient (ℕᵒᵖ ⥤ C) (.up ℤ)).obj P))) :
    ∃! v : T ⋙ ((CategoryTheory.evaluation ℕᵒᵖ D).obj (op n)).mapDerivedCategory ≅
      ((CategoryTheory.evaluation ℕᵒᵖ C).obj (op n)).mapDerivedCategory ⋙ L,
      EvaluationNormalization F FT L ε T τ n e good v := by
  have hε (P) (hP : good P) := counit_isIso_of_iso DerivedCategory.Qh _ L L₀ ε ε₀
    s hs _ (hε₀ P hP)
  have hτ (P) (hP : good P) := counit_isIso_of_iso DerivedCategory.Qh _ T T₀ τ τ₀
    t ht _ (hτ₀ P hP)
  exact evaluationNormalization_exists F FT L ε T τ n e good res hε hτ

namespace CochainComplex

-- Resolve the entire tower functorially, so its transition maps remain strict.
set_option synthInstance.maxSize 1024 in
private theorem diagramResolution
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v} C]
    (T : GrothendieckTopology C)
    [T.HasSheafCompose (forget₂ CommRingCat.{max c v} RingCat.{max c v})]
    [T.WEqualsLocallyBijective AddCommGrpCat.{max c v}]
    [HasSheafify T AddCommGrpCat.{max c v}]
    (R : Sheaf T CommRingCat.{max c v})
    (K : CochainComplex (ℕᵒᵖ ⥤ SheafOfModules.{max c v}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)) ℤ) :
    ∃ (P : CochainComplex (ℕᵒᵖ ⥤ SheafOfModules.{max c v}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)) ℤ) (p : P ⟶ K),
      QuasiIso p ∧ ∀ j : ℕᵒᵖ, IsKFlatIndependentCoefficients (P.asFunctor.obj j) := by
  classical
  let A := SheafOfModules.{max c v}
    ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.monoidalClosed_kfi (R := R)
  let := SheafOfModules.monoidalPreadditive_kfi R
  have := SheafOfModules.hasExactColimits_int_kfi R
  let := SheafOfModules.hasFunctorialFlatResolution_kfi R
  have (X : A) : PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y) (by intros; simp [curriedTensor]))
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ A))).reduced
  have hι : (ObjectProperty.flat.ι : _ ⥤ A).essImage ≤ ObjectProperty.flat := by
    rintro X ⟨Y, ⟨e⟩⟩
    exact ObjectProperty.prop_of_iso _ e Y.property
  let P := diagramComplex (K.asFunctor ⋙ Λ.resolutionFunctor)
  let p : P ⟶ K :=
    { f := fun n ↦
        { app := fun j ↦ (Λ.resolutionNatTrans.app (K.asFunctor.obj j)).f n
          naturality := fun j k a ↦ congrArg (fun f ↦ f.f n)
            (Λ.resolutionNatTrans.naturality (K.asFunctor.map a)) }
      comm' := by
        intro n m _
        apply NatTrans.ext
        funext j
        exact (Λ.resolutionNatTrans.app (K.asFunctor.obj j)).comm n m }
  refine ⟨P, p, ?_, ?_⟩
  · rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro j
    change QuasiIso (Λ.resolutionNatTrans.app (K.asFunctor.obj j))
    infer_instance
  · intro j
    have hk := Λ.kFlat_resolutionFunctor_obj hι (K.asFunctor.obj j)
    change (Λ.resolutionFunctor.obj (K.asFunctor.obj j)).IsAcyclicTensorKFlat
    intro Z hZ
    let U := tensorRight (Λ.resolutionFunctor.obj (K.asFunctor.obj j))
    have hz : QuasiIso (0 : (0 : CochainComplex A ℤ) ⟶ Z) := by
      rw [quasiIso_iff]
      intro i
      exact (quasiIsoAt_iff_exactAt _ i
        ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hZ i)
    have hmap : QuasiIso (U.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) := hk.2 _ hz
    have htzero : (U.obj (0 : CochainComplex A ℤ)).Acyclic :=
      HomologicalComplex.acyclic_of_isZero _ (U.map_isZero (isZero_zero _))
    exact fun i ↦ (exactAt_iff_of_quasiIsoAt
      (U.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) i).1 (htzero i)

end CochainComplex

namespace AlgebraicGeometry.Scheme

private theorem canonicalOrdinaryPair {X Y : Scheme.{u}} (g : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    IsCompletedOrdinaryPullbackPair g d
      (completedOrdinaryPullback g d) (completedOrdinaryPullbackCounit g d) := by
  unfold completedOrdinaryPullback completedOrdinaryPullbackCounit
  exact (completedOrdinaryPullback_exists g d).choose_spec.choose_spec

private theorem canonicalTowerPair {X Y : Scheme.{u}} (g : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    IsCompletedTowerPullbackPair g d
      (completedTowerPullback g d) (completedTowerPullbackCounit g d) := by
  unfold completedTowerPullback completedTowerPullbackCounit
  exact (completedTowerPullback_exists g d).choose_spec.choose_spec

end AlgebraicGeometry.Scheme

private theorem inverseMate_counit_formula
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (H : D ⥤ F) :
    ((mateEquiv a₁ a₂).symm
      (TwoSquare.mk R₁ H (L₁ ⋙ H ⋙ R₂) R₂
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight a₁.counit _ ≫ (Functor.leftUnitor _).hom))).natTrans =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (L₁ ⋙ H) a₂.counit ≫ (Functor.rightUnitor _).hom := by
  apply NatTrans.ext
  funext M
  dsimp [mateEquiv]
  simp [← Functor.map_comp, a₁.left_triangle_components]

private theorem derivedCounitOnComplex_comp
    {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (L₁ L₂ : DerivedCategory C ⥤ DerivedCategory D)
    (ε₁ : DerivedCategory.Qh ⋙ L₁ ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ε₂ : DerivedCategory.Qh ⋙ L₂ ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : L₁ ⟶ L₂) (he : Functor.whiskerLeft DerivedCategory.Qh e ≫ ε₂ = ε₁)
    (P : CochainComplex C ℤ) :
    e.app (DerivedCategory.Q.obj P) ≫ Functor.leftDerivedCounitOnComplex F L₂ ε₂ P =
      Functor.leftDerivedCounitOnComplex F L₁ ε₁ P := by
  have h := congr_app he ((HomotopyCategory.quotient C (.up ℤ)).obj P)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  dsimp only [Functor.leftDerivedCounitOnComplex]
  rw [← e.naturality_assoc]
  simpa only [Category.assoc, Functor.comp_obj] using
    congrArg (fun f ↦ L₁.map ((DerivedCategory.quotientCompQhIso C).inv.app P) ≫ f ≫
      DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
      (DerivedCategory.quotientCompQhIso D).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) h

private theorem normalizationTransportCounits
    {A B A' B' : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
    [Category* A'] [Abelian A'] [Category* B'] [Abelian B']
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory A'] [HasDerivedCategory B']
    (F : A ⥤ B) [F.Additive] (FT : A' ⥤ B') [FT.Additive]
    (H : DerivedCategory B ⥤ DerivedCategory B')
    (G : DerivedCategory A ⥤ DerivedCategory A')
    (Δ : CochainComplex A ℤ ⥤ CochainComplex A' ℤ)
    (L L₀ : DerivedCategory A ⥤ DerivedCategory B)
    (T T₀ : DerivedCategory A' ⥤ DerivedCategory B')
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ε₀ : DerivedCategory.Qh ⋙ L₀ ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (τ : DerivedCategory.Qh ⋙ T ⟶ FT.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (τ₀ : DerivedCategory.Qh ⋙ T₀ ⟶ FT.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (s : L ≅ L₀) (t : T ≅ T₀)
    (hs : Functor.whiskerLeft DerivedCategory.Qh s.hom ≫ ε₀ = ε)
    (ht : Functor.whiskerLeft DerivedCategory.Qh t.hom ≫ τ₀ = τ)
    (good : CochainComplex A ℤ → Prop)
    (f : ∀ P, G.obj (DerivedCategory.Q.obj P) ⟶ DerivedCategory.Q.obj (Δ.obj P))
    (l : ∀ P, H.obj (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) ⟶
      DerivedCategory.Q.obj ((FT.mapHomologicalComplex (.up ℤ)).obj (Δ.obj P)))
    (b : L ⋙ H ≅ G ⋙ T) :
    (∀ P, good P → H.map (Functor.leftDerivedCounitOnComplex F L ε P) ≫ l P =
      b.hom.app (DerivedCategory.Q.obj P) ≫ T.map (f P) ≫
        Functor.leftDerivedCounitOnComplex FT T τ (Δ.obj P)) ↔
    (∀ P, good P → H.map (Functor.leftDerivedCounitOnComplex F L₀ ε₀ P) ≫ l P =
      (Functor.isoWhiskerRight s.symm H ≪≫ b ≪≫
        Functor.isoWhiskerLeft G t).hom.app (DerivedCategory.Q.obj P) ≫
          T₀.map (f P) ≫ Functor.leftDerivedCounitOnComplex FT T₀ τ₀ (Δ.obj P)) := by
  exact constantNormalizationTransportNat H G s t good
    (fun P ↦ DerivedCategory.Q.obj P) (fun P ↦ DerivedCategory.Q.obj (Δ.obj P))
    (fun P ↦ DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (fun P ↦ DerivedCategory.Q.obj ((FT.mapHomologicalComplex (.up ℤ)).obj (Δ.obj P)))
    (Functor.leftDerivedCounitOnComplex F L ε) (Functor.leftDerivedCounitOnComplex F L₀ ε₀)
    (fun P ↦ Functor.leftDerivedCounitOnComplex FT T τ (Δ.obj P))
    (fun P ↦ Functor.leftDerivedCounitOnComplex FT T₀ τ₀ (Δ.obj P)) f l
    (derivedCounitOnComplex_comp F L L₀ ε ε₀ s.hom hs)
    (fun P ↦ derivedCounitOnComplex_comp FT T T₀ τ τ₀ t.hom ht (Δ.obj P)) b

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

private theorem constantDirect_naturality
    {B C : CommRingCat.{u + 1}} (φ : B ⟶ C) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map φ ≫
        proEtaleConstantDirectImageMap g CommRingCat.{u + 1} C =
      proEtaleConstantDirectImageMap g CommRingCat.{u + 1} B ≫
        (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map φ) := by
  apply ((sheafificationAdjunction (ProEt.topology Y)
    CommRingCat.{u + 1}).homEquiv _ _).injective
  change (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv _ _
    ((presheafToSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
      ((Functor.const Y.ProEtᵒᵖ).map φ) ≫ _) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext V
  exact congr_app
    (toSheafify_naturality (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map φ))
      ((proEtaleBaseChange g).op.obj V)

private theorem constantInverse_naturality
    {B C : CommRingCat.{u + 1}} (φ : B ⟶ C) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map φ) ≫
      proEtaleConstantInverseImageMap g CommRingCat.{u + 1} C =
    proEtaleConstantInverseImageMap g CommRingCat.{u + 1} B ≫
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map φ := by
  unfold proEtaleConstantInverseImageMap
  rw [← Functor.map_comp_assoc, constantDirect_naturality g φ, Functor.map_comp]
  simp only [Category.assoc]
  rw [← (proEtaleSheafAdjunction g CommRingCat.{u + 1}).counit_naturality]

/-- Projection-normalized coefficient presentations are the published coefficient map;
finite constant-section maps commute with every quotient transition, including identities.
Source: blueprint CBC presentation argument, Step 1; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-models).
Proof: completion is the limit of the finite coefficient sheaves, so its projections
are jointly monic. The prescribed components are those of completedCoefficientMap.
For the quotient square, take adjuncts: both maps on the constant presheaf send a scalar
to its quotient constant section. Sheafification and the inverse-image adjunction identify
them. This also applies to the empty scheme and the zero quotient ring. -/
theorem adic_pullback_coefficient_presentations
    (c₁ c₂ : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (pbcAdicCompletion Y d) ⟶ pbcAdicCompletion X d)
    (h₁ : ∀ n : ℕ, c₁ ≫ pbcAdicProjection X d n = completedCoefficientComponent g d n)
    (h₂ : ∀ n : ℕ, c₂ ≫ pbcAdicProjection X d n = completedCoefficientComponent g d n) :
    c₁ = c₂ ∧ c₁ = completedCoefficientMap g d ∧
      ∀ (b a : ℕ) (hab : a ≤ b),
        completedFiniteCoefficientMap g d b ≫ pbcAdicQuotient X d b a hab =
          (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
            (pbcAdicQuotient Y d b a hab) ≫ completedFiniteCoefficientMap g d a := by
  have unique (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (pbcAdicCompletion Y d) ⟶ pbcAdicCompletion X d)
      (hc : ∀ n : ℕ, c ≫ pbcAdicProjection X d n =
        completedCoefficientComponent g d n) : c = completedCoefficientMap g d := by
    apply limit.hom_ext
    intro ⟨n⟩
    change c ≫ pbcAdicProjection X d n =
      completedCoefficientMap g d ≫ pbcAdicProjection X d n
    rw [hc n]
    unfold completedCoefficientMap pbcAdicProjection
    symm
    apply limit.lift_π
  refine ⟨(unique c₁ h₁).trans (unique c₂ h₂).symm, unique c₁ h₁, ?_⟩
  let c : adicLisseRingSystem Y d.ideal ⋙
      proEtaleSheafInverseImage g CommRingCat.{u + 1} ⟶
      adicLisseRingSystem X d.ideal :=
    NatTrans.ofOpSequence
      (fun n ↦ proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
        (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))))
      (fun n ↦ by
        simpa only [Functor.comp_map, adicLisseRingSystem,
          Functor.ofOpSequence_map_homOfLE_succ] using
          constantInverse_naturality g
            (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1))))
  let t := Functor.whiskerRight (pbcConstantSystemComparison Y d).inv
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}) ≫
    c ≫ (pbcConstantSystemComparison X d).hom
  intro b a hab
  exact (t.naturality (homOfLE hab).op).symm

/-- Module pullback for a specified coefficient presentation, using the existing sheaf tensor.
Source: blueprint CBC presentation argument, Step 2
(blueprint: lem-cbc-adic-pullback-presentation-models). -/
def adicPresentationPullback
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (pbcAdicCompletion Y d) ⟶ pbcAdicCompletion X d) :=
  proEtaleModuleInverseImage g (pbcAdicCompletion Y d) ⋙ reductionChange X c

/-- The identity on balanced tensors is equality transport along coefficient uniqueness.
Its inverse is the same identity formula. Source: blueprint CBC argument, Step 2
(blueprint: lem-cbc-adic-pullback-presentation-models). -/
def adicPresentationIdentity
    (c₁ c₂ : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (pbcAdicCompletion Y d) ⟶ pbcAdicCompletion X d)
    (h₁ : ∀ n : ℕ, c₁ ≫ pbcAdicProjection X d n = completedCoefficientComponent g d n)
    (h₂ : ∀ n : ℕ, c₂ ≫ pbcAdicProjection X d n = completedCoefficientComponent g d n) :
    adicPresentationPullback g d c₁ ≅ adicPresentationPullback g d c₂ :=
  eqToIso (congrArg (adicPresentationPullback g d)
    (adic_pullback_coefficient_presentations g d c₁ c₂ h₁ h₂).1)

/-- Proof that the published ordinary pair is a universal left-derived pair.
Source: blueprint CBC argument, Step 3; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-models).
Proof: completedOrdinaryPullback_exists constructs this very counited pair by the
one-object K-flat resolving class. Its first property is precisely the assertion. -/
theorem adicPresentationOrdinaryUniversal_proof :
    (completedOrdinaryPullback g d).IsLeftDerivedFunctor
      (completedOrdinaryPullbackCounit g d)
      (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)) := by
  exact (canonicalOrdinaryPair g d).1

/-- The published ordinary pair carries its universal left-derived structure.
Source: blueprint CBC argument, Step 3; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-models). -/
instance adicPresentationOrdinaryUniversal :
    (completedOrdinaryPullback g d).IsLeftDerivedFunctor
      (completedOrdinaryPullbackCounit g d)
      (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)) :=
  adicPresentationOrdinaryUniversal_proof g d

/-- Proof that the published strict-tower pair is a universal left-derived pair.
Source: blueprint CBC argument, Step 3; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-models).
Proof: completedTowerPullback_exists constructs this pair by strict diagram K-flat
replacements. Its first property is precisely the universal derived property. -/
theorem adicPresentationTowerUniversal_proof :
    (completedTowerPullback g d).IsLeftDerivedFunctor
      (completedTowerPullbackCounit g d)
      (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ)) := by
  exact (canonicalTowerPair g d).1

/-- The published strict-tower pair carries its universal left-derived structure.
Source: blueprint CBC argument, Step 3; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-models). -/
instance adicPresentationTowerUniversal :
    (completedTowerPullback g d).IsLeftDerivedFunctor
      (completedTowerPullbackCounit g d)
      (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ)) :=
  adicPresentationTowerUniversal_proof g d

section Ordinary
variable (L : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
  (ε : DerivedCategory.Qh ⋙ L ⟶
    (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [L.IsLeftDerivedFunctor ε
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))]

/-- The universal counit fixes the comparison to the published ordinary pair.
Source: blueprint CBC argument, Step 3; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-models). -/
def adicPresentationOrdinaryIso : L ≅ completedOrdinaryPullback g d :=
  Functor.leftDerivedUnique (completedOrdinaryPullback g d) L ε
    (completedOrdinaryPullbackCounit g d)
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))
end Ordinary

section Tower
variable (L : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
  (ε : DerivedCategory.Qh ⋙ L ⟶
    (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [L.IsLeftDerivedFunctor ε
    (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))]

/-- The universal counit fixes the comparison to the published strict-tower pair.
Source: blueprint CBC argument, Step 3; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-models). -/
def adicPresentationTowerIso : L ≅ completedTowerPullback g d :=
  Functor.leftDerivedUnique (completedTowerPullback g d) L ε
    (completedTowerPullbackCounit g d)
    (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))
end Tower


section NormalizedPair
variable
  (L : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
  (ε : DerivedCategory.Qh ⋙ L ⟶
    (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [hL : L.IsLeftDerivedFunctor ε
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))]
  (T : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
  (τ : DerivedCategory.Qh ⋙ T ⟶
    (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [hT : T.IsLeftDerivedFunctor τ
    (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))]

/-- Constant-tower comparison for any universal pair, transported through the unique
counit-preserving identifications with the published pairs. Source: CBC Step 4; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-models). -/
def adicPresentationConstantIso :
    L ⋙ completedDerivedConstant d X ≅ completedDerivedConstant d Y ⋙ T :=
  Functor.isoWhiskerRight (adicPresentationOrdinaryIso g d L ε)
      (completedDerivedConstant d X) ≪≫
    completedPullbackConstantIso g d ≪≫
    Functor.isoWhiskerLeft (completedDerivedConstant d Y)
      (adicPresentationTowerIso g d T τ).symm

/-- The generalized representative normalization retains both universal counits.
Source: CBC Step 4; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-models). -/
def HasAdicPresentationConstantNormalization
    (b : L ⋙ completedDerivedConstant d X ≅ completedDerivedConstant d Y ⋙ T) : Prop :=
  Functor.HasRepresentativeNormalization L T
    (completedDerivedConstant d X) (completedDerivedConstant d Y)
    (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion Y d) P)
    (fun P ↦ DerivedCategory.Q.obj P)
    (fun P ↦ DerivedCategory.Q.obj
      (((completedTowerConstant d Y).mapHomologicalComplex (.up ℤ)).obj P))
    (fun P ↦ DerivedCategory.Q.obj
      (((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P))
    (fun P ↦ DerivedCategory.Q.obj
      (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
        (((completedTowerConstant d Y).mapHomologicalComplex (.up ℤ)).obj P)))
    (fun P ↦ Functor.leftDerivedCounitOnComplex (completedModulePullback g d) L ε P)
    (fun P ↦ Functor.leftDerivedCounitOnComplex (completedTowerModulePullback g d) T τ
      (((completedTowerConstant d Y).mapHomologicalComplex (.up ℤ)).obj P))
    (fun P ↦ ((completedTowerConstant d Y).mapDerivedCategoryFactors).hom.app P)
    (fun P ↦ ((completedTowerConstant d X).mapDerivedCategoryFactors).hom.app
      (((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (eqToHom (completedPullbackConstantComplex_eq g d P))) b

omit hL hT in
private theorem constantProofAux
    (s : L ≅ completedOrdinaryPullback g d)
    (t : T ≅ completedTowerPullback g d)
    (hs : Functor.whiskerLeft DerivedCategory.Qh s.hom ≫
      completedOrdinaryPullbackCounit g d = ε)
    (ht : Functor.whiskerLeft DerivedCategory.Qh t.hom ≫
      completedTowerPullbackCounit g d = τ)
    (c : completedOrdinaryPullback g d ⋙ completedDerivedConstant d X ≅
      completedDerivedConstant d Y ⋙ completedTowerPullback g d)
    (hc : HasCompletedPullbackConstantNormalization g d c)
    (hu : ∀ b, HasCompletedPullbackConstantNormalization g d b → b = c) :
    HasAdicPresentationConstantNormalization g d L ε T τ
      (Functor.isoWhiskerRight s (completedDerivedConstant d X) ≪≫
        c ≪≫
        Functor.isoWhiskerLeft (completedDerivedConstant d Y) t.symm) ∧
    ∀ b : L ⋙ completedDerivedConstant d X ≅ completedDerivedConstant d Y ⋙ T,
      HasAdicPresentationConstantNormalization g d L ε T τ b →
        b = Functor.isoWhiskerRight s (completedDerivedConstant d X) ≪≫
          c ≪≫
          Functor.isoWhiskerLeft (completedDerivedConstant d Y) t.symm := by
  have transport (b : L ⋙ completedDerivedConstant d X ≅
      completedDerivedConstant d Y ⋙ T) :
      HasAdicPresentationConstantNormalization g d L ε T τ b ↔
        HasCompletedPullbackConstantNormalization g d
          (Functor.isoWhiskerRight s.symm (completedDerivedConstant d X) ≪≫ b ≪≫
            Functor.isoWhiskerLeft (completedDerivedConstant d Y) t) := by
    exact normalizationTransportCounits (completedModulePullback g d)
      (completedTowerModulePullback g d)
      (completedDerivedConstant d X) (completedDerivedConstant d Y)
      ((completedTowerConstant d Y).mapHomologicalComplex (.up ℤ))
      L (completedOrdinaryPullback g d) T (completedTowerPullback g d)
      ε (completedOrdinaryPullbackCounit g d) τ (completedTowerPullbackCounit g d)
      s t hs ht
      (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients
        (R := pbcAdicCompletion Y d) P)
      (fun P ↦ ((completedTowerConstant d Y).mapDerivedCategoryFactors).hom.app P)
      (fun P ↦ ((completedTowerConstant d X).mapDerivedCategoryFactors).hom.app
        (((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (eqToHom (completedPullbackConstantComplex_eq g d P))) b
  exact isoConjugate_unique
    (Functor.isoWhiskerRight s (completedDerivedConstant d X))
    (Functor.isoWhiskerLeft (completedDerivedConstant d Y) t)
    (HasAdicPresentationConstantNormalization g d L ε T τ)
    (HasCompletedPullbackConstantNormalization g d) transport c hc hu


/-- The transported constant comparison is the unique counit-normalized one.
Source: CBC Step 4; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-models).
Proof: substitute the two counit-preserving universal comparisons in the published
constant comparison's normalization. This gives the displayed representative equation.
Both counits are invertible on constant K-flat representatives. Diagram resolutions of
arrows give naturality; resolving roofs and then inverting quasi-isomorphisms gives
uniqueness on the derived category. -/
theorem adicPresentationConstantIso_normalized :
    HasAdicPresentationConstantNormalization g d L ε T τ
      (adicPresentationConstantIso g d L ε T τ) ∧
    ∀ b : L ⋙ completedDerivedConstant d X ≅ completedDerivedConstant d Y ⋙ T,
      HasAdicPresentationConstantNormalization g d L ε T τ b →
        b = adicPresentationConstantIso g d L ε T τ := by
  exact constantProofAux g d L ε T τ
    (adicPresentationOrdinaryIso g d L ε) (adicPresentationTowerIso g d T τ)
    (by simp [adicPresentationOrdinaryIso]) (by simp [adicPresentationTowerIso])
    (completedPullbackConstantIso g d)
    (completedPullbackConstantIso_exists g d).exists.choose_spec
    (fun b hb ↦ (completedPullbackConstantIso_exists g d).unique hb
      (completedPullbackConstantIso_exists g d).exists.choose_spec)

/-- Evaluation and levelwise pullback give the identical complex.
Source: CBC Step 4; Stacks 015F
(blueprint: lem-cbc-adic-pullback-presentation-models).
Proof: in every complex degree both sides are the pullback of the same tower level,
with the same pulled differential. Componentwise extensionality gives the equality. -/
theorem adicPresentationEvaluationComplex_eq (n : ℕ)
    (P : CochainComplex (pbcTowers Y (pbcAdicCompletion Y d)) ℤ) :
    (((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
      (op n)).mapHomologicalComplex (.up ℤ)).obj
        (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) =
    ((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
      ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
        (op n)).mapHomologicalComplex (.up ℤ)).obj P) := by
  rfl

/-- Evaluation comparison normalized by the actual counits on strict K-flat diagrams.
Source: CBC Step 4; Stacks 05S7 and 015F
(blueprint: lem-cbc-adic-pullback-presentation-models). -/
def HasAdicPresentationEvaluationNormalization (n : ℕ)
    (v : T ⋙ pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      pbcTowerEvaluation Y (pbcAdicCompletion Y d) n ⋙ L) : Prop :=
  Functor.HasRepresentativeNormalization T L
    (pbcTowerEvaluation X (pbcAdicCompletion X d) n)
    (pbcTowerEvaluation Y (pbcAdicCompletion Y d) n)
    (fun P ↦ ∀ k : ℕ, CochainComplex.IsKFlatIndependentCoefficients
      (R := pbcAdicCompletion Y d) (P.asFunctor.obj (op k)))
    (fun P ↦ DerivedCategory.Q.obj P)
    (fun P ↦ DerivedCategory.Q.obj
      ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
        (op n)).mapHomologicalComplex (.up ℤ)).obj P))
    (fun P ↦ DerivedCategory.Q.obj
      (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P))
    (fun P ↦ DerivedCategory.Q.obj
      (((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
        ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
          (op n)).mapHomologicalComplex (.up ℤ)).obj P)))
    (fun P ↦ Functor.leftDerivedCounitOnComplex (completedTowerModulePullback g d) T τ P)
    (fun P ↦ Functor.leftDerivedCounitOnComplex (completedModulePullback g d) L ε
      ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
        (op n)).mapHomologicalComplex (.up ℤ)).obj P))
    (fun P ↦ ((CategoryTheory.evaluation ℕᵒᵖ
      (pbcModules Y (pbcAdicCompletion Y d))).obj (op n)).mapDerivedCategoryFactors.hom.app P)
    (fun P ↦ ((CategoryTheory.evaluation ℕᵒᵖ
      (pbcModules X (pbcAdicCompletion X d))).obj (op n)).mapDerivedCategoryFactors.hom.app
        (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (eqToHom (adicPresentationEvaluationComplex_eq g d n P))) v

include hL hT in
/-- Evaluation commutes with arbitrary universal pullback pairs in one normalized way.
Source: CBC Step 4; Stacks 05S7 and 015F
(blueprint: lem-cbc-adic-pullback-presentation-models).
Proof: evaluate a strict objectwise K-flat resolution. Exact evaluation and both
counits identify the two sides with the identical evaluated pullback complex. Resolve
arrows simultaneously to get naturality, then descend roofs through localization.
The invertible representative counits force uniqueness and invertibility. -/
theorem adicPresentationEvaluationIso_exists (n : ℕ) :
    ∃! v : T ⋙ pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      pbcTowerEvaluation Y (pbcAdicCompletion Y d) n ⋙ L,
      HasAdicPresentationEvaluationNormalization g d L ε T τ n v := by
  classical
  let MY := pbcModules Y (pbcAdicCompletion Y d)
  let MX := pbcModules X (pbcAdicCompletion X d)
  let EY := (CategoryTheory.evaluation ℕᵒᵖ MY).obj (op n)
  let EX := (CategoryTheory.evaluation ℕᵒᵖ MX).obj (op n)
  let F := completedModulePullback g d
  let FT := completedTowerModulePullback g d
  let good : ObjectProperty (CochainComplex (ℕᵒᵖ ⥤ MY) ℤ) := fun P ↦
    ∀ k : ℕ, CochainComplex.IsKFlatIndependentCoefficients
      (R := pbcAdicCompletion Y d) (P.asFunctor.obj (op k))
  have res (K : CochainComplex (ℕᵒᵖ ⥤ MY) ℤ) :
      ∃ (P : CochainComplex (ℕᵒᵖ ⥤ MY) ℤ) (p : P ⟶ K), good P ∧ QuasiIso p := by
    obtain ⟨P, p, hp, hP⟩ := CochainComplex.diagramResolution
      (ProEt.topology Y) (pbcAdicCompletion Y d) K
    exact ⟨P, p, fun k ↦ hP (op k), hp⟩
  let e := evaluationComplexIso F n
  exact evaluationNormalization_of_canonical F FT L ε T τ
    (completedOrdinaryPullback g d) (completedOrdinaryPullbackCounit g d)
    (completedTowerPullback g d) (completedTowerPullbackCounit g d)
    (adicPresentationOrdinaryIso g d L ε) (adicPresentationTowerIso g d T τ)
    (by simp [adicPresentationOrdinaryIso]) (by simp [adicPresentationTowerIso])
    n e good res (fun P hP ↦ (canonicalOrdinaryPair g d).2 _ (hP n))
    (fun P hP ↦ (canonicalTowerPair g d).2.2 P hP)

/-- The unique evaluation comparison, including all maps of strict diagrams.
Source: CBC Step 4; Stacks 015F
(blueprint: lem-cbc-adic-pullback-presentation-models). -/
def adicPresentationEvaluationIso (n : ℕ) :
    T ⋙ pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      pbcTowerEvaluation Y (pbcAdicCompletion Y d) n ⋙ L :=
  (adicPresentationEvaluationIso_exists g d L ε T τ n).exists.choose

/-- Finite-reduction comparison for any universal tower pair. The published comparison
is uniquely fixed by its tensor generators and actual resolving counits, rather than
chosen from the earlier bare Nonempty interface. Source: CBC Step 5; Stacks 099L
(blueprint: lem-cbc-adic-pullback-presentation-models). -/
def adicPresentationFiniteIso (n : ℕ) :
    completedReductionTower Y d ⋙ T ⋙ pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      completedReductionFiniteTarget g d n ⋙
        pbcDerivedRestrict (completedReductionProjection X d n) :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (completedReductionTower Y d)
        (adicPresentationTowerIso g d T τ))
      (pbcTowerEvaluation X (pbcAdicCompletion X d) n) ≪≫
    completedReductionFiniteEvaluation g d n
end NormalizedPair


end AlgebraicGeometry.Scheme
