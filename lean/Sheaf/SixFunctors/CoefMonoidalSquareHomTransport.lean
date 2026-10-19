module


public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Transport of closed monoidal comparisons through a monoidal square

Source: literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/
`thm-coef-finite-hom.md`, proof final sentence
(blueprint: lem-coef-monoidal-square-hom-transport).
-/

@[expose] public section

universe uCA vCA uCB vCB uDA vDA uDB vDB
universe uCC vCC uDC vDC

open CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace CategoryTheory

/-- The internal-Hom comparison obtained by transposing the image of evaluation along
`V`'s tensorator (blueprint: lem-coef-monoidal-square-hom-transport).
This is the map denoted `v_V` in the source statement.
Source: literature/blueprint/master/blueprint/sec-six-functors/
sk-prop-sf-biduality-general/thm-coef-finite-hom.md, proof final sentence. -/
noncomputable def internalHomComparison
    {C : Type uCA} [Category.{vCA} C] [MonoidalCategory C]
    {D : Type uCB} [Category.{vCB} D] [MonoidalCategory D]
    [MonoidalClosed C] [MonoidalClosed D]
    (V : C ⥤ D) [V.Monoidal] (K M : C) :
    V.obj (K ⟶[C] M) ⟶ (V.obj K ⟶[D] V.obj M) :=
  MonoidalClosed.curry (Functor.LaxMonoidal.μ V K (K ⟶[C] M) ≫
    V.map ((ihom.ev K).app M))

/-- The endpoint transport induced by a natural isomorphism of functors.
Source: literature/blueprint/master/blueprint/sec-six-functors/
sk-prop-sf-biduality-general/thm-coef-finite-hom.md, proof final sentence
(blueprint: lem-coef-monoidal-square-hom-transport). -/
noncomputable def internalHomTransport
    {C : Type uCA} [Category.{vCA} C] [MonoidalCategory C]
    {D : Type uCB} [Category.{vCB} D] [MonoidalCategory D]
    [MonoidalClosed C] [MonoidalClosed D]
    {V W : C ⥤ D} (e : V ≅ W) (K M : C) :
    (V.obj K ⟶[D] V.obj M) ⟶ (W.obj K ⟶[D] W.obj M) :=
  (MonoidalClosed.pre (e.inv.app K)).app (V.obj M) ≫
    (ihom (W.obj K)).map (e.hom.app M)

/-- The naturality, evaluation, transpose, and internal-Hom composition laws for the
comparison `v_V` (blueprint: lem-coef-monoidal-square-hom-transport).
The equations use Mathlib's canonical closed structure and monoidal tensorator.
This predicate does not include successive coefficient change; that law is stated
separately by `SuccessiveCoefficientHomTransport`.
Source: literature/blueprint/master/blueprint/sec-six-functors/
sk-prop-sf-biduality-general/thm-coef-finite-hom.md, proof final sentence. -/
def InternalHomComparisonLaws
    {C : Type uCA} [Category.{vCA} C] [MonoidalCategory C]
    {D : Type uCB} [Category.{vCB} D] [MonoidalCategory D]
    [MonoidalClosed C] [MonoidalClosed D]
    (V : C ⥤ D) [V.Monoidal] : Prop :=
  (∀ {K K' M M' : C} (a : K' ⟶ K) (b : M ⟶ M'),
    V.map ((MonoidalClosed.pre a).app M ≫ (ihom K').map b) ≫
        internalHomComparison V K' M' =
      internalHomComparison V K M ≫
        (MonoidalClosed.pre (V.map a)).app (V.obj M) ≫
        (ihom (V.obj K')).map (V.map b)) ∧
  (∀ (K M : C),
    MonoidalClosed.uncurry (internalHomComparison V K M) =
      Functor.LaxMonoidal.μ V K (K ⟶[C] M) ≫ V.map ((ihom.ev K).app M)) ∧
  (∀ {T K M : C} (t : T ⟶ (K ⟶[C] M)),
    V.map t ≫ internalHomComparison V K M =
      MonoidalClosed.curry (Functor.LaxMonoidal.μ V K T ≫ V.map
        (MonoidalClosed.uncurry t))) ∧
  (∀ (K L M : C),
    V.map (MonoidalClosed.comp K L M) ≫ internalHomComparison V K M =
      Functor.OplaxMonoidal.δ V (K ⟶[C] L) (L ⟶[C] M) ≫
        (internalHomComparison V K L ⊗ₘ internalHomComparison V L M) ≫
        MonoidalClosed.comp (V.obj K) (V.obj L) (V.obj M))

/-- The four comparison laws with a specified pair as an endpoint.
Source: literature/blueprint/master/blueprint/sec-six-functors/
sk-prop-sf-biduality-general/thm-coef-finite-hom.md, proof final sentence
(blueprint: lem-coef-monoidal-square-hom-transport). -/
def InternalHomComparisonLawsAt
    {C : Type uCA} [Category.{vCA} C] [MonoidalCategory C]
    {D : Type uCB} [Category.{vCB} D] [MonoidalCategory D]
    [MonoidalClosed C] [MonoidalClosed D]
    (V : C ⥤ D) [V.Monoidal] (K M : C) : Prop :=
  (∀ {K' M' : C} (a : K' ⟶ K) (b : M ⟶ M'),
    V.map ((MonoidalClosed.pre a).app M ≫ (ihom K').map b) ≫
        internalHomComparison V K' M' =
      internalHomComparison V K M ≫
        (MonoidalClosed.pre (V.map a)).app (V.obj M) ≫
        (ihom (V.obj K')).map (V.map b)) ∧
  (MonoidalClosed.uncurry (internalHomComparison V K M) =
      Functor.LaxMonoidal.μ V K (K ⟶[C] M) ≫ V.map ((ihom.ev K).app M)) ∧
  (∀ {T : C} (t : T ⟶ (K ⟶[C] M)),
    V.map t ≫ internalHomComparison V K M =
      MonoidalClosed.curry (Functor.LaxMonoidal.μ V K T ≫ V.map
        (MonoidalClosed.uncurry t))) ∧
  (∀ (L : C),
    V.map (MonoidalClosed.comp K L M) ≫ internalHomComparison V K M =
      Functor.OplaxMonoidal.δ V (K ⟶[C] L) (L ⟶[C] M) ≫
        (internalHomComparison V K L ⊗ₘ internalHomComparison V L M) ≫
        MonoidalClosed.comp (V.obj K) (V.obj L) (V.obj M))

/-- Coherent successive coefficient change, including endpoint transports.
The composite identifications `fComp` and `gComp` are monoidal, as the node specifies
("specified monoidal composite identifications"); the assumed composition equation for
`v_F` is the hypothesis `_hFComp`.
Source: literature/blueprint/master/blueprint/sec-six-functors/
sk-prop-sf-biduality-general/thm-coef-finite-hom.md, proof final sentence
(blueprint: lem-coef-monoidal-square-hom-transport). -/
def SuccessiveCoefficientHomTransport
    {CA : Type uCA} [Category.{vCA} CA] [MonoidalCategory CA]
    [BraidedCategory CA]
    {CB : Type uCB} [Category.{vCB} CB] [MonoidalCategory CB]
    [BraidedCategory CB]
    {DA : Type uDA} [Category.{vDA} DA] [MonoidalCategory DA]
    [BraidedCategory DA]
    {DB : Type uDB} [Category.{vDB} DB] [MonoidalCategory DB]
    [BraidedCategory DB]
    [MonoidalClosed CA] [MonoidalClosed CB] [MonoidalClosed DA]
    [MonoidalClosed DB]
    (F : CA ⥤ CB) (G : DA ⥤ DB) (UA : CA ⥤ DA) (UB : CB ⥤ DB)
    [F.Monoidal] [G.Monoidal] [UA.Monoidal] [UB.Monoidal]
    (hAB : F ⋙ UB ≅ UA ⋙ G) [NatTrans.IsMonoidal hAB.hom] : Prop :=
  ∀ {CC : Type uCC} [Category.{vCC} CC] [MonoidalCategory CC]
    [BraidedCategory CC] {DC : Type uDC} [Category.{vDC} DC]
    [MonoidalCategory DC] [BraidedCategory DC]
    [MonoidalClosed CC] [MonoidalClosed DC]
    (FBC : CB ⥤ CC) (FAC : CA ⥤ CC) (GBC : DB ⥤ DC) (GAC : DA ⥤ DC)
    (UC : CC ⥤ DC)
    [FBC.Braided] [FAC.Braided] [GBC.Braided] [GAC.Braided] [UC.Braided]
    (hBC : FBC ⋙ UC ≅ UB ⋙ GBC) [NatTrans.IsMonoidal hBC.hom]
    (hAC : FAC ⋙ UC ≅ UA ⋙ GAC) [NatTrans.IsMonoidal hAC.hom]
    (fComp : FAC ≅ F ⋙ FBC) [NatTrans.IsMonoidal fComp.hom]
    (gComp : GAC ≅ G ⋙ GBC) [NatTrans.IsMonoidal gComp.hom]
    (_hCoherent : ∀ (X : CA),
      UC.map (fComp.hom.app X) ≫ hBC.hom.app (F.obj X) ≫
          GBC.map (hAB.hom.app X) ≫ gComp.inv.app (UA.obj X) =
        hAC.hom.app X),
    ∀ {K M : CA}
      [IsIso (internalHomComparison UA K M)]
      [IsIso (internalHomComparison UB (F.obj K) (F.obj M))]
      [IsIso (internalHomComparison UC (FAC.obj K) (FAC.obj M))],
      InternalHomComparisonLaws F →
      InternalHomComparisonLaws FBC →
      InternalHomComparisonLaws FAC →
      (_hFComp : internalHomComparison FAC K M ≫ internalHomTransport fComp K M =
        fComp.hom.app (K ⟶[CA] M) ≫ FBC.map (internalHomComparison F K M) ≫
          internalHomComparison FBC (F.obj K) (F.obj M)) →
      (GAC.map (internalHomComparison UA K M) ≫
          internalHomComparison GAC (UA.obj K) (UA.obj M) ≫
          internalHomTransport gComp (UA.obj K) (UA.obj M) =
        gComp.hom.app (UA.obj (K ⟶[CA] M)) ≫
          GBC.map (G.map (internalHomComparison UA K M)) ≫
          GBC.map (internalHomComparison G (UA.obj K) (UA.obj M)) ≫
          internalHomComparison GBC (G.obj (UA.obj K)) (G.obj (UA.obj M))) ∧
      (∀ (X Y : DA), internalHomComparison (𝟭 DA) X Y = 𝟙 _)

section ComparisonProofs

variable {C : Type uCA} [Category.{vCA} C] [MonoidalCategory C]
  {D : Type uCB} [Category.{vCB} D] [MonoidalCategory D]
  {E : Type uDA} [Category.{vDA} E] [MonoidalCategory E]
  [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosed E]

open Category Functor.LaxMonoidal

private lemma comparison_eq (V : C ⥤ D) [V.Monoidal] (K M : C) :
    internalHomComparison V K M = (ihomComparison V K).natTrans.app M :=
  (ihomComparison_app_eq_curry V K M).symm

private lemma comparison_comp (V : C ⥤ D) (W : D ⥤ E)
    [V.Monoidal] [W.Monoidal] (K M : C) :
    internalHomComparison (V ⋙ W) K M =
      W.map (internalHomComparison V K M) ≫
        internalHomComparison W (V.obj K) (V.obj M) := by
  simp only [comparison_eq, ihomComparison_comp_app]

private lemma comparison_iso {V W : C ⥤ D} [V.Monoidal] [W.Monoidal]
    (e : V ≅ W) [NatTrans.IsMonoidal e.hom] (K M : C) :
    e.hom.app (K ⟶[C] M) ≫ internalHomComparison W K M =
      internalHomComparison V K M ≫ internalHomTransport e K M := by
  have q := ihomComparison_app_comp_map_app e.inv K M
  have q' := congrArg (fun f ↦ e.hom.app (K ⟶[C] M) ≫ f ≫
    (ihom (W.obj K)).map (e.hom.app M)) q
  simp only [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id,
    Category.assoc, Iso.hom_inv_id_app_assoc, ← comparison_eq] at q'
  simpa [internalHomTransport] using q'


private lemma comparison_natural (V : C ⥤ D) [V.Monoidal]
    {K K' M M' : C} (a : K' ⟶ K) (b : M ⟶ M') :
    V.map ((pre a).app M ≫ (ihom K').map b) ≫ internalHomComparison V K' M' =
      internalHomComparison V K M ≫ (pre (V.map a)).app (V.obj M) ≫
        (ihom (V.obj K')).map (V.map b) := by
  simp only [comparison_eq, V.map_comp, Category.assoc]
  have q := (ihomComparison V K').natTrans.naturality b
  simp only [Functor.comp_map] at q
  rw [q]
  simp only [← Category.assoc]
  rw [map_pre_app_comp_ihomComparison_app]

private lemma comparison_transpose (V : C ⥤ D) [V.Monoidal]
    {T K M : C} (t : T ⟶ (K ⟶[C] M)) :
    V.map t ≫ internalHomComparison V K M =
      curry (μ V K T ≫ V.map (uncurry t)) := by
  rw [internalHomComparison, ← curry_natural_left, uncurry_eq,
    V.map_comp, ← μ_natural_right_assoc]

private lemma comparison_evaluation (V : C ⥤ D) [V.Monoidal] (K M : C) :
    V.obj K ◁ internalHomComparison V K M ≫ (ihom.ev (V.obj K)).app (V.obj M) =
      μ V K (K ⟶[C] M) ≫ V.map ((ihom.ev K).app M) := by
  rw [internalHomComparison, whiskerLeft_curry_ihom_ev_app]

private lemma comparison_composition (V : C ⥤ D) [V.Monoidal] (K L M : C) :
    V.map (MonoidalClosed.comp K L M) ≫ internalHomComparison V K M =
      Functor.OplaxMonoidal.δ V (K ⟶[C] L) (L ⟶[C] M) ≫
        (internalHomComparison V K L ⊗ₘ internalHomComparison V L M) ≫
        MonoidalClosed.comp (V.obj K) (V.obj L) (V.obj M) := by
  rw [← cancel_epi (μ V (K ⟶[C] L) (L ⟶[C] M))]
  simp only [Functor.Monoidal.μ_δ_assoc]
  rw [comparison_transpose]
  apply uncurry_injective
  rw [← curry_natural_left, uncurry_curry, uncurry_natural_left,
    MonoidalClosed.comp_eq, uncurry_curry]
  simp only [MonoidalClosed.comp_eq, uncurry_curry, compTranspose, V.map_comp]
  rw [associativity_inv_assoc, ← μ_natural_left_assoc]
  conv_rhs =>
    simp only [tensorHom_def', whiskerLeft_comp, Category.assoc,
      associator_inv_naturality_middle_assoc, associator_inv_naturality_right_assoc]
    rw [← comp_whiskerRight_assoc, whisker_exchange_assoc]
    simp only [comparison_evaluation, comp_whiskerRight, Category.assoc]
  dsimp only [Functor.id_obj]
  rw [comparison_evaluation V L M]

end ComparisonProofs

/-- Transport of evaluation-defined internal-Hom comparisons through a coherent strong
symmetric-monoidal square (blueprint: lem-coef-monoidal-square-hom-transport).

Source: literature/blueprint/master/blueprint/sec-six-functors/
sk-prop-sf-biduality-general/thm-coef-finite-hom.md, proof final sentence.
The postponed proof follows these eleven steps, using Mathlib's closed uncurry laws
and the monoidal-category axioms:
(1) Fix the tensorator convention and the evaluation transpose equation (E).
(2) Define the endpoint map `internalHomTransport h K M` and verify its evaluation
    characterization using `h.inv` and `h.hom`.
(3) Evaluate the left side of the square identity after tensoring by `h.app K`.
(4) Evaluate the right side using the endpoint characterization, then use naturality
    and monoidality of `h`; uniqueness of transpose proves the square identity (S).
(5) Under the two `IsIso` guards, cancel `G.map β_A` and `h_H` to obtain conjugation;
    invertibility of `v_F` is used only when invertibility of `v_G` is requested.
(6) Evaluate both sides of the two-variable naturality law and use transpose uniqueness.
(7) For `t : T ⟶ H(K,M)`, evaluate `v_V ≫ V.map t` to prove transpose and evaluation
    compatibility and transport it through (S).
(8) Evaluate the internal-Hom composition law by two successive evaluations and use
    monoidal associativity to identify the three-factor tensorators.
(9) Check that `internalHomTransport h` preserves those successive evaluation pairings;
    substitute (S) to transport the composition law.
(10) For successive functors, evaluate `v_W ≫ W.map v_V` and identify it with `v_(W⋙V)`;
     the identity tensorator gives the identity case.
(11) Apply (10) to the coherent triangle recorded by `SuccessiveCoefficientHomTransport`:
     the composite functor isomorphisms and square coherence supply the endpoint transports,
     cancellation of the middle comparison gives
     `v_{G_AC} = v_{G_BC} ≫ G_BC(v_{G_AB})`, together with the identity equation. -/
theorem coefMonoidalSquareHomTransport
    {CA : Type uCA} [Category.{vCA} CA] [MonoidalCategory CA] [BraidedCategory CA]
    {CB : Type uCB} [Category.{vCB} CB] [MonoidalCategory CB] [BraidedCategory CB]
    {DA : Type uDA} [Category.{vDA} DA] [MonoidalCategory DA] [BraidedCategory DA]
    {DB : Type uDB} [Category.{vDB} DB] [MonoidalCategory DB] [BraidedCategory DB]
    [MonoidalClosed CA] [MonoidalClosed CB] [MonoidalClosed DA] [MonoidalClosed DB]
    (F : CA ⥤ CB) (G : DA ⥤ DB) (UA : CA ⥤ DA) (UB : CB ⥤ DB)
    [F.Braided] [G.Braided] [UA.Braided] [UB.Braided]
    (h : F ⋙ UB ≅ UA ⋙ G) [NatTrans.IsMonoidal h.hom]
    (K M : CA) :
    h.hom.app (K ⟶[CA] M) ≫
          G.map (internalHomComparison UA K M) ≫
          internalHomComparison G (UA.obj K) (UA.obj M) =
        UB.map (internalHomComparison F K M) ≫
          internalHomComparison UB (F.obj K) (F.obj M) ≫
          internalHomTransport h K M ∧
    (∀ [IsIso (internalHomComparison UA K M)]
      [IsIso (internalHomComparison UB (F.obj K) (F.obj M))],
      internalHomComparison G (UA.obj K) (UA.obj M) =
        G.map (inv (internalHomComparison UA K M)) ≫
          h.inv.app (K ⟶[CA] M) ≫
          UB.map (internalHomComparison F K M) ≫
          internalHomComparison UB (F.obj K) (F.obj M) ≫
          internalHomTransport h K M) ∧
    (∀ {K M : CA}
      [IsIso (internalHomComparison UA K M)]
      [IsIso (internalHomComparison UB (F.obj K) (F.obj M))],
      InternalHomComparisonLawsAt F K M →
      InternalHomComparisonLawsAt G (UA.obj K) (UA.obj M)) ∧
    SuccessiveCoefficientHomTransport F G UA UB h := by
  have square : h.hom.app (K ⟶[CA] M) ≫
      G.map (internalHomComparison UA K M) ≫
      internalHomComparison G (UA.obj K) (UA.obj M) =
      UB.map (internalHomComparison F K M) ≫
      internalHomComparison UB (F.obj K) (F.obj M) ≫ internalHomTransport h K M := by
    simpa only [comparison_comp, Category.assoc] using comparison_iso h K M
  refine ⟨square, ?_, ?_, ?_⟩
  · intro _ _
    rw [← square]
    simp only [← G.map_comp_assoc, Iso.inv_hom_id_app_assoc,
      IsIso.inv_hom_id, G.map_id, Category.id_comp]
  · intro K M _ _ _
    exact ⟨comparison_natural G, uncurry_curry _, comparison_transpose G,
      fun L ↦ comparison_composition G (UA.obj K) L (UA.obj M)⟩
  · intro CC _ _ _ DC _ _ _ _ _ FBC FAC GBC GAC UC _ _ _ _ _ hBC _ hAC _
      fComp _ gComp _ hCoherent K M _ _ _ hF hFBC hFAC hFComp
    constructor
    · have q := comparison_iso gComp (UA.obj K) (UA.obj M)
      rw [comparison_comp] at q
      rw [← q, ← Category.assoc, gComp.hom.naturality]
      simp only [Functor.comp_map, Category.assoc]
    · intro X Y
      apply uncurry_injective
      change uncurry (curry (𝟙 _ ≫ (ihom.ev X).app Y)) = uncurry (𝟙 _)
      rw [uncurry_curry, Category.id_comp, uncurry_id_eq_ev]

end CategoryTheory
