/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AbsoluteTraceExchangeData

/-! # Absolute trace exchange under scalar comparison

Source: blueprint latest, sec-six-functors/sk-thm-sf-package/
lem-coef-finite-exceptional.proof.md, paragraph 2, preservation of evaluation,
projection and adjunction counits under coefficient comparison.
(blueprint: lem-sf-absolute-trace-scalar-exchange)

The tensorators in the projection and evaluation squares make explicit the
statement's convention "after the monoidal identifications". The canonical trace
and exchange arrows are those of `WeilConjectures.CategoryTheory.AbsoluteTraceExchangeData`.
-/

@[expose] public section

set_option autoImplicit false

universe uX0 uY0 uS0 uX1 uY1 uS1 vX0 vY0 vS0 vX1 vY1 vS1

open CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {X0 : Type uX0} {Y0 : Type uY0} {S0 : Type uS0}
  {X1 : Type uX1} {Y1 : Type uY1} {S1 : Type uS1}
  [Category.{vX0} X0] [Category.{vY0} Y0] [Category.{vS0} S0]
  [Category.{vX1} X1] [Category.{vY1} Y1] [Category.{vS1} S1]
  [MonoidalCategory X0] [SymmetricCategory X0]
  [MonoidalCategory Y0] [SymmetricCategory Y0]
  [MonoidalCategory X1] [SymmetricCategory X1]
  [MonoidalCategory Y1] [SymmetricCategory Y1]

/-- Scalar comparison preserves the canonical relative trace and its exchange arrow.
Source: blueprint latest, lem-coef-finite-exceptional.proof.md, paragraph 2;
agent-explicit categorical trace and exchange squares.
(blueprint: lem-sf-absolute-trace-scalar-exchange)

Proof (the seven DAG steps):
1. The inverse transpose for PY1 ⊣ AY1 is h ↦ PY1(h) ≫ trY1, hence injective
   (lem-weil-pbc-adjunction-of-natural-bijection). The definition of each trace
   gives PY(τ) ≫ trY = κ ≫ trX.
2. Apply this inverse transpose to both proposed relative traces, precomposing
   by aY at F0(ωX0). Naturality of κ1, the κ scalar square and the X absolute
   trace square give Qs(κ0 ≫ trX0) ≫ v on the first side. Naturality of aY and
   the Y absolute trace square give the same composite on the second side.
   Cancel aY and use injectivity to prove the first conclusion.
3. Put K = DX0(M), J = R0(K), and r = c_K ≫ R1(dX_M). Write b = σ ≫ evX
   and z = σ ≫ θ ≫ F(1 ⊗ ε); the defining pairing is z ≫ F(b) ≫ τ.
   Tensorator naturality and symmetry (def-sfb-strong-monoidal-functor and
   def-sfb-monoidal-category) commute scalar comparison past σ.
4. Naturality of θ1, symmetry and counit naturality at dX_M move r through z1.
   Substitute the counit square at N = K and projection square at W = J.
   Tensorator naturality at (1, ε0) and naturality of q then give
   (r ⊗ q_M) ≫ z1 = μY ≫ QY(z0) ≫ q ≫ F1(μX⁻¹) ≫ F1(1 ⊗ dX_M).
5. The X evaluation square, symmetry and tensorator naturality commute b with
   dX. Naturality of q and the trace equality from step 2 identify the pairings:
   (r ⊗ q_M) ≫ λ1 = μY ≫ QY(λ0) ≫ uY.
6. Evaluate QY(E0) ≫ dY using the Y evaluation square and tensorator naturality.
   Evaluate r ≫ E1 ≫ DY1(q_M) using evaluation naturality in its second variable.
   The defining transpose equations for E0 and E1 reduce these evaluations to
   the two pairings in step 5.
7. The representing Y1 evaluation bijection is injective, so the exchange maps
   agree. No relative exceptional adjoint of F or biduality is used.
-/
theorem absoluteTraceScalarExchange
    {PX0 : X0 ⥤ S0} {AX0 : S0 ⥤ X0} {PY0 : Y0 ⥤ S0} {AY0 : S0 ⥤ Y0}
    {PX1 : X1 ⥤ S1} {AX1 : S1 ⥤ X1} {PY1 : Y1 ⥤ S1} {AY1 : S1 ⥤ Y1}
    (adjX0 : PX0 ⊣ AX0) (adjY0 : PY0 ⊣ AY0) (Ω0 : S0)
    (adjX1 : PX1 ⊣ AX1) (adjY1 : PY1 ⊣ AY1) (Ω1 : S1)
    {F0 : X0 ⥤ Y0} {U0 : Y0 ⥤ X0} {R0 : X0 ⥤ Y0} (adj0 : U0 ⊣ R0)
    {F1 : X1 ⥤ Y1} {U1 : Y1 ⥤ X1} {R1 : X1 ⥤ Y1} (adj1 : U1 ⊣ R1)
    (κ0 : F0 ⋙ PY0 ≅ PX0) (κ1 : F1 ⋙ PY1 ≅ PX1)
    (θ0 : ∀ (M : X0) (W : Y0), F0.obj M ⊗ W ≅ F0.obj (M ⊗ U0.obj W))
    (θ1 : ∀ (M : X1) (W : Y1), F1.obj M ⊗ W ≅ F1.obj (M ⊗ U1.obj W))
    (DX0 : X0ᵒᵖ ⥤ X0) (DY0 : Y0ᵒᵖ ⥤ Y0)
    (DX1 : X1ᵒᵖ ⥤ X1) (DY1 : Y1ᵒᵖ ⥤ Y1)
    (evX0 : ∀ M : X0, DX0.obj (op M) ⊗ M ⟶ AX0.obj Ω0)
    (evY0 : ∀ M : Y0, DY0.obj (op M) ⊗ M ⟶ AY0.obj Ω0)
    (evX1 : ∀ M : X1, DX1.obj (op M) ⊗ M ⟶ AX1.obj Ω1)
    (evY1 : ∀ M : Y1, DY1.obj (op M) ⊗ M ⟶ AY1.obj Ω1)
    (eX0 : ∀ W M : X0, (W ⟶ DX0.obj (op M)) ≃ (W ⊗ M ⟶ AX0.obj Ω0))
    (eY0 : ∀ W M : Y0, (W ⟶ DY0.obj (op M)) ≃ (W ⊗ M ⟶ AY0.obj Ω0))
    (eX1 : ∀ W M : X1, (W ⟶ DX1.obj (op M)) ≃ (W ⊗ M ⟶ AX1.obj Ω1))
    (eY1 : ∀ W M : Y1, (W ⟶ DY1.obj (op M)) ≃ (W ⊗ M ⟶ AY1.obj Ω1))
    (hX0 : ∀ (W M : X0) (t : W ⟶ DX0.obj (op M)),
      eX0 W M t = (t ⊗ₘ 𝟙 M) ≫ evX0 M)
    (hY0 : ∀ (W M : Y0) (t : W ⟶ DY0.obj (op M)),
      eY0 W M t = (t ⊗ₘ 𝟙 M) ≫ evY0 M)
    (hX1 : ∀ (W M : X1) (t : W ⟶ DX1.obj (op M)),
      eX1 W M t = (t ⊗ₘ 𝟙 M) ≫ evX1 M)
    (hY1 : ∀ (W M : Y1) (t : W ⟶ DY1.obj (op M)),
      eY1 W M t = (t ⊗ₘ 𝟙 M) ≫ evY1 M)
    (hXM0 : ∀ (M' M : X0) (f : M' ⟶ M),
      (DX0.map f.op ⊗ₘ 𝟙 M') ≫ evX0 M' = (𝟙 (DX0.obj (op M)) ⊗ₘ f) ≫ evX0 M)
    (hYM0 : ∀ (M' M : Y0) (f : M' ⟶ M),
      (DY0.map f.op ⊗ₘ 𝟙 M') ≫ evY0 M' = (𝟙 (DY0.obj (op M)) ⊗ₘ f) ≫ evY0 M)
    (hXM1 : ∀ (M' M : X1) (f : M' ⟶ M),
      (DX1.map f.op ⊗ₘ 𝟙 M') ≫ evX1 M' = (𝟙 (DX1.obj (op M)) ⊗ₘ f) ≫ evX1 M)
    (hYM1 : ∀ (M' M : Y1) (f : M' ⟶ M),
      (DY1.map f.op ⊗ₘ 𝟙 M') ≫ evY1 M' = (𝟙 (DY1.obj (op M)) ⊗ₘ f) ≫ evY1 M)
    (hθW0 : ∀ (M : X0) (W W' : Y0) (f : W ⟶ W'),
      (𝟙 (F0.obj M) ⊗ₘ f) ≫ (θ0 M W').hom =
        (θ0 M W).hom ≫ F0.map (𝟙 M ⊗ₘ U0.map f))
    (hθM0 : ∀ (M M' : X0) (f : M ⟶ M') (W : Y0),
      (F0.map f ⊗ₘ 𝟙 W) ≫ (θ0 M' W).hom =
        (θ0 M W).hom ≫ F0.map (f ⊗ₘ 𝟙 (U0.obj W)))
    (hθW1 : ∀ (M : X1) (W W' : Y1) (f : W ⟶ W'),
      (𝟙 (F1.obj M) ⊗ₘ f) ≫ (θ1 M W').hom =
        (θ1 M W).hom ≫ F1.map (𝟙 M ⊗ₘ U1.map f))
    (hθM1 : ∀ (M M' : X1) (f : M ⟶ M') (W : Y1),
      (F1.map f ⊗ₘ 𝟙 W) ≫ (θ1 M' W).hom =
        (θ1 M W).hom ≫ F1.map (f ⊗ₘ 𝟙 (U1.obj W)))
    (QX : X0 ⥤ X1) [QX.Braided] (QY : Y0 ⥤ Y1) [QY.Braided]
    (Qs : S0 ⥤ S1) (v : Qs.obj Ω0 ≅ Ω1)
    (aX : PX0 ⋙ Qs ≅ QX ⋙ PX1) (aY : PY0 ⋙ Qs ≅ QY ⋙ PY1)
    (q : F0 ⋙ QY ≅ QX ⋙ F1) (p : U0 ⋙ QX ≅ QY ⋙ U1)
    (c : R0 ⋙ QY ≅ QX ⋙ R1)
    (uX : QX.obj (AX0.obj Ω0) ≅ AX1.obj Ω1)
    (uY : QY.obj (AY0.obj Ω0) ≅ AY1.obj Ω1)
    (dX : DX0 ⋙ QX ≅ QX.op ⋙ DX1) (dY : DY0 ⋙ QY ≅ QY.op ⋙ DY1)
    (htrX : aX.hom.app (AX0.obj Ω0) ≫ PX1.map uX.hom ≫ adjX1.counit.app Ω1 =
      Qs.map (adjX0.counit.app Ω0) ≫ v.hom)
    (htrY : aY.hom.app (AY0.obj Ω0) ≫ PY1.map uY.hom ≫ adjY1.counit.app Ω1 =
      Qs.map (adjY0.counit.app Ω0) ≫ v.hom)
    (hκ : ∀ M : X0,
      aY.hom.app (F0.obj M) ≫ PY1.map (q.hom.app M) ≫ κ1.hom.app (QX.obj M) =
        Qs.map (κ0.hom.app M) ≫ aX.hom.app M)
    (hε : ∀ N : X0,
      p.hom.app (R0.obj N) ≫ U1.map (c.hom.app N) ≫ adj1.counit.app (QX.obj N) =
        QX.map (adj0.counit.app N))
    (hθ : ∀ (M : X0) (W : Y0),
      (Functor.Monoidal.μIso QY (F0.obj M) W).hom ≫ QY.map (θ0 M W).hom ≫
        q.hom.app (M ⊗ U0.obj W) ≫
        F1.map (Functor.Monoidal.μIso QX M (U0.obj W)).inv ≫
        F1.map (𝟙 (QX.obj M) ⊗ₘ p.hom.app W) =
      (q.hom.app M ⊗ₘ 𝟙 (QY.obj W)) ≫ (θ1 (QX.obj M) (QY.obj W)).hom)
    (hevX : ∀ M : X0,
      (dX.hom.app (op M) ⊗ₘ 𝟙 (QX.obj M)) ≫ evX1 (QX.obj M) =
        (Functor.Monoidal.μIso QX (DX0.obj (op M)) M).hom ≫ QX.map (evX0 M) ≫ uX.hom)
    (hevY : ∀ M : Y0,
      (dY.hom.app (op M) ⊗ₘ 𝟙 (QY.obj M)) ≫ evY1 (QY.obj M) =
        (Functor.Monoidal.μIso QY (DY0.obj (op M)) M).hom ≫ QY.map (evY0 M) ≫ uY.hom) :
    (q.hom.app (AX0.obj Ω0) ≫ F1.map uX.hom ≫
        absoluteTraceExchangeTrace adjX1 adjY1 Ω1 κ1 =
      QY.map (absoluteTraceExchangeTrace adjX0 adjY0 Ω0 κ0) ≫ uY.hom) ∧
    (∀ M : X0,
      QY.map (absoluteTraceExchangeMap adjX0 adjY0 Ω0 adj0 κ0 θ0 DX0 DY0 evX0 eY0 M) ≫
          dY.hom.app (op (F0.obj M)) =
        c.hom.app (DX0.obj (op M)) ≫ R1.map (dX.hom.app (op M)) ≫
          absoluteTraceExchangeMap adjX1 adjY1 Ω1 adj1 κ1 θ1 DX1 DY1 evX1 eY1 (QX.obj M) ≫
          DY1.map (q.hom.app M).op) := by
  have _ := hX0
  have _ := hX1
  have _ := hXM0
  have _ := hYM0
  have _ := hXM1
  have _ := hθW0
  have _ := hθM0
  have _ := hθM1
  have htr0 : PY0.map (absoluteTraceExchangeTrace adjX0 adjY0 Ω0 κ0) ≫
      adjY0.counit.app Ω0 = κ0.hom.app (AX0.obj Ω0) ≫ adjX0.counit.app Ω0 := by
    exact (adjY0.homEquiv _ Ω0).symm_apply_apply _
  have htr1 : PY1.map (absoluteTraceExchangeTrace adjX1 adjY1 Ω1 κ1) ≫
      adjY1.counit.app Ω1 = κ1.hom.app (AX1.obj Ω1) ≫ adjX1.counit.app Ω1 := by
    exact (adjY1.homEquiv _ Ω1).symm_apply_apply _
  have htrace : q.hom.app (AX0.obj Ω0) ≫ F1.map uX.hom ≫
        absoluteTraceExchangeTrace adjX1 adjY1 Ω1 κ1 =
      QY.map (absoluteTraceExchangeTrace adjX0 adjY0 Ω0 κ0) ≫ uY.hom := by
    apply (adjY1.homEquiv (QY.obj (F0.obj (AX0.obj Ω0))) Ω1).symm.injective
    apply (cancel_epi (aY.hom.app (F0.obj (AX0.obj Ω0)))).1
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    simp only [Functor.comp_obj, Functor.map_comp, Category.assoc]
    have hn := aY.hom.naturality (absoluteTraceExchangeTrace adjX0 adjY0 Ω0 κ0)
    dsimp only [Functor.comp_obj, Functor.comp_map] at hn
    rw [← reassoc_of% hn]
    have ht1 := congrArg (fun k ↦
        PY1.map (q.hom.app (AX0.obj Ω0)) ≫ PY1.map (F1.map uX.hom) ≫ k) htr1
    rw [ht1]
    have hty := congrArg (fun k ↦ Qs.map (PY0.map
        (absoluteTraceExchangeTrace adjX0 adjY0 Ω0 κ0)) ≫ k) htrY
    rw [hty]
    have hk := κ1.hom.naturality uX.hom
    dsimp only [Functor.comp_obj, Functor.comp_map] at hk
    have hk' := congrArg (fun k ↦
        aY.hom.app (F0.obj (AX0.obj Ω0)) ≫ PY1.map (q.hom.app (AX0.obj Ω0)) ≫
          k ≫ adjX1.counit.app Ω1) hk
    simp only [Category.assoc] at hk'
    rw [hk']
    rw [reassoc_of% hκ]
    have htx := congrArg (fun k ↦ Qs.map (κ0.hom.app (AX0.obj Ω0)) ≫ k) htrX
    rw [htx]
    have ht0 := congrArg Qs.map htr0
    simp only [Functor.map_comp] at ht0
    rw [reassoc_of% ht0]
  refine ⟨htrace, ?_⟩
  intro M
  let K := DX0.obj (op M)
  let J := R0.obj K
  let K₁ := DX1.obj (op (QX.obj M))
  let J₁ := R1.obj K₁
  let r : QY.obj J ⟶ J₁ := c.hom.app K ≫ R1.map (dX.hom.app (op M))
  let b₀ : M ⊗ K ⟶ AX0.obj Ω0 := (β_ M K).hom ≫ evX0 M
  let b₁ : QX.obj M ⊗ K₁ ⟶ AX1.obj Ω1 :=
    (β_ (QX.obj M) K₁).hom ≫ evX1 (QX.obj M)
  let z₀ : J ⊗ F0.obj M ⟶ F0.obj (M ⊗ K) :=
    (β_ J (F0.obj M)).hom ≫ (θ0 M J).hom ≫
      F0.map (𝟙 M ⊗ₘ adj0.counit.app K)
  let z₁ : J₁ ⊗ F1.obj (QX.obj M) ⟶ F1.obj (QX.obj M ⊗ K₁) :=
    (β_ J₁ (F1.obj (QX.obj M))).hom ≫ (θ1 (QX.obj M) J₁).hom ≫
      F1.map (𝟙 (QX.obj M) ⊗ₘ adj1.counit.app K₁)
  have heps : p.hom.app J ≫ U1.map r ≫ adj1.counit.app K₁ =
      QX.map (adj0.counit.app K) ≫ dX.hom.app (op M) := by
    have hn := adj1.counit.naturality (dX.hom.app (op M))
    dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_map,
      Functor.op_obj, unop_op] at hn
    dsimp only [r, K₁, J]
    rw [U1.map_comp, Category.assoc, hn]
    rw [reassoc_of% (hε K)]
  have hb : (𝟙 (QX.obj M) ⊗ₘ dX.hom.app (op M)) ≫ b₁ =
      (Functor.Monoidal.μIso QX M K).hom ≫ QX.map b₀ ≫ uX.hom := by
    dsimp only [b₀, b₁, K, K₁, Functor.comp_obj, Functor.op_obj, unop_op]
    have hn := BraidedCategory.braiding_naturality
      (𝟙 (QX.obj M)) (dX.hom.app (op M))
    dsimp only [Functor.comp_obj, Functor.op_obj, unop_op] at hn
    rw [reassoc_of% hn, hevX]
    simpa only [Functor.Monoidal.μIso_hom, Functor.map_comp, Category.assoc, K] using
      congrArg (fun f ↦ f ≫ QX.map (evX0 M) ≫ uX.hom)
        (Functor.LaxBraided.braided (F := QX) M K).symm
  have hproj :
      (q.hom.app M ⊗ₘ r) ≫ (θ1 (QX.obj M) J₁).hom ≫
          F1.map (𝟙 (QX.obj M) ⊗ₘ adj1.counit.app K₁) =
        (Functor.Monoidal.μIso QY (F0.obj M) J).hom ≫
          QY.map (θ0 M J).hom ≫ q.hom.app (M ⊗ U0.obj J) ≫
          F1.map (Functor.Monoidal.μIso QX M (U0.obj J)).inv ≫
          F1.map (𝟙 (QX.obj M) ⊗ₘ QX.map (adj0.counit.app K)) ≫
          F1.map (𝟙 (QX.obj M) ⊗ₘ dX.hom.app (op M)) := by
    rw [← Category.comp_id (q.hom.app M), ← Category.id_comp r,
      ← tensorHom_comp_tensorHom, Category.assoc]
    dsimp only [Functor.comp_obj]
    rw [reassoc_of% (hθW1 (QX.obj M) (QY.obj J) J₁ r),
      ← reassoc_of% (hθ M J)]
    simp only [← F1.map_comp, ← id_tensor_comp]
    rw [heps]
  have hδ : (Functor.Monoidal.μIso QX M (U0.obj J)).inv ≫
        (𝟙 (QX.obj M) ⊗ₘ QX.map (adj0.counit.app K)) =
      QX.map (𝟙 M ⊗ₘ adj0.counit.app K) ≫
        (Functor.Monoidal.μIso QX M K).inv := by
    simpa only [Functor.Monoidal.μIso_inv, Functor.map_id,
      Functor.comp_obj, Functor.id_obj, J] using
      Functor.OplaxMonoidal.δ_natural QX (𝟙 M) (adj0.counit.app K)
  have hz : (r ⊗ₘ q.hom.app M) ≫ z₁ =
      (Functor.Monoidal.μIso QY J (F0.obj M)).hom ≫ QY.map z₀ ≫
        q.hom.app (M ⊗ K) ≫ F1.map (Functor.Monoidal.μIso QX M K).inv ≫
        F1.map (𝟙 (QX.obj M) ⊗ₘ dX.hom.app (op M)) := by
    dsimp only [z₀, z₁]
    rw [reassoc_of% (BraidedCategory.braiding_naturality r (q.hom.app M)), hproj]
    rw [← F1.map_comp_assoc, hδ, F1.map_comp_assoc]
    have hn := q.hom.naturality (𝟙 M ⊗ₘ adj0.counit.app K)
    dsimp only [Functor.comp_obj, Functor.comp_map] at hn
    rw [← reassoc_of% hn]
    simpa only [Functor.Monoidal.μIso_hom, Functor.map_comp, Category.assoc] using
      congrArg (fun f ↦ f ≫ QY.map (θ0 M J).hom ≫
        QY.map (F0.map (𝟙 M ⊗ₘ adj0.counit.app K)) ≫
        q.hom.app (M ⊗ K) ≫ F1.map (Functor.Monoidal.μIso QX M K).inv ≫
        F1.map (𝟙 (QX.obj M) ⊗ₘ dX.hom.app (op M)))
        (Functor.LaxBraided.braided (F := QY) J (F0.obj M)).symm
  have hpair : (r ⊗ₘ q.hom.app M) ≫ z₁ ≫ F1.map b₁ ≫
        absoluteTraceExchangeTrace adjX1 adjY1 Ω1 κ1 =
      (Functor.Monoidal.μIso QY J (F0.obj M)).hom ≫
        QY.map (z₀ ≫ F0.map b₀ ≫ absoluteTraceExchangeTrace adjX0 adjY0 Ω0 κ0) ≫
        uY.hom := by
    rw [reassoc_of% hz]
    have hfb := congrArg F1.map hb
    simp only [Functor.map_comp] at hfb
    rw [reassoc_of% hfb]
    simp only [Functor.map_comp, Category.assoc]
    have hcancel : F1.map (Functor.Monoidal.μIso QX M K).inv ≫
        F1.map (Functor.Monoidal.μIso QX M K).hom = 𝟙 _ := by
      rw [← F1.map_comp, Iso.inv_hom_id, F1.map_id]
    rw [reassoc_of% hcancel]
    have hn := q.hom.naturality b₀
    dsimp only [Functor.comp_obj, Functor.comp_map] at hn
    rw [← reassoc_of% hn, htrace]
  let E₀ := absoluteTraceExchangeMap adjX0 adjY0 Ω0 adj0 κ0 θ0 DX0 DY0 evX0 eY0 M
  let E₁ := absoluteTraceExchangeMap adjX1 adjY1 Ω1 adj1 κ1 θ1 DX1 DY1 evX1 eY1 (QX.obj M)
  have he₀ : (E₀ ⊗ₘ 𝟙 (F0.obj M)) ≫ evY0 (F0.obj M) =
      z₀ ≫ F0.map b₀ ≫ absoluteTraceExchangeTrace adjX0 adjY0 Ω0 κ0 := by
    rw [← hY0]
    dsimp only [E₀, absoluteTraceExchangeMap]
    rw [Equiv.apply_symm_apply]
    simp only [z₀, b₀, J, K, Category.assoc]
  have he₁ : (E₁ ⊗ₘ 𝟙 (F1.obj (QX.obj M))) ≫ evY1 (F1.obj (QX.obj M)) =
      z₁ ≫ F1.map b₁ ≫ absoluteTraceExchangeTrace adjX1 adjY1 Ω1 κ1 := by
    rw [← hY1]
    dsimp only [E₁, absoluteTraceExchangeMap]
    rw [Equiv.apply_symm_apply]
    simp only [z₁, b₁, J₁, K₁, Category.assoc]
  have hfinal : QY.map E₀ ≫ dY.hom.app (op (F0.obj M)) =
      r ≫ E₁ ≫ DY1.map (q.hom.app M).op := by
    apply (eY1 (QY.obj J) (QY.obj (F0.obj M))).injective
    rw [hY1, hY1]
    have hl : ((QY.map E₀ ≫ dY.hom.app (op (F0.obj M))) ⊗ₘ
          𝟙 (QY.obj (F0.obj M))) ≫ evY1 (QY.obj (F0.obj M)) =
        (Functor.Monoidal.μIso QY J (F0.obj M)).hom ≫
          QY.map (z₀ ≫ F0.map b₀ ≫
            absoluteTraceExchangeTrace adjX0 adjY0 Ω0 κ0) ≫ uY.hom := by
      rw [comp_tensor_id_assoc, hevY]
      have hn := Functor.LaxMonoidal.μ_natural QY E₀ (𝟙 (F0.obj M))
      simp only [Functor.map_id] at hn
      simp only [Functor.Monoidal.μIso_hom]
      rw [reassoc_of% hn, ← QY.map_comp_assoc, he₀]
    have hr : ((r ≫ E₁ ≫ DY1.map (q.hom.app M).op) ⊗ₘ
          𝟙 (QY.obj (F0.obj M))) ≫ evY1 (QY.obj (F0.obj M)) =
        (r ⊗ₘ q.hom.app M) ≫ z₁ ≫ F1.map b₁ ≫
          absoluteTraceExchangeTrace adjX1 adjY1 Ω1 κ1 := by
      rw [← he₁]
      simp only [comp_tensor_id, Category.assoc]
      dsimp only [Functor.comp_obj]
      rw [hYM1]
      simp only [← Category.assoc, tensorHom_comp_tensorHom,
        Category.comp_id, Category.id_comp]
    rw [hl, hr, hpair]
  simpa only [E₀, E₁, r, Category.assoc] using hfinal

end CategoryTheory
