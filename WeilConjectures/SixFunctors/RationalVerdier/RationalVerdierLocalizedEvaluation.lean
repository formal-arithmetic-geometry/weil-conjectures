/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierLocalizedCore
public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import WeilConjectures.SixFunctors.IntegralHom.Evaluation.IntegralHomEvaluationNaturality

/-! # Completed evaluation and its rational naturality square

Source: blueprint thm-coef-rational-verdier, paragraph 1, and Stacks 08J9
(blueprint: lem-coef-rational-verdier-localized-evaluation). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped TensorProduct

namespace WeilConjectures.RationalVerdier

attribute [local irreducible] rationalDerivedTensor

private theorem chosen_spec {A : Sort*} {P : A → Prop}
    (h : ∃ a, P a) (a : A) (ha : a = h.choose) : P a :=
  ha.symm ▸ h.choose_spec

private theorem id_heq {C : Type*} [Category* C] {A B : C} (h : A = B) :
    HEq (𝟙 A) (𝟙 B) := by cases h; rfl

private theorem tensor_map_heq {C : Type*} [Category* C] (B : C × C ⥤ C)
    {X X' Y Y' M M' N N' : C}
    (hx : X = X') (hy : Y = Y') (hm : M = M') (hn : N = N')
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : M ⟶ N} {g' : M' ⟶ N'}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (B.map (Prod.mkHom f g)) (B.map (Prod.mkHom f' g')) := by
  cases hx; cases hy; cases hm; cases hn; cases hf; cases hg
  rfl

private theorem inverse_comparison_square {C : Type*} [Category* C]
    (A B : C × C ⥤ C) (η : A ⟶ B) {K M DK DM W : C}
    (f : K ⟶ M) (g : DM ⟶ DK)
    (eK : A.obj (K, DK) ⟶ W) (eM : A.obj (M, DM) ⟶ W)
    [IsIso (η.app (K, DM))] [IsIso (η.app (M, DM))] [IsIso (η.app (K, DK))]
    (h : A.map (Prod.mkHom f (𝟙 DM)) ≫ eM =
      A.map (Prod.mkHom (𝟙 K) g) ≫ eK) :
    B.map (Prod.mkHom f (𝟙 DM)) ≫ (asIso (η.app (M, DM))).inv ≫ eM =
      B.map (Prod.mkHom (𝟙 K) g) ≫ (asIso (η.app (K, DK))).inv ≫ eK := by
  apply (cancel_epi (η.app (K, DM))).1
  simp only [← Category.assoc]
  rw [← η.naturality (Prod.mkHom f (𝟙 DM)),
    ← η.naturality (Prod.mkHom (𝟙 K) g)]
  simpa only [Category.assoc, asIso_inv, IsIso.hom_inv_id_assoc] using h

private theorem eval_localizes
    {R : Type*} [CommRing R] {C : Type*} [Category* C] [Preadditive C] [Linear R C]
    (t : R) (U : Cᵒᵖ ⥤ C) (T : C × C ⥤ C) (w : C)
    (e₀ : ∀ K : C, T.obj (K, U.obj (op K)) ⟶ w)
    (hn : ∀ (K M : C) (f : K ⟶ M),
      T.map (Prod.mkHom f (𝟙 _)) ≫ e₀ M =
        T.map (Prod.mkHom (𝟙 _) (U.map f.op)) ≫ e₀ K)
    (F : (ScalarLocalization R C t)ᵒᵖ ⥤ ScalarLocalization R C t) [F.Additive]
    (B : ScalarLocalization R C t × ScalarLocalization R C t ⥤ ScalarLocalization R C t)
    (ho : ∀ K, F.obj (op K) = (ScalarLocalization.localization R C t).obj (U.obj (op K.obj)))
    (hT : ∀ P, B.obj P = (ScalarLocalization.localization R C t).obj
      (T.obj (P.1.obj, P.2.obj)))
    (hm : ∀ (K M : C) (f : K ⟶ M) (a : Localization.Away t),
      HEq (F.map (Quiver.Hom.op (a ⊗ₜ[R] f : ScalarLocalization.mk K ⟶
        ScalarLocalization.mk M))) (a ⊗ₜ[R] U.map f.op))
    (hB : ∀ K K' M M' : ScalarLocalization R C t,
      ∃ b : (K ⟶ K') →+ (M ⟶ M') →+ (B.obj (K, M) ⟶ B.obj (K', M')),
        ∀ f g, B.map (Prod.mkHom f g) = b f g)
    (pB : ∀ (K K' M M' : C) (f : K ⟶ K') (g : M ⟶ M')
      (a b : Localization.Away t),
      HEq (B.map (Prod.mkHom (a ⊗ₜ[R] f : ScalarLocalization.mk K ⟶
        ScalarLocalization.mk K') (b ⊗ₜ[R] g : ScalarLocalization.mk M ⟶
          ScalarLocalization.mk M'))) ((a * b) ⊗ₜ[R] T.map (Prod.mkHom f g)))
    (ev : ∀ K : ScalarLocalization R C t,
      B.obj (K, F.obj (op K)) ⟶ (ScalarLocalization.localization R C t).obj w)
    (hev : ∀ K, HEq (ev K) ((ScalarLocalization.localization R C t).map (e₀ K.obj)))
    (K M : ScalarLocalization R C t) (f : K ⟶ M) :
    B.map (Prod.mkHom f (𝟙 (F.obj (op M)))) ≫ ev M =
      B.map (Prod.mkHom (𝟙 K) (F.map f.op)) ≫ ev K := by
  let Q := ScalarLocalization.localization R C t
  have hs (K M : ScalarLocalization R C t) :
      B.obj (K, F.obj (op M)) = Q.obj (T.obj (K.obj, U.obj (op M.obj))) :=
    (congrArg (fun Z ↦ B.obj (K, Z)) (ho M)).trans (hT _)
  obtain ⟨b₁, hb₁⟩ := hB K M (F.obj (op M)) (F.obj (op M))
  obtain ⟨b₂, hb₂⟩ := hB K K (F.obj (op M)) (F.obj (op K))
  induction f using TensorProduct.induction_on with
  | zero =>
    change B.map (Prod.mkHom (0 : K ⟶ M) (𝟙 _)) ≫ ev M =
      B.map (Prod.mkHom (𝟙 _) (F.map (0 : op M ⟶ op K))) ≫ ev K
    simp only [hb₁, hb₂, F.map_zero, map_zero, AddMonoidHom.zero_apply, zero_comp]
  | tmul a f =>
    have h₁ := (tensor_map_heq B rfl rfl (ho M) (ho M) HEq.rfl (id_heq (ho M))).trans
      (pB K.obj M.obj (U.obj (op M.obj)) (U.obj (op M.obj)) f (𝟙 _) a 1)
    have h₂ := (tensor_map_heq B rfl rfl (ho M) (ho K) HEq.rfl
      (hm K.obj M.obj f a)).trans
      (pB K.obj K.obj (U.obj (op M.obj)) (U.obj (op K.obj)) (𝟙 _) (U.map f.op) 1 a)
    apply eq_of_heq
    refine (heq_comp (hs K M) (hs M M) rfl h₁ (hev M)).trans
      (HEq.trans ?_ (heq_comp (hs K M) (hs K K) rfl h₂ (hev K)).symm)
    apply heq_of_eq
    change ScalarLocalization.composition R C t _ _ _
        (1 ⊗ₜ[R] e₀ M.obj) ((a * 1) ⊗ₜ[R] T.map (Prod.mkHom f (𝟙 _))) =
      ScalarLocalization.composition R C t _ _ _
        (1 ⊗ₜ[R] e₀ K.obj) ((1 * a) ⊗ₜ[R] T.map (Prod.mkHom (𝟙 _) (U.map f.op)))
    simp only [ScalarLocalization.composition_tmul, one_mul, mul_one, hn]
  | add f g hf hg =>
    change B.map (Prod.mkHom (f + g) (𝟙 _)) ≫ ev M =
      B.map (Prod.mkHom (𝟙 _) (F.map (Quiver.Hom.op (show K ⟶ M from f) +
        Quiver.Hom.op (show K ⟶ M from g)))) ≫ ev K
    simpa only [hb₁, hb₂, F.map_add, map_add,
      AddMonoidHom.add_apply, Preadditive.add_comp] using congrArg₂ (· + ·) hf hg

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

variable (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (w : sfIntegralConstructibleCategory l E X)
  (hp : ∀ K : sfIntegralConstructibleCategory l E X,
    sfIntegralConstructible l E X ((IntegralVerdier.dual l E X w.obj).obj (op K.obj)))
  (a : IntegralHom.TensorPresentation.{u, u} X
    (completedIntegralCommRingSheafUnrestricted l E X))
  (c : Completion D l hl X E a)

/-- The completed integral evaluation is ordinary evaluation after inverse completion.
Source: blueprint thm-coef-rational-verdier, paragraph 1
(blueprint: lem-coef-rational-verdier-localized-evaluation). -/
def integralEvaluation (K : sfIntegralConstructibleCategory l E X) :
    (integralTensor D l hl X E).obj
      (K, (IntegralVerdier.restrictedDual l E X w.obj hp).obj (op K)) ⟶ w :=
  ObjectProperty.homMk
    (X := (integralTensor D l hl X E).obj
      (K, (IntegralVerdier.restrictedDual l E X w.obj hp).obj (op K))) (Y := w)
    ((@asIso _ _ _ _
      (c.map.app (K.obj, (IntegralVerdier.dual l E X w.obj).obj (op K.obj)))
      (c.invertible K
        ((IntegralVerdier.restrictedDual l E X w.obj hp).obj (op K)))).inv ≫
      (a.adjunction K.obj).counit.app w.obj)

private theorem integralEvaluation_natural
    (K M : sfIntegralConstructibleCategory l E X) (f : K ⟶ M) :
    (integralTensor D l hl X E).map
        (Prod.mkHom f (𝟙 ((IntegralVerdier.restrictedDual l E X w.obj hp).obj (op M)))) ≫
      integralEvaluation D l hl X E w hp a c M =
    (integralTensor D l hl X E).map
        (Prod.mkHom (𝟙 K) ((IntegralVerdier.restrictedDual l E X w.obj hp).map f.op)) ≫
      integralEvaluation D l hl X E w hp a c K := by
  apply ObjectProperty.hom_ext
  let DK := (IntegralVerdier.restrictedDual l E X w.obj hp).obj (op K)
  let DM := (IntegralVerdier.restrictedDual l E X w.obj hp).obj (op M)
  let : IsIso (c.map.app (K.obj, DM.obj)) := c.invertible K DM
  let : IsIso (c.map.app (M.obj, DM.obj)) := c.invertible M DM
  let : IsIso (c.map.app (K.obj, DK.obj)) := c.invertible K DK
  apply inverse_comparison_square a.tensor (integralCompletedTensor l E X) c.map
    f.hom ((IntegralVerdier.restrictedDual l E X w.obj hp).map f.op).hom
    ((a.adjunction K.obj).counit.app w.obj) ((a.adjunction M.obj).counit.app w.obj)
  exact (IntegralHom.evaluation_naturality X _ a M.obj K.obj w.obj f.hom).symm

omit [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))] in
/-- The literal object equality needed to localize completed evaluation.
Source: blueprint thm-coef-rational-verdier, paragraph 1
(blueprint: lem-coef-rational-verdier-localized-evaluation).
Proof: use the rational tensor's object equation, then the rational dual's object
equation in the second argument. These are the prescribed unchanged integral objects. -/
theorem localizedEvaluation_source (K : sfRationalConstructibleCategory l E X) :
    (tensor D l hl X E).obj (K, (localizedDual l E X w hp).obj (op K)) =
      (sfRationalConstructibleLocalization l E X).obj
        ((integralTensor D l hl X E).obj
          (K.obj, (IntegralVerdier.restrictedDual l E X w.obj hp).obj (op K.obj))) := by
  have hs := chosen_spec
    (@rationalDerivedTensor_existsUnique l _ E _ _ _ X (units D l hl X)).exists
    (tensor D l hl X E) (by unfold tensor rationalDerivedTensor; rfl)
  have hT := hs.1 (K, (localizedDual l E X w hp).obj (op K))
  have hD := congrArg ScalarLocalization.obj ((localizedDual_spec l E X w hp).1 K)
  exact hT.trans (congrArg
    (fun M : sfIntegralConstructibleCategory l E X ↦
      (sfRationalConstructibleLocalization l E X).obj
        ((integralTensor D l hl X E).obj (K.obj, M))) hD)

/-- Localized evaluation, with the source transported by its proved object equation.
Source: blueprint thm-coef-rational-verdier, paragraph 1
(blueprint: lem-coef-rational-verdier-localized-evaluation). -/
def localizedEvaluation (K : sfRationalConstructibleCategory l E X) :
    (tensor D l hl X E).obj (K, (localizedDual l E X w hp).obj (op K)) ⟶
      (sfRationalConstructibleLocalization l E X).obj w :=
  eqToHom (localizedEvaluation_source D l hl X E w hp K) ≫
    (sfRationalConstructibleLocalization l E X).map
      (integralEvaluation D l hl X E w hp a c K.obj)

/-- Naturality of the constructed completed evaluation after raw scalar localization.
This asserts only the evaluation square for the explicitly constructed maps, without
any exactness, equivalence or biduality conclusion.
Source: blueprint thm-coef-rational-verdier, paragraph 1, evaluation compatibility
(blueprint: lem-coef-rational-verdier-localized-evaluation).

Proof: for an integral arrow f:K to M, ordinary evaluation's contravariant naturality
is the first-variable counit equation of IntegralHom.evaluation_naturality. Apply
naturality of c.map to the two tensor arrows (f,id) and (id,Df), and cancel its
invertible components at (K,DM), (M,DM) and (K,DK). This gives the same square for
integralEvaluation, the completed counit defined above. Localize this equation.
The pure-tensor specification of the rational tensor multiplies its component maps
by the arrow's scalar. The rational dual's pure-tensor specification preserves that
scalar, so both sides of the evaluation equation are the localized integral square
multiplied by the same scalar. The tensor and dual object equations conjugate this
square by the exact source equalities used in localizedEvaluation. Finally, express
any localized arrow as a sum of pure tensors. Additivity of the rational dual and
separate additivity of the rational tensor extend the square to zero and sums.
There is no use of faithfulness of localization or invertibility of any input arrow. -/
theorem localizedEvaluation_natural
    (K M : sfRationalConstructibleCategory l E X) (f : K ⟶ M) :
    (tensor D l hl X E).map
        (Prod.mkHom f (𝟙 ((localizedDual l E X w hp).obj (op M)))) ≫
      localizedEvaluation D l hl X E w hp a c M =
    (tensor D l hl X E).map
        (Prod.mkHom (𝟙 K) ((localizedDual l E X w hp).map f.op)) ≫
      localizedEvaluation D l hl X E w hp a c K  := by
  classical
  let U := IntegralVerdier.restrictedDual l E X w.obj hp
  let F := localizedDual l E X w hp
  let B := tensor D l hl X E
  let Q := sfRationalConstructibleLocalization l E X
  obtain ⟨ho, ha, _, hm⟩ := localizedDual_spec l E X w hp
  let : F.Additive := ha
  have hs := chosen_spec
    (@rationalDerivedTensor_existsUnique l _ E _ _ _ X (units D l hl X)).exists
    B (by dsimp only [B, tensor]; unfold rationalDerivedTensor; rfl)
  apply eval_localizes (Padic.coefficientExtensionUniformizer l E)
    U (integralTensor D l hl X E) w (integralEvaluation D l hl X E w hp a c)
    (integralEvaluation_natural D l hl X E w hp a c) F B ho hs.1 hm
  · intro K K' M M'
    obtain ⟨b, hb, _⟩ := hs.2 K K' M M'
    exact ⟨LinearMap.toAddMonoidHom'.comp b.toAddMonoidHom, hb⟩
  · intro K K' M M' f g z z'
    obtain ⟨b, hb, hpure⟩ := hs.2 (Q.obj K) (Q.obj K') (Q.obj M) (Q.obj M')
    exact (heq_of_eq (hb _ _)).trans (hpure f g z z')
  · intro K
    exact eqToHom_comp_heq (Q.map (integralEvaluation D l hl X E w hp a c K.obj))
      (localizedEvaluation_source D l hl X E w hp K)

end WeilConjectures.RationalVerdier
