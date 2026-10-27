/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.SixFunctors.RationalVerdier
public import Sheaf.SixFunctors.RationalOperations
public import Sheaf.Paper.CompletedTensorHomTranspose
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.SitePerfectComplex
public import Sheaf.Paper.DerivedPullbackTensorHom

import Sheaf.Paper.RationalTensorSymmetry
import Sheaf.Paper.RationalHomScalarTranspose
import Sheaf.Paper.RationalVerdierEvaluationAdjoints
import Sheaf.Paper.SitePerfectRationalBidual

/-! # Rational evaluation on retracts and finite scalar extension

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
lem-coef-rational-retract-evaluation, statement and proof paragraphs 1--3
(blueprint: lem-coef-rational-retract-evaluation).

The predicates spell out the clauses using the actual raw rational category,
normalized completed tensor-Hom transpose, and signed symmetry. The Hom-domain
witness in the conclusion is infrastructure supplied by rational operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
private theorem split_iso_intertwining {C : Type*} [Category C]
    {K L P Q : C} (a : K ⟶ L) [IsIso a]
    (i : P ⟶ K) (p : K ⟶ P) (j : Q ⟶ L) (q : L ⟶ Q)
    (hi : i ≫ p = 𝟙 P) (hj : j ≫ q = 𝟙 Q)
    (ha : (p ≫ i) ≫ a = a ≫ (q ≫ j)) : IsIso (i ≫ a ≫ q) := by
  have h₁ : a ≫ q ≫ j ≫ inv a = p ≫ i := by
    simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using
      (congrArg (fun f ↦ f ≫ inv a) ha).symm
  have h₂ : inv a ≫ p ≫ i ≫ a = q ≫ j := by
    simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using
      congrArg (fun f ↦ inv a ≫ f) ha
  refine ⟨⟨j ≫ inv a ≫ p, ?_, ?_⟩⟩
  · calc
      (i ≫ a ≫ q) ≫ j ≫ inv a ≫ p = i ≫ (a ≫ q ≫ j ≫ inv a) ≫ p := by
        simp only [Category.assoc]
      _ = 𝟙 P := by rw [h₁]; simp [← Category.assoc, hi]
  · calc
      (j ≫ inv a ≫ p) ≫ i ≫ a ≫ q = j ≫ (inv a ≫ p ≫ i ≫ a) ≫ q := by
        simp only [Category.assoc]
      _ = 𝟙 Q := by rw [h₂]; simp [← Category.assoc, hj]

namespace WeilConjectures.RationalRetractEvaluation

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (h : ∀ K M : sfRationalConstructibleCategory l E X,
    constructibleRationalHomPairs l E X (op K, M))

/-- The Hom-first transpose, on the recorded permitted pair.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-rational-retract-evaluation). -/
def adjoint {K L W : sfRationalConstructibleCategory l E X}
    (b : (RationalVerdier.tensor D l hl X E).obj (K, L) ⟶ W) :
    K ⟶ (RationalOperations.homDual l E X h W).obj (op L) :=
  (@podRationalClosed l _ E _ _ _ X (RationalVerdier.units D l hl X)).transpose K
    ⟨(op L, W), h L W⟩ b

/-- Perfection means that both actual adjoints are isomorphisms; the second uses
Koszul symmetry. Source: blueprint statement, second sentence
(blueprint: lem-coef-rational-retract-evaluation). -/
def IsPerfect {K L W : sfRationalConstructibleCategory l E X}
    (b : (RationalVerdier.tensor D l hl X E).obj (K, L) ⟶ W) : Prop :=
  IsIso (adjoint D l hl X E h b) ∧
    IsIso (adjoint D l hl X E h
      ((@pullbackTensorRationalBraiding l _ E _ _ _ X
        (RationalVerdier.units D l hl X) L K).hom ≫ b))

/-- The usual Hom-first evaluation to any target, including omega and the unit.
Source: blueprint proof paragraphs 1 and 3
(blueprint: lem-coef-rational-retract-evaluation). -/
def evaluation (K W : sfRationalConstructibleCategory l E X) :
    (RationalVerdier.tensor D l hl X E).obj
      ((RationalOperations.homDual l E X h W).obj (op K), K) ⟶ W :=
  (@podRationalClosed l _ E _ _ _ X (RationalVerdier.units D l hl X)).evaluation
    ⟨(op K, W), h K W⟩

/-- Restriction along any chosen splittings with adjoint idempotents, including
zero splittings. The images P,Q are existing objects of the raw category.
Source: blueprint statement and proof paragraph 2
(blueprint: lem-coef-rational-retract-evaluation). -/
def Retracts : Prop :=
  ∀ (K L W P Q : sfRationalConstructibleCategory l E X)
    (b : (RationalVerdier.tensor D l hl X E).obj (K, L) ⟶ W),
    IsPerfect D l hl X E h b →
    ∀ (i : P ⟶ K) (p : K ⟶ P) (j : Q ⟶ L) (q : L ⟶ Q),
    i ≫ p = 𝟙 P → j ≫ q = 𝟙 Q →
    (RationalVerdier.tensor D l hl X E).map (Prod.mkHom (p ≫ i) (𝟙 L)) ≫ b =
      (RationalVerdier.tensor D l hl X E).map (Prod.mkHom (𝟙 K) (q ≫ j)) ≫ b →
    IsPerfect D l hl X E h
      ((RationalVerdier.tensor D l hl X E).map (Prod.mkHom i j) ≫ b)

/-- The restricted canonical evaluation is the canonical evaluation of the
summand, as an equality of actual arrows. Source: blueprint proof paragraph 1
(blueprint: lem-coef-rational-retract-evaluation). -/
def EvaluationRestriction : Prop :=
  ∀ (K P W : sfRationalConstructibleCategory l E X) (i : P ⟶ K) (p : K ⟶ P),
    i ≫ p = 𝟙 P →
    (RationalVerdier.tensor D l hl X E).map
      (Prod.mkHom ((RationalOperations.homDual l E X h W).map p.op) i) ≫
        evaluation D l hl X E h K W = evaluation D l hl X E h P W

/-- Verdier evaluation is the recorded evaluation with its factors interchanged.
The delta and its inverse restrict by the explicit double-dual formulas.
Source: blueprint proof paragraph 1 (blueprint: lem-coef-rational-retract-evaluation). -/
def VerdierRestriction : Prop :=
  ∀ (w : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (A : RationalVerdier.Datum D l hl X E w),
    (∀ K : sfRationalConstructibleCategory l E X,
      IsPerfect D l hl X E h
        ((@pullbackTensorRationalBraiding l _ E _ _ _ X
          (RationalVerdier.units D l hl X) (A.dual.obj (op K)) K).hom ≫ A.evaluation K)) ∧
    ∀ (K P : sfRationalConstructibleCategory l E X) (i : P ⟶ K) (p : K ⟶ P),
      i ≫ p = 𝟙 P →
      ((RationalVerdier.tensor D l hl X E).map
        (Prod.mkHom i (A.dual.map p.op)) ≫ A.evaluation K = A.evaluation P) ∧
      (A.bidual.hom.app P = i ≫ A.bidual.hom.app K ≫
        (A.dual.rightOp ⋙ A.dual).map p) ∧
      (A.bidual.inv.app P = (A.dual.rightOp ⋙ A.dual).map i ≫
        A.bidual.inv.app K ≫ p)

/-- Finite scalar extension uses the coefficient-passage tensor comparison,
with no unrelated pairing or map chosen. The target becomes the scalar-extended
original target. Source: blueprint statement and proof paragraph 2
(blueprint: lem-coef-rational-retract-evaluation). -/
def ScalarExtension (F : Type u) [Field F] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) F] (ι : E →ₐ[Padic l] F)
    (hF : ∀ K M : sfRationalConstructibleCategory l F X,
      constructibleRationalHomPairs l F X (op K, M)) : Prop :=
  ∀ (K L W : sfRationalConstructibleCategory l E X)
    (b : (RationalVerdier.tensor D l hl X E).obj (K, L) ⟶ W),
    IsPerfect D l hl X E h b →
    IsPerfect D l hl X F hF
      ((@rationalTensorScalarComparison l _ E _ _ _ F _ _ _ ι X
        (RationalVerdier.units D l hl X)).inv.app (K, L) ≫
        (RationalVerdier.scalar l X E F ι).map b)

/-- All clauses, for every finite coefficient field. Internal-Hom closure is
asserted rather than assumed. The site-perfect hypothesis occurs only for the
unit-valued pairing, never for Verdier evaluation or the general retract law.
Source: blueprint statement, all sentences
(blueprint: lem-coef-rational-retract-evaluation). -/
def Conclusion : Prop :=
  ∀ (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E],
    ∃ h : ∀ K M : sfRationalConstructibleCategory l E X,
      constructibleRationalHomPairs l E X (op K, M),
    Retracts D l hl X E h ∧ EvaluationRestriction D l hl X E h ∧
    VerdierRestriction D l hl X E h ∧
    (∀ K : sfRationalConstructibleCategory l E X,
      IsSfRationalCoefficientSitePerfect l E X K →
      IsPerfect D l hl X E h
        (evaluation D l hl X E h K (RationalOperations.coefficientUnit l E X D hl))) ∧
    ∀ (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
      (ι : E →ₐ[Padic l] F),
      ∃ hF : ∀ K M : sfRationalConstructibleCategory l F X,
        constructibleRationalHomPairs l F X (op K, M),
      Retracts D l hl X F hF ∧ ScalarExtension D l hl X E h F ι hF


private theorem adjoint_naturality
    (K L W P Q : sfRationalConstructibleCategory l E X)
    (b : (RationalVerdier.tensor D l hl X E).obj (K, L) ⟶ W)
    (i : P ⟶ K) (j : Q ⟶ L) :
    adjoint D l hl X E h
        ((RationalVerdier.tensor D l hl X E).map (Prod.mkHom i j) ≫ b) =
      i ≫ adjoint D l hl X E h b ≫ (RationalOperations.homDual l E X h W).map j.op := by
  let C : D.CoefficientDatum := ⟨l, hl, AlgebraicClosure E⟩
  obtain ⟨tau, laws, _⟩ := (completedTensorHomTranspose D C E X).2
  let A : (constructibleRationalHomPairs l E X).FullSubcategory := ⟨(op L, W), h L W⟩
  let B : (constructibleRationalHomPairs l E X).FullSubcategory := ⟨(op Q, W), h Q W⟩
  let g : A ⟶ B := ObjectProperty.homMk (Prod.mkHom j.op (𝟙 W))
  let S := @podRationalClosed l _ E _ _ _ X (RationalVerdier.units D l hl X)
  have hg : (rationalDerivedInternalHom l E X).map g =
      (RationalOperations.homDual l E X h W).map j.op := rfl
  have hn := laws.naturality K P A B i g (adjoint D l hl X E h b)
  rw [laws.symmetry, laws.symmetry] at hn
  rw [hg] at hn
  simp only [Category.assoc] at hn
  change (@pullbackTensorRationalBraiding l _ E _ _ _ X
      (RationalVerdier.units D l hl X) Q P).hom ≫
      (S.transpose P B).symm
        (i ≫ adjoint D l hl X E h b ≫ (RationalOperations.homDual l E X h W).map j.op) =
    (RationalVerdier.tensor D l hl X E).map (Prod.mkHom j i) ≫
      ((@pullbackTensorRationalBraiding l _ E _ _ _ X
        (RationalVerdier.units D l hl X) L K).hom ≫
      (S.transpose K A).symm (S.transpose K A b) ≫ 𝟙 W) at hn
  rw [AddEquiv.symm_apply_apply, Category.comp_id] at hn
  have hs := congrArg (fun f ↦ f ≫ b)
    ((rationalTensorSymmetry_laws D l hl X E).1 K L P Q i j).symm
  have hn' := hn.trans (by simpa only [Category.assoc] using hs)
  have he := (cancel_epi
    (@pullbackTensorRationalBraiding l _ E _ _ _ X
      (RationalVerdier.units D l hl X) Q P).hom).mp hn'
  exact (congrArg (S.transpose P B) he).symm.trans
    (AddEquiv.apply_symm_apply _ _)

private theorem first_retract
    (K L W P Q : sfRationalConstructibleCategory l E X)
    (b : (RationalVerdier.tensor D l hl X E).obj (K, L) ⟶ W)
    [IsIso (adjoint D l hl X E h b)]
    (i : P ⟶ K) (p : K ⟶ P) (j : Q ⟶ L) (q : L ⟶ Q)
    (hi : i ≫ p = 𝟙 P) (hj : j ≫ q = 𝟙 Q)
    (hb : (RationalVerdier.tensor D l hl X E).map (Prod.mkHom (p ≫ i) (𝟙 L)) ≫ b =
      (RationalVerdier.tensor D l hl X E).map (Prod.mkHom (𝟙 K) (q ≫ j)) ≫ b) :
    IsIso (adjoint D l hl X E h
      ((RationalVerdier.tensor D l hl X E).map (Prod.mkHom i j) ≫ b)) := by
  let H := RationalOperations.homDual l E X h W
  have he := congrArg (adjoint D l hl X E h) hb
  rw [adjoint_naturality, adjoint_naturality] at he
  simp only [op_id, Category.id_comp, op_comp, Functor.map_comp] at he
  have he' : (p ≫ i) ≫ adjoint D l hl X E h b =
      adjoint D l hl X E h b ≫ (H.map j.op ≫ H.map q.op) := by
    simpa [H, Category.assoc] using he
  have hsplit : H.map q.op ≫ H.map j.op = 𝟙 (H.obj (op Q)) := by
    rw [← H.map_comp, ← op_comp, hj, op_id]
    exact H.map_id _
  have hr := split_iso_intertwining (adjoint D l hl X E h b)
    i p (H.map q.op) (H.map j.op) hi hsplit he'
  rw [adjoint_naturality]
  exact hr

private theorem retracts : Retracts D l hl X E h := by
  intro K L W P Q b hb i p j q hi hj he
  let T := RationalVerdier.tensor D l hl X E
  let beta := @pullbackTensorRationalBraiding l _ E _ _ _ X
    (RationalVerdier.units D l hl X)
  have := hb.1
  have := hb.2
  refine ⟨first_retract D l hl X E h K L W P Q b i p j q hi hj he, ?_⟩
  have he' : T.map (Prod.mkHom (q ≫ j) (𝟙 K)) ≫ (beta L K).hom ≫ b =
      T.map (Prod.mkHom (𝟙 L) (p ≫ i)) ≫ (beta L K).hom ≫ b := by
    have hs₁ := congrArg (fun f ↦ f ≫ b)
      ((rationalTensorSymmetry_laws D l hl X E).1 K L K L (𝟙 K) (q ≫ j))
    have hs₂ := congrArg (fun f ↦ f ≫ b)
      ((rationalTensorSymmetry_laws D l hl X E).1 K L K L (p ≫ i) (𝟙 L))
    have h1 : T.map (Prod.mkHom (q ≫ j) (𝟙 K)) ≫ (beta L K).hom ≫ b =
        (beta L K).hom ≫ T.map (Prod.mkHom (𝟙 K) (q ≫ j)) ≫ b := by
      simpa only [Category.assoc] using hs₁.symm
    have h2 : (beta L K).hom ≫ T.map (Prod.mkHom (p ≫ i) (𝟙 L)) ≫ b =
        T.map (Prod.mkHom (𝟙 L) (p ≫ i)) ≫ (beta L K).hom ≫ b := by
      simpa only [Category.assoc] using hs₂
    exact h1.trans ((congrArg (fun f ↦ (beta L K).hom ≫ f) he.symm).trans h2)
  have hr := first_retract D l hl X E h L K W Q P ((beta L K).hom ≫ b)
    j q i p hj hi he'
  have hs := congrArg (fun f ↦ f ≫ b)
    ((rationalTensorSymmetry_laws D l hl X E).1 K L P Q i j)
  have hs' : (beta Q P).hom ≫ T.map (Prod.mkHom i j) ≫ b =
      T.map (Prod.mkHom j i) ≫ (beta L K).hom ≫ b := by
    simpa only [Category.assoc] using hs
  rw [hs']
  exact hr

omit [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))] in
private theorem adjoint_evaluation (K W : sfRationalConstructibleCategory l E X) :
    adjoint D l hl X E h (evaluation D l hl X E h K W) =
      𝟙 ((RationalOperations.homDual l E X h W).obj (op K)) := by
  exact AddEquiv.apply_symm_apply _ _

private theorem evaluation_restriction : EvaluationRestriction D l hl X E h := by
  intro K P W i p hi
  let H := RationalOperations.homDual l E X h W
  apply ((@podRationalClosed l _ E _ _ _ X
    (RationalVerdier.units D l hl X)).transpose (H.obj (op P))
      ⟨(op P, W), h P W⟩).injective
  change adjoint D l hl X E h _ = adjoint D l hl X E h _
  rw [adjoint_naturality, adjoint_evaluation, adjoint_evaluation]
  change H.map p.op ≫ 𝟙 _ ≫ H.map i.op = 𝟙 _
  rw [Category.id_comp, ← H.map_comp, ← op_comp, hi, op_id, H.map_id]

private theorem verdier_restriction : VerdierRestriction D l hl X E h := by
  intro w A
  obtain ⟨e, he⟩ := rationalVerdier_evaluation_adjoints D l hl X E h w A
  let T := RationalVerdier.tensor D l hl X E
  let beta := @pullbackTensorRationalBraiding l _ E _ _ _ X
    (RationalVerdier.units D l hl X)
  refine ⟨?_, ?_⟩
  · intro K
    constructor
    · change IsIso ((@podRationalClosed l _ E _ _ _ X
        (RationalVerdier.units D l hl X)).transpose _ _ _)
      rw [(he K).1]
      infer_instance
    · have hs := (rationalTensorSymmetry_laws D l hl X E).2 K (A.dual.obj (op K))
      have hh : (beta K (A.dual.obj (op K))).hom ≫
          (beta (A.dual.obj (op K)) K).hom ≫ A.evaluation K = A.evaluation K := by
        rw [← Category.assoc, hs, Category.id_comp]
      change IsIso (adjoint D l hl X E h
        ((beta K (A.dual.obj (op K))).hom ≫
          (beta (A.dual.obj (op K)) K).hom ≫ A.evaluation K))
      rw [hh]
      change IsIso ((@podRationalClosed l _ E _ _ _ X
        (RationalVerdier.units D l hl X)).transpose _ _ _)
      rw [(he K).2]
      infer_instance
  · intro K P i p hi
    refine ⟨?_, ?_, ?_⟩
    · have hn := congrArg (fun f ↦ T.map (Prod.mkHom i (𝟙 _)) ≫ f)
        (A.evaluation_natural K P p)
      have h1 : T.map (Prod.mkHom i (𝟙 (A.dual.obj (op P)))) ≫
          T.map (Prod.mkHom p (𝟙 (A.dual.obj (op P)))) =
            𝟙 (T.obj (P, A.dual.obj (op P))) := by
        rw [← T.map_comp]
        have hp : Prod.mkHom i (𝟙 (A.dual.obj (op P))) ≫
            Prod.mkHom p (𝟙 _) = 𝟙 (P, A.dual.obj (op P)) := by
          change Prod.mkHom (i ≫ p) (𝟙 _ ≫ 𝟙 _) = Prod.mkHom (𝟙 P) (𝟙 _)
          rw [hi, Category.id_comp]
        rw [hp, T.map_id]
      have h2 : T.map (Prod.mkHom i (𝟙 _)) ≫
          T.map (Prod.mkHom (𝟙 K) (A.dual.map p.op)) =
          T.map (Prod.mkHom i (A.dual.map p.op)) := by
        rw [← T.map_comp]
        congr 1
        change Prod.mkHom (i ≫ 𝟙 K) (𝟙 _ ≫ A.dual.map p.op) =
          Prod.mkHom i (A.dual.map p.op)
        rw [Category.comp_id, Category.id_comp]
      change T.map (Prod.mkHom i (𝟙 _)) ≫
          (T.map (Prod.mkHom p (𝟙 _)) ≫ A.evaluation P) =
        T.map (Prod.mkHom i (𝟙 _)) ≫
          (T.map (Prod.mkHom (𝟙 K) (A.dual.map p.op)) ≫ A.evaluation K) at hn
      rw [← Category.assoc, ← Category.assoc, h1, h2, Category.id_comp] at hn
      exact hn.symm
    · have hn := congrArg (fun f ↦ f ≫ (A.dual.rightOp ⋙ A.dual).map p)
        (A.bidual.hom.naturality i)
      have hm := (A.dual.rightOp ⋙ A.dual).map_id P
      simpa only [Functor.id_map, Category.assoc, ← Functor.map_comp, hi,
        hm, Category.comp_id] using hn.symm
    · have hn := congrArg (fun f ↦ f ≫ p) (A.bidual.inv.naturality i)
      simpa [Category.assoc, hi] using hn.symm

private theorem scalar_extension
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F)
    (hF : ∀ K M : sfRationalConstructibleCategory l F X,
      constructibleRationalHomPairs l F X (op K, M)) :
    ScalarExtension D l hl X E h F ι hF := by
  intro K L W b hb
  have := hb.1
  have := hb.2
  obtain ⟨ht, hs⟩ := rationalHomScalar_transpose D l hl X E F ι
  constructor
  · change IsIso ((@podRationalClosed l _ F _ _ _ X
      (RationalVerdier.units D l hl X)).transpose _ _ _)
    have ht' := ht K L W (h L W) b
    have hh : IsIso ((RationalVerdier.scalar l X E F ι).map
        (adjoint D l hl X E h b) ≫
        (rationalHomScalarComparison l E F ι X ⟨(op L, W), h L W⟩).hom) := by
      infer_instance
    exact ht'.symm ▸ hh
  · rw [← Category.assoc, hs K L, Category.assoc, ← Functor.map_comp]
    change IsIso ((@podRationalClosed l _ F _ _ _ X
      (RationalVerdier.units D l hl X)).transpose _ _ _)
    have ht' := ht L K W (h K W)
      ((@pullbackTensorRationalBraiding l _ E _ _ _ X
        (RationalVerdier.units D l hl X) L K).hom ≫ b)
    have hh : IsIso ((RationalVerdier.scalar l X E F ι).map
        (adjoint D l hl X E h
          ((@pullbackTensorRationalBraiding l _ E _ _ _ X
            (RationalVerdier.units D l hl X) L K).hom ≫ b)) ≫
        (rationalHomScalarComparison l E F ι X ⟨(op K, W), h K W⟩).hom) := by
      infer_instance
    exact ht'.symm ▸ hh

include D hl in
private theorem hom_closed :
    ∀ K M : sfRationalConstructibleCategory l E X,
      constructibleRationalHomPairs l E X (op K, M) := by
  have hh : RationalOperations.Conclusion D l hl (AlgebraicClosure E)
      X (Spec (.of D.k)) (X ↘ Spec (.of D.k)) (integralDualizingCompactification D X) := by
    exact coef_rational_operations D l hl (AlgebraicClosure E)
      X (Spec (.of D.k)) (X ↘ Spec (.of D.k)) (integralDualizingCompactification D X)
  obtain ⟨S, Sa, H⟩ := hh
  obtain ⟨I, J, _⟩ := H ⟨E⟩ ⟨E⟩ (AlgHom.id (Padic l) E)
  exact I.homX.permitted

end WeilConjectures.RationalRetractEvaluation

namespace WeilConjectures

/-- Evaluation and biduality restrict to split idempotents; two-sided perfect
pairings stay perfect on adjoint summands and after finite coefficient extension.
For site-perfect objects this applies also to evaluation to the coefficient unit.
Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
lem-coef-rational-retract-evaluation, proof paragraphs 1--3
(blueprint: lem-coef-rational-retract-evaluation).

Proof (the thirteen DAG steps):
1. Use the raw rational category, completed tensor and Hom of rational operations,
and the evaluation-defined delta from rational Verdier duality. Idempotents split
inside this category by lem-weil-rationalization-idempotent-complete.
2. For splittings i,p and j,q, transposition of b gives a,c. Adjointness gives
intertwining with the two idempotents. Naturality identifies the restricted
adjoints with i followed by a and D(j), and j followed by c and D(i).
3. Their inverses are D(q) followed by a inverse and p, and D(p) followed by
c inverse and q. Each inverse equation reduces to the splitting identity using
intertwining. This also covers zero idempotents.
4. Naturality of evaluation gives ev_K composed with D(p) tensor i = ev_P.
The adjoints of Verdier evaluation are identity and delta. Naturality of delta
gives its displayed retract formula and the displayed inverse formula.
5. Finite scalar extension has the canonical tensor and duality comparisons
from integral finite extension, integral scalar comparisons and rational Verdier.
6. lem-coef-rational-scalar-transpose-compatibility transports both adjoints,
their restricted formulas and inverse formulas. Functoriality preserves splitting
identities. The evaluation and delta squares transport step 4 as well.
7. For a site-perfect A use Hom(A,unit) and its canonical evaluation. Internal
Hom exact restriction and exact site restriction identify these maps on slices.
Completed tensor restriction follows from its K-flat and Roos models and exact
countable products, with their fixed quotient and cone-coordinate maps.
8. On a bounded local finite-projective model, the Hom differential is the signed
Hom-complex differential and double evaluation in degree r has sign (-1)^r.
9. lem-coef-rational-bidual-triangle-compatibility supplies the signed shift and
all triangle squares, including the connecting map. Triangle two-out-of-three
makes the invertibility locus stable under shifts and triangles.
10. The unit is reflexive, then finite sums and retracts are reflexive by the
explicit retract inverse. Descend the finite stupid-truncation triangles of the
local bounded model to prove local reflexivity, without integral perfect lifts.
11. Write the rational bidual map as an integral numerator over a uniformizer
power. Its integral cone is constructible. Refine to a finite affine pro-etale
cover (the empty scheme is immediate). Local rational vanishing gives finitely
many annihilator powers; their maximum annihilates every cohomology sheaf
by sheaf separatedness. This does not yet annihilate the cone identity.
12. Derived completeness and exact countable products bound cone cohomology.
If scalar powers kill the ends of a triangle, their sum kills the middle by
Hom exactness. Induction on the finite cohomological truncations therefore kills
the cone identity by a power. Inverting the uniformizer makes the cone zero,
so the actual global bidual map is invertible and unit evaluation is perfect.
13. Apply steps 2--3 to the unit-valued pairing and step 6 with the canonical
unit and internal-Hom scalar comparisons. This gives its retract and extension
clauses, using the very same normalized evaluation and both its adjoints. -/
theorem coef_rational_retract_evaluation
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))] :
    RationalRetractEvaluation.Conclusion D l hl X := by
  intro E _ _ _
  let h := RationalRetractEvaluation.hom_closed D l hl X E
  refine ⟨h, RationalRetractEvaluation.retracts D l hl X E h,
    RationalRetractEvaluation.evaluation_restriction D l hl X E h,
    RationalRetractEvaluation.verdier_restriction D l hl X E h, ?_, ?_⟩
  · intro K hK
    refine ⟨?_, sitePerfect_rational_bidual D l hl X E h K hK⟩
    rw [RationalRetractEvaluation.adjoint_evaluation]
    infer_instance
  · intro F _ _ _ ι
    let hF := RationalRetractEvaluation.hom_closed D l hl X F
    exact ⟨hF, RationalRetractEvaluation.retracts D l hl X F hF,
      RationalRetractEvaluation.scalar_extension D l hl X E h F ι hF⟩
end WeilConjectures
