/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.Paper.ClassicalFiniteWeilDiagramData

import Sheaf.Paper.ClassicalWeilCoherentDiagramStages
import Sheaf.Paper.ClassicalWeilFiniteDiagramDescent
import Sheaf.Paper.ClassicalWeilPrescribedIsomorphismLifts
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # Simultaneous normalized realization of finite classical Weil diagrams -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
universe u v w z
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Endofunctor (IsoAlgebra)
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open AlgebraicallyClosedCoefficients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]

variable [Fact (∀ x : (D.geometricFiber Y₀).left,
  IsUnit (l : (D.geometricFiber Y₀).left.presheaf.stalk x))]

private theorem common_lisse_of_iso
    {X : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
    {K L : generalAlgebraicallyClosedConstructibleCategory l Ω X} (i : K ≅ L)
    (h : IsCommonStageLisse l Ω X K) : IsCommonStageLisse l Ω X L := by
  obtain ⟨I, V, a, hc, hV⟩ := h
  refine ⟨I, V, a, hc, ?_⟩
  intro j
  obtain ⟨hj, E, r, M, hM, ⟨e⟩⟩ := hV j
  exact ⟨hj, E, r, M, hM,
    ⟨(@commonStageDerivedPullback l _ Ω _ _ _ _ _ (V j).hom hj _).mapIso i.symm ≪≫ e⟩⟩

private theorem common_lisse_of_finite
    {X : Scheme.{u}} [hX : ∀ x : X, Invertible (l : X.residueField x)]
    (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X)
    (hK : IsRationalLisse l (Coefficient.{u} l Ω E) X K) :
    IsCommonStageLisse l Ω X
      ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K) := by
  obtain ⟨I, V, a, hc, hV⟩ := hK
  refine ⟨I, V, a, hc, ?_⟩
  intro j
  obtain ⟨hj, r, M, hM, ⟨e⟩⟩ := hV j
  refine ⟨hj, E, r, M, hM, ⟨?_⟩⟩
  exact eqToIso ((@commonStageDerivedPullback_existsUnique l _ Ω _ _ _ _ _
    (V j).hom hj hX).exists.choose_spec.1 _) ≪≫
      (GeneralAlgebraicallyClosedCoefficients.inclusion E).mapIso e

private theorem map_signed_list {α G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (φ : G →+ H) (g : α → G) (h : α → H) (hg : ∀ a, φ (g a) = h a)
    (q : List (ℤ × α)) :
    φ ((q.map (fun a ↦ a.1 • g a.2)).sum) =
      (q.map (fun a ↦ a.1 • h a.2)).sum := by
  induction q with
  | nil => exact φ.map_zero
  | cons a q ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [φ.map_add, φ.map_zsmul, hg, ih]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem finite_expression_value
    {R : ZlClassicalRealization D l hl Ω Y₀}
    {E : Padic.FiniteCoefficientFields l Ω} (P : ZlDiagramStage D l hl Ω Y₀ R E)
    {I : Type v} {A : Type w} {s t : A → I}
    (N : I → P.Weil D l hl Ω Y₀) (b : ∀ j : A, N (s j) ⟶ N (t j))
    {x y : I × ℕ} (e f : ZlWeilExpression s t x y)
    (heq : zlExpressionValue P.operation.raw N b (ObjectProperty.ι _) e =
      zlExpressionValue P.operation.raw N b (ObjectProperty.ι _) f) :
    zlExpressionValue P.operation.raw N b P.finite e =
      zlExpressionValue P.operation.raw N b P.finite f := by
  let X := zlWordObject P.operation.raw N x.1 x.2
  let Y := zlWordObject P.operation.raw N y.1 y.2
  let φ : (X.obj ⟶ Y.obj) →+ (P.finite.obj X ⟶ P.finite.obj Y) :=
    AddMonoidHom.mk' (fun g ↦ P.finite.map ⟨g⟩)
      (fun g h ↦ P.finite_add X Y ⟨g⟩ ⟨h⟩)
  have hv (q : ZlWeilExpression s t x y) :
      φ (zlExpressionValue P.operation.raw N b (ObjectProperty.ι _) q) =
        zlExpressionValue P.operation.raw N b P.finite q := by
    exact map_signed_list φ
      (fun w ↦ (ObjectProperty.ι _).map (w.eval P.operation.raw N b))
      (fun w ↦ P.finite.map (w.eval P.operation.raw N b)) (fun _ ↦ rfl) q
  exact (hv e).symm.trans ((congrArg φ heq).trans (hv f))

set_option linter.unusedSectionVars false in
/-- Simultaneous finite-stage descent, normalized free towers and heart realization.
The finite equations are imposed before coefficient extension. The conclusion's stage
witness includes the inverse-limit module realization, rational Hom normalization,
actual Frobenius pullbacks and their ordinary and finite-level unit squares.
R is an arbitrary input datum, not a realization selected by this theorem; every
stage and prescribed-object lift in the conclusion uses that same R.

Source: Bhatt--Scholze, Propositions 6.8.4(1),(4), 6.8.14(2), Remark 6.8.15;
Weil II (1.1.1)b--d; Stanford Weil II seminar L19, Proposition 1.1.9.
(blueprint: lem-zl-classical-finite-weil-diagram-realization).

Proof plan:
1. Fix the supplied normalized realization R throughout. Finite-type base change
makes Y separated, noetherian and finite dimensional, with l invertible. Its finitely
many irreducible components, grouped by chains of intersections, give finitely many
connected clopen components. Frobenius need not fix them. Choose lattices componentwise
and assemble by finite products of sheaves.
2. Take the compositum of the finitely many fields of definition of vertices. Enlarge
for the arrows, Weil maps and their inverses, with their actual pullback sources.
Each of the finitely many word equations, inverse identities and equivariance squares
holds after a further finite enlargement, by the directed Hom-colimit description.
3. On each connected component the classical lisse dictionary identifies each model
with a continuous finite-dimensional representation of a profinite group. Its compact
image preserves a finite free integral lattice. Reductions give normalized finite free
towers N_n; assemble over clopen components. Arrows remain rational: no preservation
of these integral lattices by arrows, Weil maps or their inverses is required.
4. The inverse limit of the pro-etale pullbacks of N_n is the completed lisse module.
BS 6.8.4 and the raw-system realization put its rationalization in the actual sf heart.
The scalar-extension Hom formula sends f tensor a to a(1 tensor f), so it realizes
all chosen rational arrows, and the inverse Hom bijection lifts them uniquely.
5. Apply the normalized lisse pullback comparison to geometric Frobenius, which is
allowed to be non-k-linear. The completed-system comparison uses the same finite-level
reindexing. The sf/PBC coefficient comparison preserves the full reduction tower.
6. Coefficient comparisons are fixed pointwise by Shrink. At every finite reduction,
both units send m to 1 tensor m and reindex it to the same section. On completed local
bases both ordinary and completed pullback comparisons send a basis vector to that
same tensor. The normalized ordinary-unit and finite-unit squares therefore commute.
For each E, start with R.pullback_pinning E, keeping its finite functor, finite
pullback, stage isomorphism and pinning. Choose one normalized Family from the lisse
realization theorem. Its completion and localization maps agree with those of the
witness by their quotient and unit normalizations. The integral comparison and
fraction rule give a natural module isomorphism between the two sheaf realizations.
Transport the witness's sheaf comparison along it, taking realization and Along
from the chosen Family. PullNormalized fixes both ordinary pullback comparisons
on integral tensors; additivity and localization extend that equality to rational
lisse maps. Thus ordinary_unit is preserved; finite_unit and pinning are unchanged.
Full faithfulness follows from the completed rational Hom bijection, sheaf_linear
and the lisse-heart Hom bijection; faithfulness and the same fraction rule give
finite_add. The raw pullback's map rule and finite_unit give the classical natural
isomorphism with values eqToHom. This supplies all ZlDiagramStage fields for the
original R, without changing its functor or its Frobenius comparison.
7. Lift each Weil map and its inverse and compose with that comparison. Faithfulness
shows that the lifted maps are inverse. Its naturality lifts every equivariance square.
This is exactly the IsoAlgebra construction on the actual sf pullback.
8. Rational realization is additive by its Hom formula, hence preserves all finite
signed sums of composite words. Naturality handles pullback symbols, identities and
composition. Faithfulness lifts equations. The coefficient-change comparisons have
their prescribed unit and associativity equations, so all constructions agree under
finite extension and pass to the directed Hom colimit at Omega.
9. The fully faithful realization of lisse hearts lifts a prescribed compatible
identification and its inverse uniquely. Faithfulness proves both inverse identities
and Weil compatibility. For rank zero use the zero lattice; an empty diagram has the
base coefficient field. Empty Y uses its zero sheaves. Thus no nonemptiness, positive
rank, connectedness or componentwise Frobenius-fixity assumption is needed. -/
theorem classical_finite_weil_diagram_realization
    (I : Type v) [Finite I] (A : Type w) [Finite A] (s t : A → I)
    (J : Type z) [Finite J] (x y : J → I × ℕ)
    (e f : ∀ j : J, ZlWeilExpression s t (x j) (y j)) :
    letI := zlDiagramUnits D l hl Y₀
    ∀ (R : ZlClassicalRealization D l hl Ω Y₀)
      (M : I → ZlClassicalWeil D l Ω Y₀) (a : ∀ j : A, M (s j) ⟶ M (t j)),
      (∀ j : J, zlClassicalEquation D l Ω Y₀ M a (e j) (f j)) →
    ∃ P₀ : ∀ E : Padic.FiniteCoefficientFields l Ω, ZlDiagramStage D l hl Ω Y₀ R E,
    ∃ E : Padic.FiniteCoefficientFields l Ω,
    let P := P₀ E
    ∃ N : I → P.Weil D l hl Ω Y₀,
    ∃ b : ∀ j : A, N (s j) ⟶ N (t j),
    ∃ β : ∀ i : I, (P.classicalWeil D l hl Ω Y₀).obj (N i) ≅ M i,
      (∀ j : A, (P.classicalWeil D l hl Ω Y₀).map (b j) ≫ (β (t j)).hom =
        (β (s j)).hom ≫ a j) ∧
      (∀ j : J,
        zlExpressionValue P.operation.raw N b (ObjectProperty.ι _) (e j) =
          zlExpressionValue P.operation.raw N b (ObjectProperty.ι _) (f j)) ∧
      (∀ j : J,
        zlExpressionValue P.operation.raw N b P.finite (e j) =
          zlExpressionValue P.operation.raw N b P.finite (f j)) ∧
      Finite (_root_.ConnectedComponents (D.geometricFiber Y₀).left) ∧
      (∀ y : (D.geometricFiber Y₀).left, IsClopen (connectedComponent y)) ∧
      (∀ i : I, LisseRealization.Lisse D l hl (Coefficient.{u} l Ω E)
        (zlRealizationBase D l hl Y₀) (P.finite.obj (N i).carrier)) ∧
      (∀ i : I, IsCommonStageLisse l Ω (D.geometricFiber Y₀).left
        (R.functor.obj (M i).carrier)) ∧
      ZlDiagramCoefficientCoherence D l hl Ω Y₀ R P₀ ∧
      (∀ i : I, ZlPrescribedWeilLifts D l hl Ω Y₀ R (M i)) := by
  let := zlDiagramUnits D l hl Y₀
  intro R M a h
  obtain ⟨P₀, hcoh⟩ := zl_coherent_normalized_diagram_stages D l hl Ω Y₀ R
  obtain ⟨E, N, b, β, harrow, hraw⟩ :=
    zl_finite_weil_diagram_descent D l hl Ω Y₀ R P₀ I A s t J x y e f M a h
  refine ⟨P₀, E, N, b, β, harrow, hraw, ?_, inferInstance, ?_, ?_, ?_, hcoh, ?_⟩
  · intro j
    exact finite_expression_value D l hl Ω Y₀ (P₀ E) N b (e j) (f j) (hraw j)
  · intro y
    exact isClopen_connectedComponent
  · intro i
    exact (P₀ E).lisse (N i).carrier
  · intro i
    let γ : (GeneralAlgebraicallyClosedCoefficients.inclusion E).obj
        ((P₀ E).finite.obj (N i).carrier) ≅ R.functor.obj (M i).carrier :=
      ((P₀ E).stage.app (N i).carrier).symm ≪≫
        R.functor.mapIso ((IsoAlgebra.forget
          (lisseAlgebraicAutomorphismPullback (D.geometricFrobenius Y₀) l Ω)).mapIso (β i))
    exact common_lisse_of_iso l Ω γ
      (common_lisse_of_finite l Ω E _ ((P₀ E).lisse (N i).carrier).2)
  · intro i
    exact zl_prescribed_weil_isomorphism_lifts D l hl Ω Y₀ R (M i)

end WeilConjectures
