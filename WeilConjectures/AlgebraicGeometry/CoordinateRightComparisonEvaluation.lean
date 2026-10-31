/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoordinateFoundations
import WeilConjectures.AlgebraicGeometry.SemilinearEvaluationLocalization

/-! # Finite evaluation of coordinate right comparisons

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-tower-geometric/
`sk-prop-sp-tower-geometric-gluing.proof.md`, Local pairs and Levels
(blueprint: lem-sp-coordinate-right-comparison-evaluation).
-/

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpCoordinateAdjunction

@[expose] public noncomputable section
set_option autoImplicit false

universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The system-coordinate rho for a projection. This is the shift, tensor, and pullback
part of `projectionEvaluation`; its outer `levelComparison` and `rightRealization`
arrows are removed when working in system coordinates. Source: Local pairs and Levels
(blueprint: lem-sp-coordinate-right-comparison-evaluation). -/
def projectionSystemEvaluation (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) {T Y : Scheme.{u}} (p : T ⟶ Y)
    (w : SpChartAdmissibility.Twists l E T) (d n : ℕ) (K : SpTowerShriek.D l E Y) :
    (SpTowerShriek.Ev l E T n).obj ((projectionRight l E b o p w d).obj K) ≅
      (finiteProjectionRight l E b p w d n).obj ((SpTowerShriek.Ev l E Y n).obj K) :=
  ((SpTowerShriek.Ev l E T n).commShiftIso (2 * (d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      (((b.calculus T).tensorEvaluation n).app
        ((SpTowerShriek.pull l E b (o.geometry p)).obj K, line l E w d) ≪≫
        ((b.calculus T).levelClosed n).tensor.mapIso
          (Iso.prod (((o.geometry p).pullEvaluation n).app K) (Iso.refl _)))

/-- The system-coordinate rho for the actual projective right factor restricted along
j. The source comparison is the supplied `finiteMaps.comparison`, pasted after the
canonical `pullEvaluation` for j. Source: Local pairs and Levels
(blueprint: lem-sp-coordinate-right-comparison-evaluation). -/
def affineSystemEvaluation {b : SpTowerShriek.Base l E}
    {o : SpTowerShriek.Operations l E b} {Y : Scheme.{u}}
    (t : ProjectivePresentation l E b o Y) (n : ℕ) (K : SpTowerShriek.D l E Y) :
    (SpTowerShriek.Ev l E (space Y 1) n).obj
      ((SpTowerShriek.pull l E b (o.geometry (ProjectiveLine.affineChart Y))).obj
        ((t.presentation.G l E).obj K)) ≅
      (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n)
        (ProjectiveLine.affineChart Y)).obj
        ((SpTowerP1.finiteG l E t.presentation n).obj ((SpTowerShriek.Ev l E Y n).obj K)) :=
  ((o.geometry (ProjectiveLine.affineChart Y)).pullEvaluation n).app
      ((t.presentation.G l E).obj K) ≪≫
    (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n)
      (ProjectiveLine.affineChart Y)).mapIso ((t.adjunction.finiteMaps n).comparison.app K)

/-- The system-coordinate rho for the ordered pair of projection right functors.
It first evaluates the outer one-step factor and then maps the inner projection rho
through the finite outer factor. Source: ordered right factors, Levels
(blueprint: lem-sp-coordinate-right-comparison-evaluation). -/
def stepSystemEvaluation (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) {k : Type u} [Field k]
    (w : _) (Y : Bases k) (d n : ℕ)
    (K : SpTowerShriek.D l E Y.val.left) :=
  -- Infer the family domain from the coordinate API, including its ground-field scope.
  let _ := fun (q : SpTowerCalculus.Coordinates l E b) ↦ Foundations l E k b o q w;
  projectionSystemEvaluation l E b o
      (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
      (w (space Y.val.left (d + 1))) 1 n
      ((projectionRight l E b o (proj Y.val.left d) (w (space Y.val.left d)) d).obj K) ≪≫
    (finiteProjectionRight l E b
      (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
      (w (space Y.val.left (d + 1))) 1 n).mapIso
      (projectionSystemEvaluation l E b o (proj Y.val.left d) (w (space Y.val.left d)) d n K)

/-- The affine evaluation identity for the specified finite comparison on all ambient
system objects. Source: first displayed identity, Local pairs and Levels
(blueprint: lem-sp-coordinate-right-comparison-evaluation). -/
def AffineEvaluationIdentity {k : Type u} [Field k] (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : SpTowerCalculus.Coordinates l E b)
    (w : _) (a : Foundations l E k b o q w) (Y : Bases k) (n : ℕ)
    (A : SpTowerP1.finiteG l E (a.projective Y).presentation n ⋙
      proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n)
        (ProjectiveLine.affineChart Y.val.left) ≅
      finiteProjectionRight l E b (proj Y.val.left 1) (w (space Y.val.left 1)) 1 n) : Prop :=
  ∀ K : SpTowerShriek.D l E Y.val.left,
    (SpTowerShriek.Ev l E (space Y.val.left 1) n).map
        ((a.affine Y).comparison.hom.app K) ≫
      (projectionSystemEvaluation l E b o (proj Y.val.left 1)
        (w (space Y.val.left 1)) 1 n K).hom =
    (affineSystemEvaluation l E (a.projective Y) n K).hom ≫
      A.hom.app ((SpTowerShriek.Ev l E Y.val.left n).obj K)

/-- The successor evaluation identity for the specified ordered finite comparison.
Source: second displayed identity, ordered right factors and Levels
(blueprint: lem-sp-coordinate-right-comparison-evaluation). -/
def StepEvaluationIdentity {k : Type u} [Field k] (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : SpTowerCalculus.Coordinates l E b)
    (w : _) (a : Foundations l E k b o q w) (Y : Bases k) (d n : ℕ)
    (B : finiteProjectionRight l E b (proj Y.val.left d) (w (space Y.val.left d)) d n ⋙
      finiteProjectionRight l E b
        (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
        (w (space Y.val.left (d + 1))) 1 n ≅
      finiteProjectionRight l E b (proj Y.val.left (d + 1))
        (w (space Y.val.left (d + 1))) (d + 1) n) : Prop :=
  ∀ K : SpTowerShriek.D l E Y.val.left,
    (SpTowerShriek.Ev l E (space Y.val.left (d + 1)) n).map ((a.step Y d).hom.app K) ≫
      (projectionSystemEvaluation l E b o (proj Y.val.left (d + 1))
        (w (space Y.val.left (d + 1))) (d + 1) n K).hom =
    (stepSystemEvaluation l E b o w Y d n K).hom ≫
      B.hom.app ((SpTowerShriek.Ev l E Y.val.left n).obj K)

/-- The zero evaluation identity, in the direction from the identity to the finite
zero-coordinate right functor. Source: third displayed identity, Local pairs and Levels
(blueprint: lem-sp-coordinate-right-comparison-evaluation). -/
def ZeroEvaluationIdentity {k : Type u} [Field k] (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : SpTowerCalculus.Coordinates l E b)
    (w : _) (a : Foundations l E k b o q w) (Y : Bases k) (n : ℕ)
    (Z : 𝟭 (proEtaleDerivedCategory Y.val.left (SpTowerShriek.R l E n)) ≅
      finiteProjectionRight l E b (𝟙 Y.val.left) (w Y.val.left) 0 n) : Prop :=
  ∀ K : SpTowerShriek.D l E Y.val.left,
    (SpTowerShriek.Ev l E Y.val.left n).map ((a.zero Y).hom.app K) ≫
      (projectionSystemEvaluation l E b o (𝟙 Y.val.left) (w Y.val.left) 0 n K).hom =
    Z.hom.app ((SpTowerShriek.Ev l E Y.val.left n).obj K)

/-- The finite affine, ordered successor and zero comparisons and their three
commuting evaluation squares. The `specified` fields pin each finite natural
isomorphism uniquely by the normalized tower word in `a` and the canonical rho maps.
Thus these are precisely the finite root-section affine comparison, the finite
pullback-composition/tensor-associator/Tate-product/total-shift comparison, and the
finite identity-pullback/scalar-unit/shift-zero comparison. The isomorphisms act on
entire finite derived categories. Source: Local pairs and Levels
(blueprint: lem-sp-coordinate-right-comparison-evaluation). -/
structure RightComparisonEvaluation (pchar : ℕ) (k : Type u) [Field k]
    [Fact pchar.Prime] [CharP k pchar] (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : SpTowerCalculus.Coordinates l E b)
    (w : _) (a : Foundations l E k b o q w) where
  affine : ∀ (Y : Bases k) (n : ℕ),
    SpTowerP1.finiteG l E (a.projective Y).presentation n ⋙
      proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n)
        (ProjectiveLine.affineChart Y.val.left) ≅
      finiteProjectionRight l E b (proj Y.val.left 1) (w (space Y.val.left 1)) 1 n
  affine_evaluation : ∀ (Y : Bases k) (n : ℕ),
    AffineEvaluationIdentity l E b o q w a Y n (affine Y n)
  affine_specified : ∀ (Y : Bases k) (n : ℕ)
    (A : SpTowerP1.finiteG l E (a.projective Y).presentation n ⋙
      proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n)
        (ProjectiveLine.affineChart Y.val.left) ≅
      finiteProjectionRight l E b (proj Y.val.left 1) (w (space Y.val.left 1)) 1 n),
    AffineEvaluationIdentity l E b o q w a Y n A → A = affine Y n
  step : ∀ (Y : Bases k) (d n : ℕ),
    finiteProjectionRight l E b (proj Y.val.left d) (w (space Y.val.left d)) d n ⋙
      finiteProjectionRight l E b
        (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
        (w (space Y.val.left (d + 1))) 1 n ≅
      finiteProjectionRight l E b (proj Y.val.left (d + 1))
        (w (space Y.val.left (d + 1))) (d + 1) n
  step_evaluation : ∀ (Y : Bases k) (d n : ℕ),
    StepEvaluationIdentity l E b o q w a Y d n (step Y d n)
  step_specified : ∀ (Y : Bases k) (d n : ℕ)
    (B : finiteProjectionRight l E b (proj Y.val.left d) (w (space Y.val.left d)) d n ⋙
      finiteProjectionRight l E b
        (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
        (w (space Y.val.left (d + 1))) 1 n ≅
      finiteProjectionRight l E b (proj Y.val.left (d + 1))
        (w (space Y.val.left (d + 1))) (d + 1) n),
    StepEvaluationIdentity l E b o q w a Y d n B → B = step Y d n
  zero : ∀ (Y : Bases k) (n : ℕ),
    𝟭 (proEtaleDerivedCategory Y.val.left (SpTowerShriek.R l E n)) ≅
      finiteProjectionRight l E b (𝟙 Y.val.left) (w Y.val.left) 0 n
  zero_evaluation : ∀ (Y : Bases k) (n : ℕ),
    ZeroEvaluationIdentity l E b o q w a Y n (zero Y n)
  zero_specified : ∀ (Y : Bases k) (n : ℕ)
    (Z : 𝟭 (proEtaleDerivedCategory Y.val.left (SpTowerShriek.R l E n)) ≅
      finiteProjectionRight l E b (𝟙 Y.val.left) (w Y.val.left) 0 n),
    ZeroEvaluationIdentity l E b o q w a Y n Z → Z = zero Y n

private def projectionEvaluationIso (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) {T Y : Scheme.{u}} (p : T ⟶ Y)
    (w : SpChartAdmissibility.Twists l E T) (d n : ℕ) :
    projectionRight l E b o p w d ⋙ SpTowerShriek.Ev l E T n ≅
      SpTowerShriek.Ev l E Y n ⋙ finiteProjectionRight l E b p w d n := by
  let P := SpTowerShriek.pull l E b (o.geometry p)
  let V := SpTowerShriek.Ev l E T n
  let L := line l E w d
  let U := SpTowerShriek.tensor l E b T
  let W := ((b.calculus T).levelClosed n).tensor
  let z : ℤ := 2 * (d : ℤ)
  let h : P ⋙ Prod.sectL (SpTowerShriek.D l E T) L ⋙ V.prod V ≅
      SpTowerShriek.Ev l E Y n ⋙
        proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) p ⋙
          Prod.sectL (proEtaleDerivedCategory T (SpTowerShriek.R l E n)) (V.obj L) :=
    NatIso.ofComponents
      (fun K ↦ Iso.prod (((o.geometry p).pullEvaluation n).app K) (Iso.refl _)) (by
        intro K K' f
        apply CategoryTheory.Prod.hom_ext
        · exact ((o.geometry p).pullEvaluation n).hom.naturality f
        · change V.map (𝟙 L) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
          simp)
  exact Functor.isoWhiskerLeft (P ⋙ Prod.sectL (SpTowerShriek.D l E T) L ⋙ U)
      (V.commShiftIso z) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (P ⋙ Prod.sectL (SpTowerShriek.D l E T) L)
        ((b.calculus T).tensorEvaluation n)) (shiftFunctor _ z) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight h W) (shiftFunctor _ z)

private theorem projectionEvaluationIso_app (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) {T Y : Scheme.{u}} (p : T ⟶ Y)
    (w : SpChartAdmissibility.Twists l E T) (d n : ℕ) (K : SpTowerShriek.D l E Y) :
    (projectionEvaluationIso l E b o p w d n).hom.app K =
      (projectionSystemEvaluation l E b o p w d n K).hom := by
  simp [projectionEvaluationIso, projectionSystemEvaluation, Prod.sectL]

private def affineEvaluationIso {b : SpTowerShriek.Base l E}
    {o : SpTowerShriek.Operations l E b} {Y : Scheme.{u}}
    (t : ProjectivePresentation l E b o Y) (n : ℕ) :
    (t.presentation.G l E ⋙
      SpTowerShriek.pull l E b (o.geometry (ProjectiveLine.affineChart Y))) ⋙
        SpTowerShriek.Ev l E (space Y 1) n ≅
    SpTowerShriek.Ev l E Y n ⋙ (SpTowerP1.finiteG l E t.presentation n ⋙
      proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n)
        (ProjectiveLine.affineChart Y)) :=
  Functor.isoWhiskerLeft (t.presentation.G l E)
      ((o.geometry (ProjectiveLine.affineChart Y)).pullEvaluation n) ≪≫
    Functor.isoWhiskerRight (t.adjunction.finiteMaps n).comparison
      (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n)
        (ProjectiveLine.affineChart Y))

private def stepEvaluationIso (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) {k : Type u} [Field k]
    (w : _) (Y : Bases k) (d n : ℕ) :
    let _ := stepSystemEvaluation l E b o w Y d n;
    (projectionRight l E b o (proj Y.val.left d) (w (space Y.val.left d)) d ⋙
      projectionRight l E b o
        (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
        (w (space Y.val.left (d + 1))) 1) ⋙
      SpTowerShriek.Ev l E (space Y.val.left (d + 1)) n ≅
    SpTowerShriek.Ev l E Y.val.left n ⋙
      (finiteProjectionRight l E b (proj Y.val.left d) (w (space Y.val.left d)) d n ⋙
        finiteProjectionRight l E b
          (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
          (w (space Y.val.left (d + 1))) 1 n) :=
  Functor.isoWhiskerLeft
      (projectionRight l E b o (proj Y.val.left d) (w (space Y.val.left d)) d)
      (projectionEvaluationIso l E b o
        (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
        (w (space Y.val.left (d + 1))) 1 n) ≪≫
    Functor.isoWhiskerRight
      (projectionEvaluationIso l E b o (proj Y.val.left d) (w (space Y.val.left d)) d n)
      (finiteProjectionRight l E b
        (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
        (w (space Y.val.left (d + 1))) 1 n)

private theorem descendIso
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    (V : C ⥤ D) (W : A ⥤ B)
    (ff : ((Functor.whiskeringLeft C D B).obj V).FullyFaithful)
    {F G : C ⥤ A} {F' G' : D ⥤ B}
    (r : F ⋙ W ≅ V ⋙ F') (s : G ⋙ W ≅ V ⋙ G') (t : F ≅ G) :
    ∃ x : F' ≅ G',
      (∀ K, W.map (t.hom.app K) ≫ s.hom.app K =
        r.hom.app K ≫ x.hom.app (V.obj K)) ∧
      (∀ y : F' ≅ G', (∀ K, W.map (t.hom.app K) ≫ s.hom.app K =
        r.hom.app K ≫ y.hom.app (V.obj K)) → y = x) := by
  let z := r.symm ≪≫ Functor.isoWhiskerRight t W ≪≫ s
  let x := ff.preimageIso z
  have hx (K : C) : x.hom.app (V.obj K) = z.hom.app K :=
    congrArg (fun f ↦ f.app K) (ff.map_preimage z.hom)
  refine ⟨x, ?_, ?_⟩
  · intro K
    rw [hx]
    simp [z]
  · intro y hy
    apply Iso.ext
    apply ff.map_injective
    ext K
    change y.hom.app (V.obj K) = x.hom.app (V.obj K)
    rw [hx]
    apply (cancel_epi (r.hom.app K)).1
    simpa [z] using (hy K).symm

/-- The specified finite right-functor comparisons and all three evaluation identities.
Source: latest blueprint, Local pairs and Levels
(blueprint: lem-sp-coordinate-right-comparison-evaluation).

Proof. Evaluation at a fixed level is a localization: its exact coinduced right
adjoint is fully faithful, before and after passage to the unbounded derived
categories. Therefore precomposition with evaluation is fully faithful on functor
categories. Package the displayed projection rho maps as a natural isomorphism,
using shift evaluation, tensor evaluation and pull evaluation in that order.
The affine and ordered-source rho maps are the corresponding pastings.
Conjugate each of the three given natural tower comparisons by its source and
target rho maps. Fully faithful precomposition gives a unique finite natural
isomorphism inducing this conjugate. Its map-preimage equation, after cancellation
of the source rho and its inverse, is precisely the required evaluation equation.
Faithfulness gives each specified-uniqueness clause. Apply this construction to
`a.affine.comparison`, `a.step` and `a.zero`; the identity source rho in the last
case gives exactly the stated direction of the zero comparison. This defines
maps on the entire finite categories and requires no chosen tower lifts. -/
theorem coordinate_right_comparison_evaluation
    (pchar : ℕ) (k : Type u) [Field k] [Fact pchar.Prime] [CharP k pchar]
    (_hl : l ≠ pchar) (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : SpTowerCalculus.Coordinates l E b)
    (w : _) (a : Foundations l E k b o q w) :
    Nonempty (RightComparisonEvaluation l E pchar k b o q w a) := by
  classical
  have hloc (T : Scheme.{u}) (n : ℕ) :=
    SemilinearSections.evaluation_isLocalization
      (Scheme.ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) n
  have ha (Y : Bases k) (n : ℕ) := by
    have := hloc Y.val.left n
    exact descendIso (SpTowerShriek.Ev l E Y.val.left n)
      (SpTowerShriek.Ev l E (space Y.val.left 1) n)
      (Localization.fullyFaithfulWhiskeringLeft _
        ((MorphismProperty.isomorphisms _).inverseImage
          (SpTowerShriek.Ev l E Y.val.left n)) _)
      (affineEvaluationIso l E (a.projective Y) n)
      (projectionEvaluationIso l E b o (proj Y.val.left 1)
        (w (space Y.val.left 1)) 1 n) (a.affine Y).comparison
  have hb (Y : Bases k) (d n : ℕ) := by
    have := hloc Y.val.left n
    exact descendIso (SpTowerShriek.Ev l E Y.val.left n)
      (SpTowerShriek.Ev l E (space Y.val.left (d + 1)) n)
      (Localization.fullyFaithfulWhiskeringLeft _
        ((MorphismProperty.isomorphisms _).inverseImage
          (SpTowerShriek.Ev l E Y.val.left n)) _)
      (stepEvaluationIso l E b o w Y d n)
      (projectionEvaluationIso l E b o (proj Y.val.left (d + 1))
        (w (space Y.val.left (d + 1))) (d + 1) n) (a.step Y d)
  have hz (Y : Bases k) (n : ℕ) := by
    have := hloc Y.val.left n
    exact descendIso (F' := 𝟭 (proEtaleDerivedCategory Y.val.left (SpTowerShriek.R l E n)))
      (SpTowerShriek.Ev l E Y.val.left n) (SpTowerShriek.Ev l E Y.val.left n)
      (Localization.fullyFaithfulWhiskeringLeft _
        ((MorphismProperty.isomorphisms _).inverseImage
          (SpTowerShriek.Ev l E Y.val.left n)) _) (Iso.refl _)
      (projectionEvaluationIso l E b o (𝟙 Y.val.left) (w Y.val.left) 0 n) (a.zero Y)
  choose A hA using ha
  choose B hB using hb
  choose Z hZ using hz
  refine ⟨{
    affine := A
    affine_evaluation := ?_
    affine_specified := ?_
    step := B
    step_evaluation := ?_
    step_specified := ?_
    zero := Z
    zero_evaluation := ?_
    zero_specified := ?_ }⟩
  · intro Y n K
    simpa [projectionEvaluationIso_app, affineEvaluationIso, affineSystemEvaluation]
      using (hA Y n).1 K
  · intro Y n A' h
    apply (hA Y n).2 A'
    intro K
    simpa [projectionEvaluationIso_app, affineEvaluationIso, affineSystemEvaluation]
      using h K
  · intro Y d n K
    simpa [stepEvaluationIso, stepSystemEvaluation, projectionEvaluationIso_app,
      Functor.map_comp] using (hB Y d n).1 K
  · intro Y d n B' h
    apply (hB Y d n).2 B'
    intro K
    simpa [stepEvaluationIso, stepSystemEvaluation, projectionEvaluationIso_app,
      Functor.map_comp] using h K
  · intro Y n K
    simpa [projectionEvaluationIso_app] using (hZ Y n).1 K
  · intro Y n Z' h
    apply (hZ Y n).2 Z'
    intro K
    simpa [projectionEvaluationIso_app] using h K

end

end AlgebraicGeometry.ProEtale.SpCoordinateAdjunction
