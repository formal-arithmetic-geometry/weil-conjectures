/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.SixFunctors.CoefQbarVerdierData
import Sheaf.SixFunctors.RationalHomIdentifications
import Sheaf.SixFunctors.RationalVerdier
import Sheaf.Paper.IntrinsicQbarCategory
import Sheaf.CategoryTheory.StageSystemOpposite

/-! # Descent of finite-origin Verdier duality and evaluation

Source: blueprint thm-coef-qbar-verdier, proof steps 1--4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] WeilConjectures.CoefQbarTensor
  WeilConjectures.CoefQbarPullback

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CoefQbarVerdier
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition associator unitor)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

omit [IsAlgClosure (Padic l) Ω] in
/-- Simultaneous finite data from rational Verdier duality and finite Hom identification.
Source: blueprint thm-coef-qbar-verdier, proof steps 1 and 5
(blueprint: lem-coef-qbar-verdier-core-descent).

Proof: apply the simultaneous rational duality theorem. Choose integral dualizing
presentations at each finite coefficient field, specialize its duality and scalar
families, and use the finite Hom-identification theorem for each identity field map.
The normalized scalar comparisons themselves supply beta, so betaNormalized is reflexive. -/
theorem finite_data_exists : Nonempty (Finite D l hl Ω X) := by
  classical
  obtain ⟨d, s, hs, _, _⟩ := coef_rational_verdier D l hl X
  let w := fun E : Index l Ω ↦ Classical.choice
    (IntegralFiniteExtension.dualizingDatum_nonempty l X D hl (Coefficient.{u} l Ω E))
  let a := fun E : Index l Ω ↦ d (Coefficient.{u} l Ω E) (w E)
  let e := fun (E L : Index l Ω) (h : E ≤ L) ↦
    s (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) (w E) (w L)
  have H (E : Index l Ω) : Nonempty
      (RationalOperations.HomIdentification l (Coefficient.{u} l Ω E) X D hl (w E) (a E)) := by
    obtain ⟨h, _, _⟩ := RationalOperations.rationalHom_identifications
      D l hl X (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω E)
      (AlgHom.id (Padic l) (Coefficient.{u} l Ω E)) (w E) (w E) (a E) (a E)
    exact ⟨h⟩
  refine ⟨{ omega := w, datum := a, hom := fun E ↦ Classical.choice (H E)
            scalar := e, normalized := ?_, beta := ?_, betaNormalized := ?_ }⟩
  · intro E L h
    exact hs (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) (w E) (w L)
  · intro E L h
    exact (e E L h).comparison
  · intro E L h
    exact HEq.rfl


/-- The finite-origin equations for duality and evaluation, before their formal
restriction to split retracts. All data and maps are those of DualityData.
Source: blueprint thm-coef-qbar-verdier, proof steps 1--4
(blueprint: lem-coef-qbar-verdier-core-descent). -/
def CoreProperties (B : DualityData D l hl Ω X) : Prop :=
  (fun [_linearInst : Linear Ω (generalAlgebraicallyClosedConstructibleCategory l Ω X)] ↦
  (FiniteCoherent D l hl Ω X B.finite) ∧
  B.duality.dual.Additive ∧
  (∀ (E : Index l Ω)
      (K M : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X) (f : K ⟶ M)
      (c : Coefficient.{u} l Ω E),
    (inclusion (Y := X) E).map
      ((sfRationalCoefficientEquiv l (Coefficient.{u} l Ω E)).symm c •
        (f : (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X) ⟶ M)) =
      ((Shrink.algEquiv (Padic l) E.val c : E.val) : Ω) • (inclusion (Y := X) E).map f) ∧
  (∀ (K M : generalAlgebraicallyClosedConstructibleCategory l Ω X)
      (f : K ⟶ M) (c : Ω),
    B.duality.dual.map (c • f).op = c • B.duality.dual.map f.op) ∧
  (∀ (E : Index l Ω) (K : Stage l Ω X E),
    B.duality.dual.obj (op ((inclusion (Y := X) E).obj K)) =
      (inclusion (Y := X) E).obj ((B.finite.datum E).dual.obj (op K))) ∧
  (∀ (E : Index l Ω) (K : Stage l Ω X E),
    HEq ((B.comparison E).hom.app (op K))
      (𝟙 ((inclusion (Y := X) E).obj ((B.finite.datum E).dual.obj (op K))))) ∧
  (∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E),
    (inclusion (Y := X) L).map ((B.finite.beta E L h).hom.app (op K)) ≫
      (B.comparison L).hom.app (op ((transition l Ω X E L h).obj K)) ≫
      B.duality.dual.map ((inclusionTransition l Ω X E L h).inv.app K).op =
    (inclusionTransition l Ω X E L h).hom.app ((B.finite.datum E).dual.obj (op K)) ≫
      (B.comparison E).hom.app (op K)) ∧
  (∀ (E : Index l Ω),
    SfClassEvaluationCompatible (inclusion (Y := X) E) (B.finite.datum E).dual B.duality.dual
      (B.finite.datum E).bidual.hom B.duality.bidual.hom (B.comparison E)) ∧
  (∀ (E L : Index l Ω) (h : E ≤ L),
    (inclusion (Y := X) L).map (B.finite.scalar E L h).omega.hom ≫ (B.omegaComparison L).hom =
      (inclusionTransition l Ω X E L h).hom.app
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
          (B.finite.omega E).omega) ≫ (B.omegaComparison E).hom) ∧
  (∀ (E : Index l Ω) (K : Stage l Ω X E),
    (tensorInclusion D l hl Ω X E K ((B.finite.datum E).dual.obj (op K))).hom ≫
      (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom (𝟙 ((inclusion (Y := X) E).obj K)) ((B.comparison E).hom.app (op K))) ≫
      B.evaluation ((inclusion (Y := X) E).obj K) =
    (inclusion (Y := X) E).map ((B.finite.datum E).evaluation K) ≫ (B.omegaComparison E).hom) ∧
  (∀ (K M : generalAlgebraicallyClosedConstructibleCategory l Ω X)
      (f : K ⟶ M),
    (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom f (𝟙 (B.duality.dual.obj (op M)))) ≫ B.evaluation M =
      (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom (𝟙 K) (B.duality.dual.map f.op)) ≫ B.evaluation K))
      (_linearInst := B.linearCategory)

/-- Coherent finite Verdier functors and their canonical evaluation descend to the
actual common-stage category, with its prescribed coefficient action.
Source: blueprint thm-coef-qbar-verdier, proof steps 1--4
(blueprint: lem-coef-qbar-verdier-core-descent).

Proof: choose coherent integral dualizing presentations and the simultaneous rational
Verdier data. Their normalized unit and tower equations give the finite beta equations.
Reverse representatives to identify the opposite-stage pair category with the opposite
pair category, and apply coherent pair-functor descent. A representative at L maps to
beta composed with the rational dual arrow and inverse beta at its other endpoint.
The tower equation proves independence of extension and representative. The resulting
object is literally the pair at the original stage, so the inclusion comparisons have
identity components. Use intrinsicQbarLinear, whose multiplication by c is computed
after a finite extension containing c and the representative; its finite-representative
formula and tower compatibility give the coefficient normalization. Finite linearity
gives additivity and Omega-linearity. Descend omega using the canonical u comparisons,
and descend evaluation and biduality using
the finite scalar squares. Finite biduality and its inverse are inverse on every
representative. The finite shift comparisons descend, and a distinguished triangle
has a finite-stage representative, proving exactness for the prescribed triangles.
The scalar, evaluation and biduality normalization equations are their finite-stage
squares, transported through the canonical inclusion-transition comparisons. Evaluation
naturality follows at a common stage from finite rational evaluation naturality. -/
theorem core_descent :
    ∃ B : DualityData D l hl Ω X, CoreProperties D l hl Ω X B := by
  sorry

/-- Naturality supplies all three split-retract equations without another descent
argument. Source: blueprint thm-coef-qbar-verdier, proof step 10
(blueprint: lem-coef-qbar-verdier-core-descent).

Proof: factor tensor(i,Dp) into tensor(i,1) followed by tensor(1,Dp).
Evaluation naturality for p replaces the second factor by tensor(p,1) followed by
evaluation at P. Functoriality and i composed with p equals identity cancel the
first factors. Naturality of biduality, and then of its inverse, proves the two
remaining equations by the same split equation. -/
theorem core_complete (B : DualityData D l hl Ω X)
    (hB : CoreProperties D l hl Ω X B) : DualityProperties D l hl Ω X B := by
  let := B.linearCategory
  rcases hB with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_, ?_, ?_⟩
  · intro P K i p h
    let T := CoefQbarTensor D l hl Ω X
    change T.map (Prod.mkHom i (B.duality.dual.map p.op)) ≫ B.evaluation K = _
    calc
      _ = T.map (Prod.mkHom i (𝟙 _)) ≫
          (T.map (Prod.mkHom (𝟙 K) (B.duality.dual.map p.op)) ≫ B.evaluation K) := by
        rw [← Category.assoc, ← T.map_comp]
        simp
      _ = T.map (Prod.mkHom i (𝟙 _)) ≫
          (T.map (Prod.mkHom p (𝟙 _)) ≫ B.evaluation P) := by rw [← h11 K P p]
      _ = B.evaluation P := by
        rw [← Category.assoc, ← T.map_comp]
        simp [h]
  · intro P K i p h
    change i ≫ B.duality.bidual.hom.app K ≫
      (B.duality.dual.rightOp ⋙ B.duality.dual).map p = _
    have hp := B.duality.bidual.hom.naturality p
    dsimp only [Functor.id_map] at hp
    rw [← hp, ← Category.assoc, h, Category.id_comp]
  · intro P K i p h
    change (B.duality.dual.rightOp ⋙ B.duality.dual).map i ≫
      B.duality.bidual.inv.app K ≫ p = _
    have hi := B.duality.bidual.inv.naturality i
    dsimp only [Functor.id_map] at hi
    rw [← Category.assoc, hi, Category.assoc, h]
    exact Category.comp_id (B.duality.bidual.inv.app P)

/-- Complete the core by its forced retract equations. Source: blueprint
thm-coef-qbar-verdier, proof step 10
(blueprint: lem-coef-qbar-verdier-core-descent). -/
def completeCore (B : DualityData D l hl Ω X) (hB : CoreProperties D l hl Ω X B) :
    Duality D l hl Ω X where
  val := B
  property := core_complete D l hl Ω X B hB

end WeilConjectures.CoefQbarVerdier
