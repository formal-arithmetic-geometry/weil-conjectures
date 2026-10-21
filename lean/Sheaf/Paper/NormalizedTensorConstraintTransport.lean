/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.Paper.CompletedPrimitiveCounitComparison
public import Sheaf.Paper.CompletedOperationExpressions
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.CategoryTheory.StrictRoosComparison

/-! # Normalized tensor constraints through coherent realization

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 0FPT and 0941;
sites-modules.tex, Tag 03EL; the whole-system counit calculation in the node
(blueprint: lem-pur-normalized-tensor-constraint-transport).

The four expression pairs in this node have the named systems as input leaves.
Their recursive beta maps are expanded below. The completed associator is the
quotient contraction roof, defined before its beta-conjugation identity. The
primitive realization is required to have its recorded quotient/Roos normalization.
Natural index n denotes exponent n+1. The small site has sizes t + 1 and t.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.NormalizedTensorTransport

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})
  (S : CoefficientDerivedSystemReduction l E W)
  (σ : @SymmetricCategory (coefficientSequenceDerived l E W) _ S.systemClosed.monoidal)
  (C : RingedDerivedTensorCoherence.{t + 1, t, u, (max u (t + 1)) + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W) S.systemClosed S.systemTensorModel σ)
  (r : integralCompletedTensor l E W ≅
    S.reduction.prod S.reduction ⋙ S.systemClosed.tensor ⋙ coefficientSequenceLimit l E W)

/-- The four tensor constraint shapes, with the orientation in the node.
Source: Stacks 0FPT (blueprint: lem-pur-normalized-tensor-constraint-transport). -/
inductive Kind where
  | associator
  | leftUnitor
  | rightUnitor
  | symmetry

/-- The four typed expression pairs, with input labels 0=A, 1=N, 2=H on W.
This uses the existing expression syntax rather than introducing another grammar.
Source: node fourth paragraph (blueprint: lem-pur-normalized-tensor-constraint-transport). -/
def Kind.expressions (k : Kind) :
    CompletedOperations.Expression (fun _ : Unit ↦ W) (fun _ : Fin 3 ↦ ()) () ×
      CompletedOperations.Expression (fun _ : Unit ↦ W) (fun _ : Fin 3 ↦ ()) () :=
  match k with
  | .associator => (.tensor (.tensor (.input 0) (.input 1)) (.input 2),
      .tensor (.input 0) (.tensor (.input 1) (.input 2)))
  | .leftUnitor => (.tensor (.unit ()) (.input 0), .input 0)
  | .rightUnitor => (.tensor (.input 0) (.unit ()), .input 0)
  | .symmetry => (.tensor (.input 0) (.input 1), .tensor (.input 1) (.input 0))

/-- The actual coefficient system B_n[0], with its quotient transitions.
Source: Stacks 0FPT (blueprint: lem-pur-normalized-tensor-constraint-transport). -/
abbrev unit : coefficientSequenceDerived l E W :=
  DerivedCategory.Q.obj (ringedTensorUnitComplex.{t + 1, t, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W))

/-- Actual scalar action on the left, retaining the degree-zero coefficient unit.
Source: Stacks 0FPT (blueprint: lem-pur-normalized-tensor-constraint-transport). -/
def leftAction (A : coefficientSequenceDerived l E W) :
    S.systemClosed.tensor.obj (unit l E W, A) ≅ A :=
  S.systemClosed.tensor.mapIso (C.unitIso.symm.prod (Iso.refl A)) ≪≫
    S.systemClosed.monoidal.leftUnitor A

/-- Actual scalar action on the right, with the same unit normalization.
Source: Stacks 0FPT (blueprint: lem-pur-normalized-tensor-constraint-transport). -/
def rightAction (A : coefficientSequenceDerived l E W) :
    S.systemClosed.tensor.obj (A, unit l E W) ≅ A :=
  S.systemClosed.tensor.mapIso ((Iso.refl A).prod C.unitIso.symm) ≪≫
    S.systemClosed.monoidal.rightUnitor A

/-- Source systems of the four displayed expression pairs.
Source: node fourth paragraph (blueprint: lem-pur-normalized-tensor-constraint-transport). -/
def systemSource (A N H : coefficientSequenceDerived l E W) :
    Kind → coefficientSequenceDerived l E W
  | .associator => S.systemClosed.tensor.obj (S.systemClosed.tensor.obj (A, N), H)
  | .leftUnitor => S.systemClosed.tensor.obj (unit l E W, A)
  | .rightUnitor => S.systemClosed.tensor.obj (A, unit l E W)
  | .symmetry => S.systemClosed.tensor.obj (A, N)

/-- Target systems of the four displayed expression pairs.
Source: node fourth paragraph (blueprint: lem-pur-normalized-tensor-constraint-transport). -/
def systemTarget (A N H : coefficientSequenceDerived l E W) :
    Kind → coefficientSequenceDerived l E W
  | .associator => S.systemClosed.tensor.obj (A, S.systemClosed.tensor.obj (N, H))
  | .leftUnitor => A
  | .rightUnitor => A
  | .symmetry => S.systemClosed.tensor.obj (N, A)

/-- Whole-system constraints, fixed on total complexes by C's generator formulas.
Source: Stacks 0FPT (blueprint: lem-pur-normalized-tensor-constraint-transport). -/
def systemMap (A N H : coefficientSequenceDerived l E W) (k : Kind) :
    systemSource l E W S A N H k ≅ systemTarget l E W S A N H k :=
  match k with
  | .associator => S.systemClosed.monoidal.associator A N H
  | .leftUnitor => leftAction l E W S σ C A
  | .rightUnitor => rightAction l E W S σ C A
  | .symmetry => σ.braiding A N

/-- Completed source vertices, with exactly the same parentheses as systemSource.
Source: node third paragraph (blueprint: lem-pur-normalized-tensor-constraint-transport). -/
def completedSource (A N H : coefficientSequenceDerived l E W) :
    Kind → DerivedCategory (scalarReductionSource l E W)
  | .associator => (integralCompletedTensor l E W).obj
      ((integralCompletedTensor l E W).obj
        ((coefficientSequenceLimit l E W).obj A, (coefficientSequenceLimit l E W).obj N),
        (coefficientSequenceLimit l E W).obj H)
  | .leftUnitor => (integralCompletedTensor l E W).obj
      ((coefficientSequenceLimit l E W).obj (unit l E W),
        (coefficientSequenceLimit l E W).obj A)
  | .rightUnitor => (integralCompletedTensor l E W).obj
      ((coefficientSequenceLimit l E W).obj A,
        (coefficientSequenceLimit l E W).obj (unit l E W))
  | .symmetry => (integralCompletedTensor l E W).obj
      ((coefficientSequenceLimit l E W).obj A, (coefficientSequenceLimit l E W).obj N)

/-- Completed target vertices.
Source: node third paragraph (blueprint: lem-pur-normalized-tensor-constraint-transport). -/
def completedTarget (A N H : coefficientSequenceDerived l E W) :
    Kind → DerivedCategory (scalarReductionSource l E W)
  | .associator => (integralCompletedTensor l E W).obj
      ((coefficientSequenceLimit l E W).obj A,
        (integralCompletedTensor l E W).obj
          ((coefficientSequenceLimit l E W).obj N, (coefficientSequenceLimit l E W).obj H))
  | .leftUnitor => (coefficientSequenceLimit l E W).obj A
  | .rightUnitor => (coefficientSequenceLimit l E W).obj A
  | .symmetry => (integralCompletedTensor l E W).obj
      ((coefficientSequenceLimit l E W).obj N, (coefficientSequenceLimit l E W).obj A)

/-- The recursive beta at the source, using precisely the primitive counit arrow.
Inputs and the coefficient-unit leaf have identity beta.
Source: node third paragraph (blueprint: lem-pur-normalized-tensor-constraint-transport). -/
def betaSource (A N H : coefficientSequenceDerived l E W) (k : Kind) :
    completedSource l E W A N H k ⟶
      (coefficientSequenceLimit l E W).obj (systemSource l E W S A N H k) :=
  match k with
  | .associator => (integralCompletedTensor l E W).map
      (Prod.mkHom (PrimitiveCounit.tensorBeta l E W S r A N) (𝟙 _)) ≫
        PrimitiveCounit.tensorBeta l E W S r (S.systemClosed.tensor.obj (A, N)) H
  | .leftUnitor => PrimitiveCounit.tensorBeta l E W S r (unit l E W) A
  | .rightUnitor => PrimitiveCounit.tensorBeta l E W S r A (unit l E W)
  | .symmetry => PrimitiveCounit.tensorBeta l E W S r A N

/-- The recursive beta at the target; the unitor targets are input leaves.
Source: node third paragraph (blueprint: lem-pur-normalized-tensor-constraint-transport). -/
def betaTarget (A N H : coefficientSequenceDerived l E W) (k : Kind) :
    completedTarget l E W A N H k ⟶
      (coefficientSequenceLimit l E W).obj (systemTarget l E W S A N H k) :=
  match k with
  | .associator => (integralCompletedTensor l E W).map
      (Prod.mkHom (𝟙 _) (PrimitiveCounit.tensorBeta l E W S r N H)) ≫
        PrimitiveCounit.tensorBeta l E W S r A (S.systemClosed.tensor.obj (N, H))
  | .leftUnitor => 𝟙 _
  | .rightUnitor => 𝟙 _
  | .symmetry => PrimitiveCounit.tensorBeta l E W S r N A

/-- Coherent reduction gamma at the source: R(beta) followed by the actual counit.
Source: node third paragraph (blueprint: lem-pur-normalized-tensor-constraint-transport). -/
def gammaSource (A N H : coefficientSequenceDerived l E W) (k : Kind) :=
  S.reduction.map (betaSource l E W S r A N H k) ≫
    S.adjunction.counit.app (systemSource l E W S A N H k)

/-- Coherent reduction gamma at the target.
Source: node third paragraph (blueprint: lem-pur-normalized-tensor-constraint-transport). -/
def gammaTarget (A N H : coefficientSequenceDerived l E W) (k : Kind) :=
  S.reduction.map (betaTarget l E W S r A N H k) ≫
    S.adjunction.counit.app (systemTarget l E W S A N H k)

/-- The inner quotient contraction d=e_(T(RK,RJ)) R(r_(K,J)). This uses the
scalar-extension adjuncts of the actual total-limit projections, before beta.
Source: node proof steps 4 and 6
(blueprint: lem-pur-normalized-tensor-constraint-transport). -/
def contraction (K J : DerivedCategory (scalarReductionSource l E W)) :=
  S.reduction.map (r.hom.app (K, J)) ≫
    S.adjunction.counit.app (S.systemClosed.tensor.obj (S.reduction.obj K, S.reduction.obj J))

/-- The quotient-model completed associator. The roof first contracts the left
inner completed tensor, reassociates the three reduced inputs, then inverts the
right inner contraction. Both outer arrows are the defining quotient realizations.
Source: node proof step 6 (blueprint: lem-pur-normalized-tensor-constraint-transport). -/
def quotientAssociator (X Y Z : DerivedCategory (scalarReductionSource l E W))
    [IsIso (contraction l E W S r Y Z)] :
    (integralCompletedTensor l E W).obj ((integralCompletedTensor l E W).obj (X, Y), Z) ⟶
      (integralCompletedTensor l E W).obj (X, (integralCompletedTensor l E W).obj (Y, Z)) :=
  r.hom.app ((integralCompletedTensor l E W).obj (X, Y), Z) ≫
    (coefficientSequenceLimit l E W).map
      (S.systemClosed.tensor.map (Prod.mkHom (contraction l E W S r X Y)
          (𝟙 (S.reduction.obj Z))) ≫
        (S.systemClosed.monoidal.associator
          (S.reduction.obj X) (S.reduction.obj Y) (S.reduction.obj Z)).hom ≫
        S.systemClosed.tensor.map (Prod.mkHom (𝟙 (S.reduction.obj X))
          (inv (contraction l E W S r Y Z)))) ≫
    r.inv.app (X, (integralCompletedTensor l E W).obj (Y, Z))

/-- The completed constraints from the actual quotient roofs. The action unitors
contract by T(e_U,e_A) or T(e_A,e_U), so no alternative identification of LU is used.
Source: node proof steps 6, 8 and 9
(blueprint: lem-pur-normalized-tensor-constraint-transport). -/
def quotientMap (A N H : coefficientSequenceDerived l E W)
    [IsIso (contraction l E W S r
      ((coefficientSequenceLimit l E W).obj N) ((coefficientSequenceLimit l E W).obj H))]
    (k : Kind) : completedSource l E W A N H k ⟶ completedTarget l E W A N H k :=
  match k with
  | .associator => quotientAssociator l E W S r
      ((coefficientSequenceLimit l E W).obj A) ((coefficientSequenceLimit l E W).obj N)
      ((coefficientSequenceLimit l E W).obj H)
  | .leftUnitor => r.hom.app _ ≫ (coefficientSequenceLimit l E W).map
      (S.systemClosed.tensor.map (Prod.mkHom (S.adjunction.counit.app (unit l E W))
        (S.adjunction.counit.app A)) ≫ (leftAction l E W S σ C A).hom)
  | .rightUnitor => r.hom.app _ ≫ (coefficientSequenceLimit l E W).map
      (S.systemClosed.tensor.map (Prod.mkHom (S.adjunction.counit.app A)
        (S.adjunction.counit.app (unit l E W))) ≫ (rightAction l E W S σ C A).hom)
  | .symmetry => r.hom.app _ ≫ (coefficientSequenceLimit l E W).map
      (σ.braiding
        (S.reduction.obj ((coefficientSequenceLimit l E W).obj A))
        (S.reduction.obj ((coefficientSequenceLimit l E W).obj N))).hom ≫
      r.inv.app ((coefficientSequenceLimit l E W).obj N,
        (coefficientSequenceLimit l E W).obj A)

/-- Transport of all four normalized tensor constraints, with the actual quotient
construction on the left side of the conjugation equality. The first clause supplies
the inner contraction isomorphism needed by that construction, without a new hypothesis.
The four conditional isomorphism hypotheses are exactly those on beta_P,beta_Q and
gamma_P,gamma_Q in the node. The last two clauses retain both whole-system counit
naturality and the actual quotient-transition square. C specifies the canonical
reassociation, scalar actions and signed swap on simultaneous total representatives.

Source: Stacks sites-cohomology.tex, Tags 07A4, 0FPT, 0941 and sites-modules.tex, Tag 03EL
(blueprint: lem-pur-normalized-tensor-constraint-transport).

Proof plan, following all eleven steps of the node:
1. Work on the sequence site, using lem-coef-semilinear-derived-sections and
   lem-pur-normalized-operation-system-models for simultaneous flat-term K-flat models.
   Tensor, including the intermediate parenthesizations, preserves normalization.
2. Apply lem-sf-ringed-derived-closed-symmetric-monoidal to that site. Its generator
   equations in C give reassociation, both actions, and the sign (-1)^(pq).
   On (p,q,r), the tensor differential signs are 1,(-1)^p,(-1)^(p+q).
3. Apply lem-pur-cochain-pullback-tensor-coherence to scalar extension, then naturality
   in each actual transition adjoint. Both routes have the same three images, scalar
   product, or signed reversed pair. The scalar degree is zero. Identity and iterated
   quotients use the input unit and cocycle equations, before localization.
4. Expand beta_T by lem-pur-completed-primitive-counit-comparison. Counit naturality
   gives gamma_T=T(e_A,e_N)d. Effectivity of normalized tensor systems makes gamma_T
   and T(e_A,e_N) invertible; hence d is invertible.
5. Naturality of the primitive realization expands beta_left as L(T(gamma_AN,e_H))r
   and beta_right as L(T(e_A,gamma_NH))r.
6. The actual quotient associator contracts the inner reductions by d_AN and d_NH.
   Between them it reassociates the three reduced systems. This is quotientAssociator.
7. Substitute gamma=T(e,e)d. Naturality of reassociation cancels the right contraction
   and gives h_right v=a h_left. Applying L proves the first conjugation equality.
8. For symmetry use its quotient word r >> L(sigma) >> r inverse. Naturality moves
   T(e,e) through the signed swap and gives the same beta square.
9. For actions use r >> L(T(e_U,e_A) >> lambda) and the right-hand counterpart.
   The counit e_U is adjoint to the actual limit projections: z tensor b maps to b p_n(z).
   Thus these are precisely the actual coefficient actions, with no scalar rescaling.
10. lem-pur-integral-operations-well-defined and lem-weil-strict-roos-comparison
    identify these quotient words with the descended quotient/Roos maps. Strict maps
    commute with 1-s on products and hence with its shifted cone; Roos naturality
    preserves the equalities and makes the calculation resolution independent.
11. Apply R to the beta square and postcompose with e. Whole-system counit naturality
    gives the gamma square. Every factor is a system map, giving every quotient
    square, including m=n and all iterated quotients. Naturality in inputs follows
    from the same whole-system functor and counit naturality equations.
-/
theorem normalizedTensorConstraintTransport
    (_hl : ∀ w : W, IsUnit (l : W.presheaf.stalk w))
    (ρ : PrimitiveCounit.RoosRealization l E W)
    (_hr : PrimitiveCounit.TensorModel l E W S ρ r)
    (A N H : coefficientSequenceDerived l E W)
    (_hA : IsNormalizedCoefficientSequence l E W A)
    (_hN : IsNormalizedCoefficientSequence l E W N)
    (_hH : IsNormalizedCoefficientSequence l E W H) :
    ∃ _i : IsIso (contraction l E W S r
        ((coefficientSequenceLimit l E W).obj N) ((coefficientSequenceLimit l E W).obj H)),
      ∀ k : Kind,
        ∀ [IsIso (betaSource l E W S r A N H k)]
          [IsIso (betaTarget l E W S r A N H k)]
          [IsIso (gammaSource l E W S r A N H k)]
          [IsIso (gammaTarget l E W S r A N H k)],
        quotientMap l E W S σ C r A N H k =
          betaSource l E W S r A N H k ≫
            (coefficientSequenceLimit l E W).map (systemMap l E W S σ C A N H k).hom ≫
              inv (betaTarget l E W S r A N H k) ∧
        S.reduction.map (quotientMap l E W S σ C r A N H k) ≫
            gammaTarget l E W S r A N H k =
          gammaSource l E W S r A N H k ≫ (systemMap l E W S σ C A N H k).hom ∧
        S.reduction.map ((coefficientSequenceLimit l E W).map
            (systemMap l E W S σ C A N H k).hom) ≫
            S.adjunction.counit.app (systemTarget l E W S A N H k) =
          S.adjunction.counit.app (systemSource l E W S A N H k) ≫
            (systemMap l E W S σ C A N H k).hom ∧
        (∀ {m n : ℕ} (h : n ≤ m),
          (coefficientSequenceDerivedTransition l E W h).app _ ≫
              (normalizedDVRRes l E W h).map
                ((coefficientSequenceDerivedEvaluation l E W n).map
                  (systemMap l E W S σ C A N H k).hom) =
            (coefficientSequenceDerivedEvaluation l E W m).map
                (systemMap l E W S σ C A N H k).hom ≫
              (coefficientSequenceDerivedTransition l E W h).app _) := by
  sorry

end WeilConjectures.NormalizedTensorTransport
