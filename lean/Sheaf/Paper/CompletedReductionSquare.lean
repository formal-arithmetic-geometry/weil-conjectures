/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.Paper.CompletedBaseChangeMap
public import Sheaf.Paper.CompletedDirectImageLimits
public import Sheaf.Paper.CompletedPullbackReduction
public import Sheaf.Paper.KoszulReconstruction
public import Sheaf.Paper.PerfectProjectionFormula
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.Paper.RingedEtaleOriginWitness
public import Sheaf.Paper.FourCorners
public import Sheaf.Paper.FourArrows
public import Sheaf.Paper.CompletedPullback
public import Sheaf.Paper.IntrinsicCompletion
public import Sheaf.Paper.FiniteReductionReconstructionCompleted
public import Sheaf.Paper.ProjectionFormulaBaseChangeNaturality

/-!
# The four edges of the completed reduction square

Source: blueprint proper base change, order 1341
(blueprint: def-weil-pbc-completed-reduction-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe t v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
/-- The quotient-tower model of derived completion, with its strict coefficient action.
Source: Stacks 099M (blueprint: def-weil-pbc-completed-reduction-square). -/
abbrev AdicCoefficientDatum.quotientCompletion (T : Scheme.{t}) :
    d.derived T ⥤ d.derived T :=
  completedReductionTower T d ⋙ completedRlim T (d.completedRing T)

/-- Evaluation of completion into the original finite reduction, after scalar restriction.
The second factor is the fixed K-flat evaluation comparison of the adic datum.
Source: blueprint order 1249 (blueprint: def-weil-pbc-completed-reduction-square). -/
def AdicCoefficientDatum.quotientCompletionEvaluation (T : Scheme.{t})
    (K : d.derived T) (n : ℕ) :
    (d.quotientCompletion T).obj K ⟶
      (reductionDerivedRestrict T (d.projection T n)).obj ((d.reduction T n).obj K) :=
  (completedRlimProjection T (d.completedRing T) n).app
      ((completedReductionTower T d).obj K) ≫
    (completedReductionEvaluation T d n).app K

/-- The specified rho is the scalar-extension adjunct of evaluation. Its target retains
its quotient-ring action, and its source is reduced only after forming the derived limit.
Source: blueprint order 1249 (blueprint: def-weil-pbc-completed-reduction-square). -/
def AdicCoefficientDatum.quotientCompletionReduction (T : Scheme.{t})
    (K : d.derived T) (n : ℕ) :
    (d.reduction T n).obj ((d.quotientCompletion T).obj K) ⟶ (d.reduction T n).obj K :=
  (proEtaleRingDerivedExtensionAdjunction (d.projection T n)).homEquiv _ _ |>.symm
    (d.quotientCompletionEvaluation T K n)

section
variable {U V : Scheme.{t}} (g : U ⟶ V)

/-- Completed pullback is completion of ordinary pullback by the canonical strict
reduction/pullback comparison, including its transition maps.
Source: Stacks 099N (blueprint: def-weil-pbc-completed-reduction-square). -/
def AdicCoefficientDatum.completedPullCompletionIso (K : d.derived V) :
    (d.completedPull g).obj K ≅ (d.quotientCompletion U).obj ((d.pull g).obj K) :=
  (completedRlim U (d.completedRing U)).mapIso ((d.reductionTowerPullbackIso g).app K)

/-- Projection-induced finite reduction of completed pullback. The ordered factors
identify the pulled-back strict tower, apply the adjunct of its limit projection,
and use the inverse of the finite coefficient tensor/pullback comparison.
Source: blueprint completed pullback reduction
(blueprint: def-weil-pbc-completed-reduction-square). -/
def AdicCoefficientDatum.completedPullReduction (K : d.derived V) (n : ℕ) :
    (d.reduction U n).obj ((d.completedPull g).obj K) ⟶
      (d.finitePull g n).obj ((d.reduction V n).obj K) :=
  (d.reduction U n).map (d.completedPullCompletionIso g K).hom ≫
    d.quotientCompletionReduction U ((d.pull g).obj K) n ≫ (d.chi g n).inv.app K

end

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

/-- Completion commutes with direct image by first taking the derived limit of the
canonical projection-formula tower map and then the inverse direct-image/limit
comparison. Finally the strict pullback/reduction identification identifies the completed
ordinary pullback with completed pullback. This order is part of the definition.
Source: blueprint completed reduction square
(blueprint: def-weil-pbc-completed-reduction-square). -/
def AdicCoefficientDatum.completionDirectImageComparison (K : d.derived X) :
    (d.quotientCompletion Y').obj ((d.push f').obj ((d.pull g').obj K)) ⟶
      (d.push f').obj ((d.completedPull g').obj K) :=
  (completedRlim Y' (d.completedRing Y')).map
      (d.towerProjection f' ((d.pull g').obj K)) ≫
    (d.directImageRlimIso f').inv.app
      ((completedReductionTower X' d).obj ((d.pull g').obj K)) ≫
    (d.push f').map (d.completedPullCompletionIso g' K).inv

/-- The specified comparison chi is invertible.
Source: blueprint completed reduction square; Stacks Tags 0944 and 099N
(blueprint: def-weil-pbc-completed-reduction-square).
Proof: each level of towerProjection is the canonical projection-formula map with the
perfect coefficient A/I^(n+1), by its defining adjunction and the strict quotient tower
comparison. Its inverse is the finite-total inverse from the perfect projection formula.
The inverses commute with transitions by naturality and cancelling the forward maps.
Thus the tower map is an isomorphism. Derived limit preserves this isomorphism, and the
remaining two factors are the canonical direct-image/limit and pullback/tower isomorphisms.
No completeness assumption on ordinary pullback is used. -/
theorem AdicCoefficientDatum.completionDirectImageComparison_isIso (K : d.derived X) :
    IsIso (d.completionDirectImageComparison (g' := g') (f' := f') K) := by
  sorry

attribute [instance] AdicCoefficientDatum.completionDirectImageComparison_isIso

/-- Finite reduction of quotient-tower completion is the adjunct of the strict limit
projection, and is invertible even when its input has not been completed.
Source: blueprint completed reduction square; Stacks Tags 099M and 091Z
(blueprint: def-weil-pbc-completed-reduction-square).
Proof: identify quotient-tower and intrinsic Koszul completion by Koszul reconstruction.
Tensor a bounded finite-projective resolution of A/I^(n+1) with the Roos products and
cone. In the reduced Koszul tower each negative summand is pro-zero since a sufficiently
long transition is multiplication by a power of a generator that vanishes in the quotient.
The degree-zero tower is constant, and its Roos evaluation is identity. Therefore the
reduced completion unit is invertible. The scalar-extension adjunction and the limit
projection give rho composed with that unit equal to identity, so rho is its inverse.
This argument does not assume the input complete. -/
theorem AdicCoefficientDatum.completedDirectImageReduction_isIso (K : d.derived X) (n : ℕ) :
    IsIso (d.quotientCompletionReduction Y' ((d.push f').obj ((d.pull g').obj K)) n) := by
  sorry

attribute [instance] AdicCoefficientDatum.completedDirectImageReduction_isIso

/-- The canonical sigma map is invertible: direct image preserves completeness and
completed-pullback reduction is invertible on complete objects.
Source: blueprint order 1341, sigma; Stacks Tags 099M and 099N
(blueprint: def-weil-pbc-completed-reduction-square).
Proof:
1. The completion-unit compatibility of direct image and its Rlim comparison gives
completeness of Rf_*K, by prop-weil-pbc-direct-image-limits.
2. The normalized strict reduction/pullback comparison identifies completed pullback
with quotient completion of ordinary pullback, retaining all transition maps.
3. Tensor a bounded finite-projective resolution of the quotient with the two Roos
products and their cone. Koszul reconstruction identifies this with the reduced Koszul
tower: the negative summands are pro-zero because long transitions multiply by powers
of generators vanishing in the quotient; the degree-zero summand is constant.
4. The limit evaluation on that constant summand is identity. The scalar-extension
adjunction identifies its adjunct with completedPullReduction, after the prescribed chi
comparison. It is therefore invertible, with no boundedness hypothesis on K.
TowerComplete agrees with intrinsic completeness by towerComplete_iff_intrinsic. -/
theorem AdicCoefficientDatum.completedReductionSigma_isIso (K : d.derived X)
    (hK : d.TowerComplete X K) (n : ℕ) :
    IsIso (d.completedPullReduction g ((d.push f).obj K) n) := by
  sorry

/-- The canonical sigma is reduction of completed pullback, applied to Rf_* K.
Source: blueprint completed reduction square
(blueprint: def-weil-pbc-completed-reduction-square). -/
def AdicCoefficientDatum.completedReductionSigma (K : d.derived X)
    (hK : d.TowerComplete X K) (n : ℕ) :
    (d.reduction Y' n).obj ((d.completedPull g).obj ((d.push f).obj K)) ≅
      (d.finitePull g n).obj ((d.reduction Y n).obj ((d.push f).obj K)) :=
  letI : IsIso (d.completedPullReduction g ((d.push f).obj K) n) :=
    d.completedReductionSigma_isIso (f := f) (g := g) K hK n
  asIso (d.completedPullReduction g ((d.push f).obj K) n)

/-- Tau is reduction of the INVERSE of chi followed by rho for M=Rf'_* Lg'^* K.
Both arrows retain the quotient coefficient action.
Source: blueprint completed reduction square
(blueprint: def-weil-pbc-completed-reduction-square). -/
def AdicCoefficientDatum.completedReductionTau (K : d.derived X) (n : ℕ) :
    (d.reduction Y' n).obj ((d.push f').obj ((d.completedPull g').obj K)) ≅
      (d.reduction Y' n).obj ((d.push f').obj ((d.pull g').obj K)) :=
  (d.reduction Y' n).mapIso
      (asIso (d.completionDirectImageComparison (g' := g') (f' := f') K)).symm ≪≫
    asIso (d.quotientCompletionReduction Y' ((d.push f').obj ((d.pull g').obj K)) n)

/-- The completed reduction square records its four vertices and the four ordered edges.
The horizontal edges are the reduced completed exchange and the finite exchange; the
vertical edges are sigma followed by h and tau followed by h'. No path equality is a field.
Source: blueprint completed reduction square
(blueprint: def-weil-pbc-completed-reduction-square). -/
structure CompletedReductionSquareEdges {C : Type v} [Category.{w} C]
    (S T B D : C) where
  upper : S ⟶ T
  lower : B ≅ D
  left : S ≅ B
  right : T ≅ D

/-- The four edges of the completed reduction square at positive level n+1. The complete
input and its separate etale-origin witnesses are exactly those of completed base change.
Sigma is canonical completed-pullback reduction; tau has the inverse-chi-then-rho order.
The finite projection formula and exchange provide the specified h, h' and v'.
Source: blueprint completed reduction square, order 1341
(blueprint: def-weil-pbc-completed-reduction-square). -/
def AdicCoefficientDatum.completedReductionSquare [IsProper f] (K : d.derived X)
    (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) (n : ℕ) :
    CompletedReductionSquareEdges
      ((d.reduction Y' n).obj ((d.completedPull g).obj ((d.push f).obj K)))
      ((d.reduction Y' n).obj ((d.push f').obj ((d.completedPull g').obj K)))
      (d.fourCorners (f := f) (f' := f') (g := g) (g' := g') K n 1)
      (d.fourCorners (f := f) (f' := f') (g := g) (g' := g') K n 3) where
  upper := (d.reduction Y' n).map (d.completedBaseChangeMap sq K hK W)
  lower := (d.fourArrows sq K hK W n).v'
  left := d.completedReductionSigma (f := f) (g := g) K hK n ≪≫
    (d.fourArrows sq K hK W n).h
  right := d.completedReductionTau (f' := f') (g' := g') K n ≪≫
    (d.fourArrows sq K hK W n).h'

end AlgebraicGeometry.Scheme
