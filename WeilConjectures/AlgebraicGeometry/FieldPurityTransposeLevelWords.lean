/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldPurityTransposeArrows
public import WeilConjectures.AlgebraicGeometry.CohomologicalSmoothnessFiniteComparison

/-! # Finite words for the normalized field purity transpose

Source: blueprint sk-lem-sp-field-extension-towers.proof.md (2), finite tensor and
purity evaluation (blueprint: def-sp-field-purity-transpose-level-words).
These are the existing finite word constructors on the normalized adjunction interface.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldPuritySystem

open FieldShriekSystem FieldExceptionalSystem
variable (P : PurityFiniteSetting.{u}) (D : Models P)
variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  (b : FieldShriekSystem.Laws P D c) (a : Domains P D c) (A : Adjoints P D c b a)
variable (t : ProjectionTensorComparisons P D) (q : Coordinates P D (f := f))

/-- The finite input word retained by the actual tower adjunction.
Source: blueprint (2), finite tensor maps
(blueprint: def-sp-field-purity-transpose-level-words). -/
def inputWord (E : Index P) (n : ℕ) (K : N P D E Y) :
    SpTowerP1.LevelWord P.coefficients.l E.val n Y where
  tower := K.obj
  etale := (A.finite E n).realization.origin.obj ((level P D a E Y n).obj K)
  comparison := (A.finite E n).realization.originIso.hom.app _

/-- The finite exceptional word, preserving both the tower and ordinary counits.
Source: blueprint (2), finite tensor maps
(blueprint: def-sp-field-purity-transpose-level-words). -/
def targetWord (E : Index P) (n : ℕ) (K : N P D E Y) :
    SpTowerP1.LevelWord P.coefficients.l E.val n X where
  tower := ((A.right E).obj K).obj
  etale := (A.finite E n).realization.right.obj
    ((A.finite E n).realization.origin.obj ((level P D a E Y n).obj K))
  comparison := (A.finite E n).realization.rightIso.inv.app _ ≫
    ((A.evaluation E n).inv.app K).hom

/-- The unique right-adjoint comparison for the same chosen compactification.
Source: blueprint (2), finite counit normalization
(blueprint: def-sp-field-purity-transpose-level-words). -/
@[irreducible]
def finiteRightComparison (E : Index P) (n : ℕ) [HasCompactification f] [QuasiCompact f] :
    (A.finite E n).realization.right ≅
      Etale.rightDerivedUpperShriek
        (SpTowerP1.levelRing P.coefficients.l E.val n) f :=
  (A.finite E n).realization.adjunction.rightAdjointUniq
    ((Etale.rightDerivedUpperShriekAdjunction
      (SpTowerP1.levelRing P.coefficients.l E.val n) f).ofNatIsoLeft
        (Etale.rightDerivedLowerShriekIso
          (SpTowerP1.levelRing P.coefficients.l E.val n) c).symm)

/-- Finite ordinary tensor source using G of the degree-zero coefficient unit.
Source: blueprint (2), theta (blueprint: def-sp-field-purity-transpose-level-words). -/
def finiteTensorWord (E : Index P) (n : ℕ)
    (tc : SpTowerP1.TensorCoordinates P.coefficients.l E.val n (D.base E) X)
    (gc : SpTowerP1.GeometricCoordinates P.coefficients.l E.val n f)
    (K : N P D E Y) : SpTowerP1.LevelWord P.coefficients.l E.val n X :=
  SpTowerP1.tensorWord P.coefficients.l E.val n (D.base E) tc
    (SpTowerP1.pullWord P.coefficients.l E.val n (D.base E)
      ((D.operations E).geometry f) gc (inputWord P D c b a A E n K))
    (targetWord P D c b a A E n (unit P D q E))

/-- The specified finite theta, transported only by the counit-preserving right-adjoint
comparison and the input-unit comparison. All tensor and site comparisons are the
published word constructors.
Source: blueprint (2), theta of def-pur-co-smoothness
(blueprint: def-sp-field-purity-transpose-level-words). -/
@[irreducible]
def finiteTheta (E : Index P) (n : ℕ) [HasCompactification f] [QuasiCompact f]
    (ui : (inputWord P D c b a A E n (unit P D q E)).etale ≅
      Etale.ordinaryFiniteUnit (SpTowerP1.levelRing P.coefficients.l E.val n) Y)
    (K : N P D E Y) :=
  ((Etale.ordinaryFiniteTensor (SpTowerP1.levelRing P.coefficients.l E.val n) X).obj
      ((Etale.ordinaryFinitePullback (SpTowerP1.levelRing P.coefficients.l E.val n) f).obj
        (inputWord P D c b a A E n K).etale)).map
      ((finiteRightComparison P D c b a A E n).hom.app _ ≫
        (Etale.rightDerivedUpperShriek
          (SpTowerP1.levelRing P.coefficients.l E.val n) f).map ui.hom) ≫
    PurityFiniteSetting.smoothPurityEtaleTheta
      (SpTowerP1.levelRing P.coefficients.l E.val n) f
      (inputWord P D c b a A E n K).etale ≫
    (finiteRightComparison P D c b a A E n).inv.app _

/-- The finite-level identification of the actual tau with the specified theta.
The input unit is fixed by the normalized constant-section coefficient coordinates.
Source: blueprint (2), finite tensor-map identification
(blueprint: def-sp-field-purity-transpose-level-words). -/
@[irreducible]
def FiniteTensorIdentification [HasCompactification f] [QuasiCompact f] : Prop :=
  ∀ (E : Index P) (n : ℕ),
    ∃ (hy : IsUnit ((P.coefficients.l ^ (n + 1) : ℕ) : Γ(Y, ⊤)))
      (cc : SpTowerP1.CoefficientCoordinates P.coefficients.l E.val n Y hy)
      (tc : SpTowerP1.TensorCoordinates P.coefficients.l E.val n (D.base E) X)
      (gc : SpTowerP1.GeometricCoordinates P.coefficients.l E.val n f)
      (ui : (inputWord P D c b a A E n (unit P D q E)).etale ≅
        Etale.ordinaryFiniteUnit (SpTowerP1.levelRing P.coefficients.l E.val n) Y),
      (SpTowerP1.nu P.coefficients.l E.val n Y).map ui.hom ≫
          (SpTowerP1.unitWord P.coefficients.l E.val n Y cc).comparison =
        (inputWord P D c b a A E n (unit P D q E)).comparison ∧
      ∀ (K : N P D E Y)
        (hpf : IsIso (leftProjection P D t E c K.obj (omega P D c b a A q E).obj)),
        SpTowerP1.WordComparison P.coefficients.l E.val n
          (finiteTensorWord P D c b a A q E n tc gc K)
          (targetWord P D c b a A E n K)
          (tau P D c b a A t q E K hpf).hom (finiteTheta P D c b a A q E n ui K)

/-- A diagonal orientation is tested with exactly the recorded normalized finite
root, tensor, site and ordinary-adjoint comparisons. The equation uses the inverse
of the diagonal purity isomorphism, as in tower-gamma (1).
Source: blueprint (2), diagonal orientations
(blueprint: def-sp-field-purity-transpose-level-words). -/
@[irreducible]
def DiagonalOrientation [HasCompactification f] [QuasiCompact f]
    [IsNoetherian X] [IsNoetherian Y]
    (E : Index P) (d : ℕ) (w : SpChartAdmissibility.Twists P.coefficients.l E.val X)
    (orientation : SpTowerGamma.orderedLine P.coefficients.l E.val (D.base E) X w d ≅
      (omega P D c b a A q E).obj) : Prop :=
  ∀ n : ℕ,
    ∃ (hx : IsUnit ((P.coefficients.l ^ (n + 1) : ℕ) : Γ(X, ⊤)))
      (hy : IsUnit ((P.coefficients.l ^ (n + 1) : ℕ) : Γ(Y, ⊤)))
      (cx : SpTowerP1.CoefficientCoordinates P.coefficients.l E.val n X hx)
      (cy : SpTowerP1.CoefficientCoordinates P.coefficients.l E.val n Y hy)
      (tc : SpTowerP1.TensorCoordinates P.coefficients.l E.val n (D.base E) X)
      (roots : SpCoordinateAdjunction.RootLines P.coefficients.l E.val X)
      (ui : (inputWord P D c b a A E n (unit P D q E)).etale ≅
        Etale.ordinaryFiniteUnit (SpTowerP1.levelRing P.coefficients.l E.val n) Y)
      (dg : Etale.FiniteRingSectionDeformation.Geometry d (pullback.fst f f)
        (pullback.diagonal f))
      (alpha : Etale.dualizingComplex
          (SpTowerP1.levelRing P.coefficients.l E.val n) f ≅
        Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing P.coefficients.l E.val n)
          (P.coefficients.l ^ (n + 1)) (SpTowerP1.levelAnnihilates P.coefficients.l E.val n)
          X d),
      Etale.FiniteSmoothPurity.OrientationNormalized
        (SpTowerP1.levelRing P.coefficients.l E.val n) (P.coefficients.l ^ (n + 1))
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
        (SpTowerP1.levelAnnihilates P.coefficients.l E.val n) f d dg hx alpha ∧
      (SpTowerP1.nu P.coefficients.l E.val n Y).map ui.hom ≫
          (SpTowerP1.unitWord P.coefficients.l E.val n Y cy).comparison =
        (inputWord P D c b a A E n (unit P D q E)).comparison ∧
      SpTowerP1.WordComparison P.coefficients.l E.val n
        (SpTowerGamma.coefficientWord P.coefficients.l E.val (D.base E) X w roots n hx cx tc d)
        (targetWord P D c b a A E n (unit P D q E)) orientation.hom
        (alpha.inv ≫ (Etale.rightDerivedUpperShriek
            (SpTowerP1.levelRing P.coefficients.l E.val n) f).map
              (PurityFiniteSetting.smoothPurityUnitIso
                (SpTowerP1.levelRing P.coefficients.l E.val n) Y).inv ≫
          (finiteRightComparison P D c b a A E n).inv.app _ ≫
          (A.finite E n).realization.right.map ui.inv)

/-- Every evaluation of the actual oriented transpose is the specified finite purity
map, with the recorded root, pullback, tensor and right-adjoint comparisons.
Source: blueprint (2), evaluation to def-pur-smooth-purity-map
(blueprint: def-sp-field-purity-transpose-level-words). -/
@[irreducible]
def FinitePurityIdentification [HasCompactification f] [QuasiCompact f]
    [IsNoetherian X] [IsNoetherian Y]
    (E : Index P) (d : ℕ) (w : SpChartAdmissibility.Twists P.coefficients.l E.val X)
    (orientation : SpTowerGamma.orderedLine P.coefficients.l E.val (D.base E) X w d ≅
      (omega P D c b a A q E).obj) (K : N P D E Y)
    (hpf : IsIso (leftProjection P D t E c K.obj (omega P D c b a A q E).obj)) : Prop :=
  ∀ n : ℕ,
    ∃ (hx : IsUnit ((P.coefficients.l ^ (n + 1) : ℕ) : Γ(X, ⊤)))
      (cx : SpTowerP1.CoefficientCoordinates P.coefficients.l E.val n X hx)
      (tc : SpTowerP1.TensorCoordinates P.coefficients.l E.val n (D.base E) X)
      (gc : SpTowerP1.GeometricCoordinates P.coefficients.l E.val n f)
      (roots : SpCoordinateAdjunction.RootLines P.coefficients.l E.val X)
      (dg : Etale.FiniteRingSectionDeformation.Geometry d (pullback.fst f f)
        (pullback.diagonal f))
      (alpha : Etale.dualizingComplex
          (SpTowerP1.levelRing P.coefficients.l E.val n) f ≅
        Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing P.coefficients.l E.val n)
          (P.coefficients.l ^ (n + 1)) (SpTowerP1.levelAnnihilates P.coefficients.l E.val n)
          X d),
      Etale.FiniteSmoothPurity.OrientationNormalized
        (SpTowerP1.levelRing P.coefficients.l E.val n) (P.coefficients.l ^ (n + 1))
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
        (SpTowerP1.levelAnnihilates P.coefficients.l E.val n) f d dg hx alpha ∧
      SpTowerP1.WordComparison P.coefficients.l E.val n
        (SpTowerP1.tensorWord P.coefficients.l E.val n (D.base E) tc
          (SpTowerP1.pullWord P.coefficients.l E.val n (D.base E)
            ((D.operations E).geometry f) gc (inputWord P D c b a A E n K))
          (SpTowerGamma.coefficientWord P.coefficients.l E.val (D.base E) X w roots n
            hx cx tc d))
        (targetWord P D c b a A E n K) (gamma P D c b a A t q E w d orientation K hpf)
        (Etale.FiniteSmoothPurity.gamma (SpTowerP1.levelRing P.coefficients.l E.val n) f
            (Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing P.coefficients.l E.val n)
              (P.coefficients.l ^ (n + 1))
              (SpTowerP1.levelAnnihilates P.coefficients.l E.val n) X d)
            alpha (inputWord P D c b a A E n K).etale ≫
          (finiteRightComparison P D c b a A E n).inv.app _)

/-- The coefficient comparison of shifted lines is used only through its specified
orientation equation. This is the second displayed equality for the diagonal maps.
Source: blueprint (2), purity compatibility
(blueprint: def-sp-field-purity-transpose-level-words). -/
@[irreducible]
def DiagonalPurityCompatibility [HasCompactification f] [QuasiCompact f]
    [IsNoetherian X] [IsNoetherian Y]
    {E F : Index P} (h : E ≤ F) (d : ℕ) : Prop :=
  ∀ (wE : SpChartAdmissibility.Twists P.coefficients.l E.val X)
    (wF : SpChartAdmissibility.Twists P.coefficients.l F.val X)
    (line : (D.scalars E F h X).T.obj
        (SpTowerGamma.orderedLine P.coefficients.l E.val (D.base E) X wE d) ≅
      SpTowerGamma.orderedLine P.coefficients.l F.val (D.base F) X wF d)
    (aE : SpTowerGamma.orderedLine P.coefficients.l E.val (D.base E) X wE d ≅
      (omega P D c b a A q E).obj)
    (aF : SpTowerGamma.orderedLine P.coefficients.l F.val (D.base F) X wF d ≅
      (omega P D c b a A q F).obj),
    DiagonalOrientation P D c b a A q E d wE aE →
    DiagonalOrientation P D c b a A q F d wF aF →
    (D.scalars E F h X).T.map aE.hom ≫ omegaComparison P D c b a A q h =
      line.hom ≫ aF.hom →
    ∀ (K : N P D E Y)
      (hA : IsIso (leftProjection P D t E c K.obj (omega P D c b a A q E).obj))
      (hB : IsIso (leftProjection P D t F c ((scalar P D a h Y).obj K).obj
        (omega P D c b a A q F).obj)),
      (D.scalars E F h X).T.map (gamma P D c b a A t q E wE d aE K hA) ≫
          (component P D c b a A h K).hom =
        (puritySourceComparison P D t h d wE wF line K).hom ≫
          gamma P D c b a A t q F wF d aF ((scalar P D a h Y).obj K) hB

end AlgebraicGeometry.ProEtale.FieldPuritySystem
