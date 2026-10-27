/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Mathlib.CategoryTheory.PathCategory.Basic
public import Sheaf.Paper.IntegralPullbackComparisonRealization

/-! # Common-stage finite realization and iterated Weil structures

Source: current Weil blueprint, `lem-wf-l2-upper`, opening punctual-bounds argument,
and its extracted finite-stage argument (blueprint: lem-wf-common-stage-weil-iterate).

Finite quivers record the specified objects and arrows; finitely many pairs of paths
record equations between composites. The finite-stage models use the published
rationalized categories, literal pair category and normalized scalar comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v w t z
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.Endofunctor
open WeilConjectures.AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The specified rationalized integral scalar comparison for Frobenius pullback.
Source: extracted finite-stage argument, scalar comparison paragraph
(blueprint: lem-wf-common-stage-weil-iterate). -/
def wfScalarComparison (E M : Index l Ω) (h : E ≤ M) :
    sfWeilFrobeniusPullback D l hl Y₀ (Coefficient.{u} l Ω E) ⋙
        transition l Ω (D.geometricFiber Y₀).left E M h ≅
      transition l Ω (D.geometricFiber Y₀).left E M h ⋙
        sfWeilFrobeniusPullback D l hl Y₀ (Coefficient.{u} l Ω M) :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  rationalPullbackScalarComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω M)
    (coefficientInclusion l Ω E M h) (D.geometricFrobenius Y₀).hom

/-- Scalar extension of a Weil pair, with structure d^{-1} followed by scalar theta.
Source: extracted finite-stage argument, theta_M formula
(blueprint: lem-wf-common-stage-weil-iterate). -/
def wfScalarWeil (E M : Index l Ω) (h : E ≤ M) :
    sfWeilComplex D l hl Y₀ (Coefficient.{u} l Ω E) ⥤
      sfWeilComplex D l hl Y₀ (Coefficient.{u} l Ω M) :=
  IsoAlgebra.mapOfNatIso (wfScalarComparison D l hl Ω Y₀ E M h).symm

/-- Iterated scalar comparison d_r, formed from the specified one-step comparison.
Source: extracted finite-stage argument, induction on r
(blueprint: lem-wf-common-stage-weil-iterate). -/
def wfIteratedScalarComparison (E M : Index l Ω) (h : E ≤ M)
    (K : Stage l Ω (D.geometricFiber Y₀).left E) : (r : ℕ) →
    (transition l Ω (D.geometricFiber Y₀).left E M h).obj
        (((sfWeilFrobeniusPullback D l hl Y₀ (Coefficient.{u} l Ω E)).iterate r).obj K) ≅
      ((sfWeilFrobeniusPullback D l hl Y₀ (Coefficient.{u} l Ω M)).iterate r).obj
        ((transition l Ω (D.geometricFiber Y₀).left E M h).obj K)
  | 0 => Iso.refl _
  | r + 1 =>
    (wfScalarComparison D l hl Ω Y₀ E M h).app
        (((sfWeilFrobeniusPullback D l hl Y₀ (Coefficient.{u} l Ω E)).iterate r).obj K) ≪≫
      (sfWeilFrobeniusPullback D l hl Y₀ (Coefficient.{u} l Ω M)).mapIso
        (wfIteratedScalarComparison E M h K r)

/-- The canonical comparison of iterated common-stage and finite-stage pullbacks.
Source: extracted finite-stage argument, representative-independence paragraph
(blueprint: lem-wf-common-stage-weil-iterate). -/
def wfStageIteratedComparison (E : Index l Ω)
    (K : Stage l Ω (D.geometricFiber Y₀).left E) : (r : ℕ) →
    ((sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).iterate r).obj
        ((inclusion E).obj K) ≅
      (inclusion E).obj
        (((sfWeilFrobeniusPullback D l hl Y₀ (Coefficient.{u} l Ω E)).iterate r).obj K)
  | 0 => Iso.refl _
  | r + 1 =>
    (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).mapIso
        (wfStageIteratedComparison E K r) ≪≫
      sfWeilStagePullbackIdentification D l hl Y₀ Ω E
        (((sfWeilFrobeniusPullback D l hl Y₀ (Coefficient.{u} l Ω E)).iterate r).obj K)

/-- Identify T^{n+1} with the pullback along g^{n+1} using the specified composition maps.
Source: extracted finite-stage argument, positive-iterate paragraph
(blueprint: lem-wf-common-stage-weil-iterate). -/
def wfPowerPullbackComparison (E : Index l Ω)
    (K : Stage l Ω (D.geometricFiber Y₀).left E) : (n : ℕ) →
    ((sfWeilFrobeniusPullback D l hl Y₀ (Coefficient.{u} l Ω E)).iterate (n + 1)).obj K ≅
      (@rationalDerivedPullback l _ (Coefficient.{u} l Ω E) _ _ _ _ _
        (localPositivePower (D.geometricFrobenius Y₀).hom n)
        (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).obj K
  | 0 => Iso.refl _
  | n + 1 =>
    eqToIso (Functor.congr_obj
        ((sfWeilFrobeniusPullback D l hl Y₀
          (Coefficient.{u} l Ω E)).iterate_succ_left (n + 1)) K) ≪≫
      wfPowerPullbackComparison E
        ((sfWeilFrobeniusPullback D l hl Y₀ (Coefficient.{u} l Ω E)).obj K) n ≪≫
      (letI := sfWeilPrimeInvertible D l hl Y₀
       (localPullbackComposition l (Coefficient.{u} l Ω E)
         (localPositivePower (D.geometricFrobenius Y₀).hom n)
         (D.geometricFrobenius Y₀).hom K).symm)

/-- Simultaneous finite-stage Weil models, including any finite list of path equations.
Source: current blueprint `lem-wf-l2-upper`, opening punctual-bounds argument; extracted
finite-stage argument, steps 1--3 (blueprint: lem-wf-common-stage-weil-iterate).

Proof: choose representatives of each structure map and its inverse and of each specified
arrow in the literal pair category of def-weil-algebraically-closed-coefficients. Take a
compositum containing all fields and the prescribed finite starting fields. Conjugate the
structure representatives by the normalized pullback/scalar comparisons of
lem-trf-integral-pullback-comparison-realization. Represent the two inverse equations,
each Weil square and every specified path equation at a further finite stage using the
eventual-equality criterion. One finite compositum of these witnesses makes all equations
true simultaneously. The inverse representatives are then actual inverses, the arrows
are Weil morphisms, and the canonical stage identifications give the displayed isomorphisms.
This does not require injective transition maps on Hom sets. -/
theorem commonStageWeilFiniteRealization [IsSeparated Y₀.hom]
    (V : Type w) [Quiver.{t} V] [Finite V] [∀ i j : V, Finite (i ⟶ j)]
    (F : V ⥤q sfCommonStageWeilComplex D l hl Y₀ Ω)
    (R : Type z) [Finite R] (a b : R → V)
    (p q : ∀ r, Quiver.Path (a r) (b r))
    (heq : ∀ r, (Paths.lift F).map (p r) = (Paths.lift F).map (q r))
    (S : Finset (Index l Ω)) :
    ∃ (E : Index l Ω), (∀ M ∈ S, M ≤ E) ∧
      ∃ (h : ∀ i, (F.obj i).carrier.stage ≤ E)
        (F₀ : V ⥤q sfWeilComplex D l hl Y₀ (Coefficient.{u} l Ω E))
        (σ : ∀ i, sfWeilStageObject D l hl Y₀ Ω E (F₀.obj i) ≅ F.obj i),
        (∀ i, (F₀.obj i).carrier = (F.obj i).carrier.toStage (h i)) ∧
        (∀ i, HEq (σ i).inv.hom.f
          ((stageSystem l Ω (D.geometricFiber Y₀).left).isoToStage
            (F.obj i).carrier (h i)).hom) ∧
        (∀ (i j : V) (e : i ⟶ j),
          (F.map e).hom.f = (σ i).inv.hom.f ≫
            (inclusion E).map (F₀.map e).hom.f ≫ (σ j).hom.hom.f) ∧
        (∀ r, (Paths.lift F₀).map (p r) = (Paths.lift F₀).map (q r)) := by
  sorry

/-- Positive Weil iterates commute with scalar extension, its unit and tower comparisons,
descend from every finite model, and intertwine arbitrary common-stage Weil morphisms.
Source: current blueprint `lem-wf-l2-upper`, opening punctual-bounds argument; extracted
finite-stage argument, steps 4--8 (blueprint: lem-wf-common-stage-weil-iterate).

Proof: the structure isomorphism and its images under pullback are invertible, so their
composites are invertible. The associativity and unit comparisons of
lem-trf-integral-pullback-comparison-realization identify the functor powers with the
scheme-power pullbacks, giving the localWeilIterate recursion of
def-weil-local-frobenius-trace. Induct on the positive exponent for the scalar equation:
use naturality of d_r at theta and the coherent successor formula for d_{r+1}; the
inductive equality then cancels the adjacent comparisons. The scalar unit and tower
laws follow from the same normalized comparison laws. Stage inclusion preserves these
composites, giving the descent equation. For two representatives, enlarge to a field
where their structure maps and inverse equations agree; inverses agree by uniqueness,
and equal maps have equal iterates. Thus the result is independent of inverse and equation
witnesses. Finally induct on r in the Weil square u theta_K = theta_L T(u); applying T
and associativity proves the next square without using an inverse of u. -/
theorem commonStageWeilIterate [IsSeparated Y₀.hom] :
    (∀ (E : Index l Ω)
      (K : sfWeilComplex D l hl Y₀ (Coefficient.{u} l Ω E)) (n : ℕ),
      wfPowerPullbackComparison D l hl Ω Y₀ E K.carrier n ≪≫
          localWeilIterate l (Coefficient.{u} l Ω E) D hl Y₀ K n =
        K.strIterate (n + 1)) ∧
    (∀ (E M : Index l Ω) (h : E ≤ M)
      (K : sfWeilComplex D l hl Y₀ (Coefficient.{u} l Ω E)) (n : ℕ),
      wfIteratedScalarComparison D l hl Ω Y₀ E M h K.carrier (n + 1) ≪≫
          ((wfScalarWeil D l hl Ω Y₀ E M h).obj K).strIterate (n + 1) =
        (transition l Ω (D.geometricFiber Y₀).left E M h).mapIso
          (K.strIterate (n + 1))) ∧
    (∀ (E : Index l Ω) (K : Stage l Ω (D.geometricFiber Y₀).left E) (n : ℕ),
      wfIteratedScalarComparison D l hl Ω Y₀ E E le_rfl K (n + 1) ≪≫
          ((sfWeilFrobeniusPullback D l hl Y₀ (Coefficient.{u} l Ω E)).iterate
            (n + 1)).mapIso ((unitor l Ω (D.geometricFiber Y₀).left E).app K) =
        (unitor l Ω (D.geometricFiber Y₀).left E).app
          (((sfWeilFrobeniusPullback D l hl Y₀
            (Coefficient.{u} l Ω E)).iterate (n + 1)).obj K)) ∧
    (∀ (E M N : Index l Ω) (h : E ≤ M) (k : M ≤ N)
      (K : Stage l Ω (D.geometricFiber Y₀).left E) (n : ℕ),
      (transition l Ω (D.geometricFiber Y₀).left M N k).mapIso
          (wfIteratedScalarComparison D l hl Ω Y₀ E M h K (n + 1)) ≪≫
        wfIteratedScalarComparison D l hl Ω Y₀ M N k
          ((transition l Ω (D.geometricFiber Y₀).left E M h).obj K) (n + 1) ≪≫
        ((sfWeilFrobeniusPullback D l hl Y₀ (Coefficient.{u} l Ω N)).iterate
          (n + 1)).mapIso ((associator l Ω (D.geometricFiber Y₀).left E M N h k).app K) =
      (associator l Ω (D.geometricFiber Y₀).left E M N h k).app
          (((sfWeilFrobeniusPullback D l hl Y₀
            (Coefficient.{u} l Ω E)).iterate (n + 1)).obj K) ≪≫
        wfIteratedScalarComparison D l hl Ω Y₀ E N (h.trans k) K (n + 1)) ∧
    (∀ (E : Index l Ω)
      (K : sfWeilComplex D l hl Y₀ (Coefficient.{u} l Ω E)) (n : ℕ),
      (sfWeilStageObject D l hl Y₀ Ω E K).strIterate (n + 1) =
        wfStageIteratedComparison D l hl Ω Y₀ E K.carrier (n + 1) ≪≫
          (inclusion E).mapIso (K.strIterate (n + 1))) ∧
    (∀ (K L : sfCommonStageWeilComplex D l hl Y₀ Ω) (uKL : K ⟶ L) (n : ℕ),
      (K.strIterate (n + 1)).hom ≫ uKL.hom.f =
        ((sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).iterate (n + 1)).map
          uKL.hom.f ≫ (L.strIterate (n + 1)).hom) := by
  sorry

end WeilConjectures
