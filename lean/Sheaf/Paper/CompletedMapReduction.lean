/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.Paper.CompletedBaseChangeMap
public import Sheaf.Paper.CompletedReductionSquare
import Sheaf.Paper.FourCorners
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.AdicCompletionReduction
import Sheaf.Paper.CompletionMap
import Sheaf.Paper.CompleteCoefficientDatum
import Sheaf.Paper.CompletedPullbackReduction
import Sheaf.Paper.FourArrows
import Sheaf.Paper.CompletedTowerCompatibility
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.PbcRectangleDerivedLimit
import Sheaf.Paper.CompletedRlimFunctor
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.CategoryTheory.DiagramSiteRealization
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.CondensedAmbientExchange
import Sheaf.Paper.FiniteLevelRectangle
import Sheaf.Paper.PbcRoosTriangle
import Sheaf.Paper.QuotientCornerFrobeniusStructures
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.StrictTowerExchangeMateNormalization
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Finite reduction of the completed base-change map

Source: blueprint sec-proper-base-change/sk-thm-properbasechange,
`lemma-weil-pbc-completed-map-reduction.md`, detailed form and proof, order 1347;
Stacks Project Tag 099N (blueprint: lemma-weil-pbc-completed-map-reduction).

## Main statements

- `AdicCoefficientDatum.completedMapReduction`: the specified conjugated equality.
- `AdicCoefficientDatum.completedMapReduction_transition`: compatibility on all four edges.
- `AdicCoefficientDatum.completedMapReduction_endomorphism`: operator compatibility.

The index `n : ℕ` denotes the positive exponent `n+1`. Transitions are compared only
in the ambient completed-coefficient category, retaining the actual quotient actions
at each finite level. The helper comparisons use the canonical finite projection
formula and chi, independently of commutativity of the completed reduction square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe t v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Compatibility between two reduction squares means compatibility on each of their
four specified edges. Source: blueprint order 1347, transition and operator paragraphs
(blueprint: lemma-weil-pbc-completed-map-reduction). -/
def CompletedReductionSquareEdges.Intertwines {C : Type v} [Category.{w} C]
    {S T B D S' T' B' D' : C}
    (e : CompletedReductionSquareEdges S T B D)
    (e' : CompletedReductionSquareEdges S' T' B' D')
    (s : S ⟶ S') (t : T ⟶ T') (b : B ⟶ B') (d : D ⟶ D') : Prop :=
  e.upper ≫ t = s ≫ e'.upper ∧
  e.lower.hom ≫ d = b ≫ e'.lower.hom ∧
  e.left.hom ≫ b = s ≫ e'.left.hom ∧
  e.right.hom ≫ d = t ≫ e'.right.hom

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

/-- The four finite vertices, in the order S reduced, T reduced, B_n, D_n.
Source: blueprint order 1347, displayed reduction square
(blueprint: lemma-weil-pbc-completed-map-reduction). -/
def AdicCoefficientDatum.completedReductionVertexFunctor (n : ℕ) (i : Fin 4) :
    d.derived X ⥤ DerivedCategory (proEtaleRingModules Y' (d.finiteRing Y' n)) :=
  ![d.push f ⋙ d.completedPull g ⋙ d.reduction Y' n,
    d.completedPull g' ⋙ d.push f' ⋙ d.reduction Y' n,
    d.reduction X n ⋙ d.finitePush f n ⋙ d.finitePull g n,
    d.reduction X n ⋙ d.finitePull g' n ⋙ d.finitePush f' n] i

/-- The ambient objects whose quotient reductions canonically give the four vertices:
S, T, N=Lg*Rf_*K, M=Rf'_*Lg'*K. Source: blueprint order 1347, proof step 1
(blueprint: lemma-weil-pbc-completed-map-reduction). -/
def AdicCoefficientDatum.completedReductionModelFunctor (i : Fin 4) :
    d.derived X ⥤ d.derived Y' :=
  ![d.push f ⋙ d.completedPull g, d.completedPull g' ⋙ d.push f',
    d.push f ⋙ d.pull g, d.pull g' ⋙ d.push f'] i

/-- The canonical finite identifications with quotient reductions. For B use h inverse
followed by chi; for D use h' inverse. Thus the quotient transition on the ordinary
models is the specified finite-corner transition, transported by projection formula.
Source: blueprint order 1347, proof steps 1 and 4
(blueprint: lemma-weil-pbc-completed-map-reduction). -/
def AdicCoefficientDatum.completedReductionVertexIso [IsProper f]
    (K : d.derived X) (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) (n : ℕ) (i : Fin 4) :
    (d.completedReductionVertexFunctor (f := f) (f' := f') (g := g) (g' := g') n i).obj K ≅
      (d.reduction Y' n).obj
        ((d.completedReductionModelFunctor (f := f) (f' := f') (g := g) (g' := g') i).obj K) :=
  match i with
  | 0 => Iso.refl _
  | 1 => Iso.refl _
  | 2 => (d.fourArrows sq K hK W n).h.symm ≪≫ (d.chi g n).app ((d.push f).obj K)
  | 3 => (d.fourArrows sq K hK W n).h'.symm

/-- Restrict each finite vertex to the ambient coefficient category, for comparing
successive levels. Source: blueprint order 1347, proof step 4
(blueprint: lemma-weil-pbc-completed-map-reduction). -/
def AdicCoefficientDatum.completedReductionAmbientVertexFunctor (n : ℕ) (i : Fin 4) :
    d.derived X ⥤ d.derived Y' :=
  d.completedReductionVertexFunctor (f := f) (f' := f') (g := g) (g' := g') n i ⋙
    reductionDerivedRestrict Y' (d.projection Y' n)

/-- Canonical identification of an ambient vertex with the evaluated strict quotient
tower of its model. This uses the normalized K-flat evaluation comparison, never an
arbitrary isomorphism. Source: blueprint order 1347, proof step 4
(blueprint: lemma-weil-pbc-completed-map-reduction). -/
def AdicCoefficientDatum.completedReductionVertexEvaluation [IsProper f]
    (K : d.derived X) (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) (n : ℕ) (i : Fin 4) :
    (d.completedReductionAmbientVertexFunctor
      (f := f) (f' := f') (g := g) (g' := g') n i).obj K ≅
      completedTowerDerivedSequence Y' d
        ((completedReductionTower Y' d).obj
          ((d.completedReductionModelFunctor
            (f := f) (f' := f') (g := g) (g' := g') i).obj K)) n :=
  (reductionDerivedRestrict Y' (d.projection Y' n)).mapIso
      (d.completedReductionVertexIso sq K hK W n i) ≪≫
    (asIso ((completedReductionEvaluation Y' d n).app
      ((d.completedReductionModelFunctor
        (f := f) (f' := f') (g := g) (g' := g') i).obj K))).symm

/-- The actual consecutive quotient transition, transported through the canonical
finite projection-formula comparisons. On S and T it is 1 tensor q_n; on B and D it
is the finite-corner transition. Source: blueprint order 1347, proof step 4
(blueprint: lemma-weil-pbc-completed-map-reduction). -/
def AdicCoefficientDatum.completedReductionVertexStep [IsProper f]
    (K : d.derived X) (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) (n : ℕ) (i : Fin 4) :
    (d.completedReductionAmbientVertexFunctor
      (f := f) (f' := f') (g := g) (g' := g') (n + 1) i).obj K ⟶
      (d.completedReductionAmbientVertexFunctor
        (f := f) (f' := f') (g := g) (g' := g') n i).obj K :=
  (d.completedReductionVertexEvaluation sq K hK W (n + 1) i).hom ≫
    completedTowerDerivedStep Y' d
      ((completedReductionTower Y' d).obj
        ((d.completedReductionModelFunctor
          (f := f) (f' := f') (g := g) (g' := g') i).obj K)) n ≫
    (d.completedReductionVertexEvaluation sq K hK W n i).inv

/-- The published reduction square after exact restriction to ambient coefficients.
Source: blueprint order 1347, transition paragraph
(blueprint: lemma-weil-pbc-completed-map-reduction). -/
def AdicCoefficientDatum.completedReductionAmbientSquare [IsProper f]
    (K : d.derived X) (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) (n : ℕ) :
    CompletedReductionSquareEdges
      ((d.completedReductionAmbientVertexFunctor
        (f := f) (f' := f') (g := g) (g' := g') n 0).obj K)
      ((d.completedReductionAmbientVertexFunctor
        (f := f) (f' := f') (g := g) (g' := g') n 1).obj K)
      ((d.completedReductionAmbientVertexFunctor
        (f := f) (f' := f') (g := g) (g' := g') n 2).obj K)
      ((d.completedReductionAmbientVertexFunctor
        (f := f) (f' := f') (g := g) (g' := g') n 3).obj K) where
  upper := (reductionDerivedRestrict Y' (d.projection Y' n)).map
    (d.completedReductionSquare sq K hK W n).upper
  lower := (reductionDerivedRestrict Y' (d.projection Y' n)).mapIso
    (d.completedReductionSquare sq K hK W n).lower
  left := (reductionDerivedRestrict Y' (d.projection Y' n)).mapIso
    (d.completedReductionSquare sq K hK W n).left
  right := (reductionDerivedRestrict Y' (d.projection Y' n)).mapIso
    (d.completedReductionSquare sq K hK W n).right

/-- Reduction of the specified completed map, conjugated by alpha_n and delta_n,
is precisely the specified finite exchange, in the quotient-coefficient category.
Source: blueprint order 1347, detailed statement
(blueprint: lemma-weil-pbc-completed-map-reduction).
Proof, steps 1-3 of the node:
1. For N=Lg*Rf_*K and M=Rf'_*Lg'*K use arbitrary-input adic completion reduction,
transported through constant-completion equivalence. Its projection-induced maps q_A
and q_C are invertible without completeness of N or M. The definitions identify
sigma=q_A (s_A tensor 1) and tau=q_C (c inverse tensor 1).
2. The strict tower rectangle and functoriality of Rlim give V'H=H'V. The ordered
completion/direct-image comparison has dc=H', hence the completed map is c V s_A.
3. Functorial reduction applied to the ambient exchange e:N→M gives
q_C (V tensor 1)=v_n q_A. Thus tau xi_bar=v_n sigma. The finite rectangle says
h'_n v_n=v'_n h_n, so xi_bar delta=alpha v'_n in Lean composition order.
Cancel the specified alpha isomorphism to obtain the displayed conjugation. -/
theorem AdicCoefficientDatum.completedMapReduction [IsProper f]
    (K : d.derived X) (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) (n : ℕ) :
    (d.completedReductionSquare sq K hK W n).left.inv ≫
        (d.completedReductionSquare sq K hK W n).upper ≫
        (d.completedReductionSquare sq K hK W n).right.hom =
      (d.completedReductionSquare sq K hK W n).lower.hom := by
  sorry

/-- Successive reduction squares commute on every edge with the quotient transitions.
The transitions are ambient maps, not iterated unnormalized tensor over A/I^(n+2).
Source: blueprint order 1347, detailed statement and proof step 4
(blueprint: lemma-weil-pbc-completed-map-reduction).
Proof: for Z=N,M the quotient completion unit eta_Z satisfies
rho_(Z,n) (eta_Z tensor 1)=identity, by the scalar-extension adjunction and its limit
projection. Since rho is invertible by arbitrary-input completion reduction,
eta_Z tensor 1 is its inverse. Naturality of tensoring eta_Z with the quotient map,
followed by cancellation, makes rho commute with transitions. Composing with
s_A tensor 1 and c inverse tensor 1 gives transition compatibility of sigma and tau.
The strict tower equations for h,h',v' then give compatibility of alpha,delta,v'.
Functoriality of tensoring the fixed completed map gives the upper-edge equation.
The helper steps retain precisely these quotient transitions through chi and the
finite projection formula. This proves all four conjuncts of Intertwines. -/
theorem AdicCoefficientDatum.completedMapReduction_transition [IsProper f]
    (K : d.derived X) (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) (n : ℕ) :
    (d.completedReductionAmbientSquare sq K hK W (n + 1)).Intertwines
      (d.completedReductionAmbientSquare sq K hK W n)
      (d.completedReductionVertexStep sq K hK W n 0)
      (d.completedReductionVertexStep sq K hK W n 1)
      (d.completedReductionVertexStep sq K hK W n 2)
      (d.completedReductionVertexStep sq K hK W n 3) := by
  sorry

/-- Each reduction square intertwines the endomorphisms induced by an endomorphism
of K, on all four edges with the finite quotient actions retained.
Source: blueprint order 1347, detailed statement and proof step 5
(blueprint: lemma-weil-pbc-completed-map-reduction).
Proof: tower compatibility gives the four finite operator equations for h,h',v,v'.
Rlim functoriality gives their limit equations. Completed-pullback functoriality
intertwines s_A, and naturality of the direct-image/Rlim comparison intertwines d;
since c=d inverse H', it intertwines c as well. Apply arbitrary-input functorial
adic reduction to the endomorphisms of N and M, with the unit-preserving constant-
completion comparisons. This intertwines q_A,q_C, hence sigma,tau and alpha,delta.
The ordered formula xi=c V s_A intertwines the induced endomorphisms of S and T.
Tensoring gives the upper-edge equality; finite exchange naturality gives the lower.
These are exactly the four equations in Intertwines. -/
theorem AdicCoefficientDatum.completedMapReduction_endomorphism [IsProper f]
    (K : d.derived X) (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) (n : ℕ) (k : K ⟶ K) :
    (d.completedReductionSquare sq K hK W n).Intertwines
      (d.completedReductionSquare sq K hK W n)
      ((d.completedReductionVertexFunctor
        (f := f) (f' := f') (g := g) (g' := g') n 0).map k)
      ((d.completedReductionVertexFunctor
        (f := f) (f' := f') (g := g) (g' := g') n 1).map k)
      ((d.completedReductionVertexFunctor
        (f := f) (f' := f') (g := g) (g' := g') n 2).map k)
      ((d.completedReductionVertexFunctor
        (f := f) (f' := f') (g := g) (g' := g') n 3).map k) := by
  sorry

end AlgebraicGeometry.Scheme
