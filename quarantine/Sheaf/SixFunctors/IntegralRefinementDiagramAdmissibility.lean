/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
public import Sheaf.SixFunctors.IntegralSystemExpressionDomain
public import Sheaf.Paper.FiniteFieldFiber
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage
import Sheaf.AlgebraicGeometry.FiniteTypeGeometryFibreBound
import Sheaf.Paper.ProEtaleScalarMateNormalization
import Sheaf.Paper.ProperEtaleOriginScalarIsomorphism
import Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus
import Sheaf.Paper.OpenExtensionFiniteTor
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.Paper.NormalizedEtaleOriginWitnesses
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.Paper.CoefficientSystemDerivedComparison
import Sheaf.SixFunctors.OpenTensorNormalization
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Admissibility of integral compactification refinement diagrams

Source: blueprint, exceptional inverse image, extracted normalized coefficient argument,
old step 9; Stacks 09B1, 0F0G, 0GL1 and 0B56
(blueprint: lem-sf-integral-refinement-diagram-admissibility).

The finite list retains the empty word, each open prefix, the refinement proper images
and their composite, each expanded proper/open word, and the compact-support constructors.
Identity diagrams are obtained by taking both refinements to be identities.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- A common Tor interval on the actual evaluated positive levels, with exponent `n+1`.
Source: blueprint old step 9, the interval invariant
(blueprint: lem-sf-integral-refinement-diagram-admissibility). -/
def refinementTorInterval (W : Scheme.{u}) (M : System l E W) (a b : ℤ) : Prop :=
  ∀ n : ℕ, HasProEtaleTorAmplitude W (Padic.coefficientExtensionRing l E (n + 1))
    ((coefficientSequenceDerivedEvaluation l E W n).obj M) a b

/-- The sharp open-step estimate preserves any chosen input Tor interval.
Source: Stacks 0GL1 and blueprint lem-trf-open-ctf
(blueprint: lem-sf-integral-refinement-diagram-admissibility). -/
def refinementOpenEstimate (o : Operations l E) {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j] (M : System l E U) : Prop :=
  ∀ a b : ℤ, refinementTorInterval l E U M a b →
    refinementTorInterval l E V ((Operations.shriek l E o j).obj M) a b

/-- The proper-step estimate for every nonnegative source dimension bound. In particular
zero is allowed for an empty source. Source: Stacks 0F0G and the direct-image ctf bound
(blueprint: lem-sf-integral-refinement-diagram-admissibility). -/
def refinementProperEstimate (o : Operations l E) {U V : Scheme.{u}}
    (p : U ⟶ V) (M : System l E U) : Prop :=
  ∀ d : ℕ, topologicalKrullDim U ≤ (d : WithBot ℕ∞) →
    ∀ a b : ℤ, refinementTorInterval l E U M a b →
      refinementTorInterval l E V ((Operations.push l E o p).obj M) a (b + 2 * (d : ℤ))

/-- The arrows of a refinement as an actual morphism over the original base.
Source: blueprint compactification refinement diagrams, old step 9
(blueprint: lem-sf-integral-refinement-diagram-admissibility). -/
def refinementOver {B : Scheme.{u}} {X Y : Over B} {f : X ⟶ Y}
    {c d : Compactification f.left} (r : c.Refinement d) :
    compactAmbient (f := f) c ⟶ compactAmbient (f := f) d :=
  Over.homMk r.hom ((Category.assoc _ _ _).symm.trans
    (congrArg (fun g ↦ g ≫ Y.hom) r.hom_g))

/-- The eighteen words of a binary composable-refinement diagram, including all prefixes.
Taking `c` constant and `r,s` identities gives the identity refinement diagram.
The entries include the input, three opens, images under r, s and their composite,
nested proper images, all their final proper images, and three compact-support expressions.
Source: blueprint old step 9, finite-word bookkeeping
(blueprint: lem-sf-integral-refinement-diagram-admissibility). -/
def refinementDiagramWords {B : Scheme.{u}} {X Y : Over B} (f : X ⟶ Y)
    (c : Fin 3 → Compactification f.left)
    (r : (c 0).Refinement (c 1)) (s : (c 1).Refinement (c 2))
    (hq : ∀ i, QuasiCompact (c i).i) :
    Fin 18 → Σ W : Over B, Expression B (ULift.{u} Unit) (fun _ ↦ X) W
  | ⟨0, _⟩ => ⟨X, .var ⟨()⟩⟩
  | ⟨1, _⟩ => ⟨compactAmbient (c 0),
      .shriek (compactOpen (c 0)) (c 0).isOpenImmersion (hq 0) (.var ⟨()⟩)⟩
  | ⟨2, _⟩ => ⟨compactAmbient (c 1),
      .shriek (compactOpen (c 1)) (c 1).isOpenImmersion (hq 1) (.var ⟨()⟩)⟩
  | ⟨3, _⟩ => ⟨compactAmbient (c 2),
      .shriek (compactOpen (c 2)) (c 2).isOpenImmersion (hq 2) (.var ⟨()⟩)⟩
  | ⟨4, _⟩ => ⟨compactAmbient (c 1), .push (refinementOver r) r.isProper
      (.shriek (compactOpen (c 0)) (c 0).isOpenImmersion (hq 0) (.var ⟨()⟩))⟩
  | ⟨5, _⟩ => ⟨compactAmbient (c 2), .push (refinementOver s) s.isProper
      (.shriek (compactOpen (c 1)) (c 1).isOpenImmersion (hq 1) (.var ⟨()⟩))⟩
  | ⟨6, _⟩ => ⟨compactAmbient (c 2), .push (refinementOver s) s.isProper
      (.push (refinementOver r) r.isProper
        (.shriek (compactOpen (c 0)) (c 0).isOpenImmersion (hq 0) (.var ⟨()⟩)))⟩
  | ⟨7, _⟩ => ⟨compactAmbient (c 2),
      .push (refinementOver (r.comp s)) (r.comp s).isProper
        (.shriek (compactOpen (c 0)) (c 0).isOpenImmersion (hq 0) (.var ⟨()⟩))⟩
  | ⟨8, _⟩ => ⟨Y, .push (compactProper (c 0)) (c 0).isProper
      (.shriek (compactOpen (c 0)) (c 0).isOpenImmersion (hq 0) (.var ⟨()⟩))⟩
  | ⟨9, _⟩ => ⟨Y, .push (compactProper (c 1)) (c 1).isProper
      (.shriek (compactOpen (c 1)) (c 1).isOpenImmersion (hq 1) (.var ⟨()⟩))⟩
  | ⟨10, _⟩ => ⟨Y, .push (compactProper (c 2)) (c 2).isProper
      (.shriek (compactOpen (c 2)) (c 2).isOpenImmersion (hq 2) (.var ⟨()⟩))⟩
  | ⟨11, _⟩ => ⟨Y, .push (compactProper (c 1)) (c 1).isProper
      (.push (refinementOver r) r.isProper
        (.shriek (compactOpen (c 0)) (c 0).isOpenImmersion (hq 0) (.var ⟨()⟩)))⟩
  | ⟨12, _⟩ => ⟨Y, .push (compactProper (c 2)) (c 2).isProper
      (.push (refinementOver s) s.isProper
        (.shriek (compactOpen (c 1)) (c 1).isOpenImmersion (hq 1) (.var ⟨()⟩)))⟩
  | ⟨13, _⟩ => ⟨Y, .push (compactProper (c 2)) (c 2).isProper
      (.push (refinementOver s) s.isProper (.push (refinementOver r) r.isProper
        (.shriek (compactOpen (c 0)) (c 0).isOpenImmersion (hq 0) (.var ⟨()⟩))))⟩
  | ⟨14, _⟩ => ⟨Y, .push (compactProper (c 2)) (c 2).isProper
      (.push (refinementOver (r.comp s)) (r.comp s).isProper
        (.shriek (compactOpen (c 0)) (c 0).isOpenImmersion (hq 0) (.var ⟨()⟩)))⟩
  | ⟨15, _⟩ => ⟨Y, .compactSupport f (c 0) (.var ⟨()⟩)⟩
  | ⟨16, _⟩ => ⟨Y, .compactSupport f (c 1) (.var ⟨()⟩)⟩
  | _ => ⟨Y, .compactSupport f (c 2) (.var ⟨()⟩)⟩

/-- The local interval estimate at a word's last constructor. The diagram list retains
all earlier prefixes, and a compact-support constructor retains both its open and proper
steps. Inverse-image and tensor words are outside this particular diagram's syntax.
Source: blueprint old step 9, induction steps 3--5
(blueprint: lem-sf-integral-refinement-diagram-admissibility). -/
def Expression.refinementStepBounds (o : Operations l E) {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {W : Over B} (e : Expression B I X W)
    (M : ∀ i, System l E (X i).left) : Prop :=
  match e with
  | .var _ => True
  | .push f _ e => refinementProperEstimate l E o f.left (e.systemObj l E o M)
  | .shriek j hj _ e =>
    @refinementOpenEstimate l _ E _ _ _ o _ _ j.left hj (e.systemObj l E o M)
  | .compactSupport _ c e =>
    refinementOpenEstimate l E o c.i (e.systemObj l E o M) ∧
      refinementProperEstimate l E o c.g
        ((Operations.shriek l E o c.i).obj (e.systemObj l E o M))
  | .pull _ _ => False
  | .tensor _ _ => False

/-- Integral admissibility, sharp local bounds, common bounds over the entire finite
diagram, and its specified whole-system reduction identifications.
Source: blueprint exceptional inverse image, extracted old step 9; Stacks 09B1,
0F0G, 0GL1, 0B56 (blueprint: lem-sf-integral-refinement-diagram-admissibility).

Proof:
1. Retain every prefix, including hidden opens. Finite-type composition and the
finite-type geometry fibre bound give finite dimensions for all sources, without
absolute separatedness. Empty sources allow the nonnegative bound zero.
2. At the input, actual reconstruction normalizes the reduction system. Integral
constructibility and the assumed Tor interval give uniform constructibility and
cohomological bounds. The finite-ring derived-origin equivalence and normalized
etale-origin-witness theorem lift the actual transitions uniquely, with their cocycle.
3. Exact open extension preserves constructibility, cohomology and the chosen Tor
interval (lem-trf-open-ctf). The open tensor normalization identifies the actual
transition adjoint with open extension of the invertible input transition adjoint.
Apply step 2's origin procedure to the result, including every hidden open prefix.
4. System derived-image evaluation identifies each proper output with the proper
finite-level image, with its actual transitions. The direct-image ctf theorem gives
Tor interval [a,b+2d]. Compatible bounded origins satisfy the hypotheses of the proper
etale-origin scalar isomorphism, so its canonical scalar comparison is invertible.
5. Scalar-mate normalization identifies the actual proper output transition adjoint
with this scalar comparison followed by proper image of the input transition adjoint.
Both factors are invertible. The quotient cocycle is the actual system cocycle;
step 2 supplies compatible bounded origins for the proper output, also for r and s.
6. Induct over the finite prefixes. Opens keep the upper endpoint and each proper
step adds twice its source dimension bound. Take the maximum of the finitely many
upper endpoints for a single interval, independently of the coefficient level.
The zero input, empty sources and identity refinements obey the same estimates.
7. These are exactly the expression-domain conditions, so the supplied realization
comparisons apply. Actual reconstruction makes each realized object complete; its
reductions are constructible with the bounds just proved. The identification with
its reduction system is reduction of the inverse realization comparison followed by
the actual reconstruction counit. The realization normalization equation identifies
this map with the inverse of the recorded reduction isomorphism, in the whole derived
system category, hence with every quotient transition retained.
-/
theorem integralRefinementDiagramAdmissibility
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    {X Y : Over (Spec (CommRingCat.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (c : Fin 3 → Compactification f.left)
    (r : (c 0).Refinement (c 1)) (s : (c 1).Refinement (c 2))
    (hq : ∀ i, QuasiCompact (c i).i)
    (K : Integral l E X.left) (hK : sfIntegralConstructible l E X.left K)
    (a b : ℤ) (hab : a ≤ b)
    (hTor : ∀ n : ℕ,
      HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension l E X.left n).obj K) a b) :
    (∃ d : ℕ, ∀ q : Fin 18,
      topologicalKrullDim (refinementDiagramWords f c r s hq q).1.left ≤
        (d : WithBot ℕ∞)) ∧
    (∃ B : ℤ, a ≤ B ∧ ∀ q : Fin 18, ∀ n : ℕ,
      proEtaleCohomologicalSupport
          ((coefficientSequenceDerivedEvaluation l E
            (refinementDiagramWords f c r s hq q).1.left n).obj
            ((refinementDiagramWords f c r s hq q).2.systemObj l E o
              ((inputReduction l E (fun _ : ULift.{u} Unit ↦ X)).obj (fun _ ↦ K)))) ⊆
        Set.Icc a B ∧
      refinementTorInterval l E (refinementDiagramWords f c r s hq q).1.left
        ((refinementDiagramWords f c r s hq q).2.systemObj l E o
          ((inputReduction l E (fun _ : ULift.{u} Unit ↦ X)).obj (fun _ ↦ K))) a B) ∧
    (∀ q : Fin 18,
      (refinementDiagramWords f c r s hq q).2.refinementStepBounds l E o
        ((inputReduction l E (fun _ : ULift.{u} Unit ↦ X)).obj (fun _ ↦ K))) ∧
    (∀ q : Fin 18,
      ∃ (g : (refinementDiagramWords f c r s hq q).2.geometric)
        (h : (refinementDiagramWords f c r s hq q).2.domain l E o (fun _ ↦ K)),
        sfIntegralConstructible l E (refinementDiagramWords f c r s hq q).1.left
            (((refinementDiagramWords f c r s hq q).2.evaluate
              (integralInterpretation l E)).obj (fun _ ↦ K)) ∧
        (R.reduction _ g).inv.app ⟨(fun _ ↦ K), h⟩ =
          (calculus l E (refinementDiagramWords f c r s hq q).1.left).reduction.map
              ((R.comparison _ g).inv.app ⟨(fun _ ↦ K), h⟩) ≫
            (calculus l E (refinementDiagramWords f c r s hq q).1.left).adjunction.counit.app
              ((refinementDiagramWords f c r s hq q).2.systemObj l E o
                ((inputReduction l E (fun _ : ULift.{u} Unit ↦ X)).obj (fun _ ↦ K)))) := by
  sorry

end WeilConjectures.IntegralSystemRealization
