/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationSystemRealization
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemExpressionDomain
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.SixFunctors.IntegralSystemRealization.CompletedShriekCompositionLaws
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImageSupplement
import WeilConjectures.AlgebraicGeometry.Open.OpenExtensionFiniteTor
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientFlatModel
import WeilConjectures.SmoothPurity.Supporting.DirectImagesConstructible
import WeilConjectures.AlgebraicGeometry.BaseChangeDimension
import Mathlib.Tactic.FinCases

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

private theorem tor_of_iso {W : Scheme.{u}} {A : Type u} [CommRing A]
    {M N : proEtaleDerivedCategory W A} (e : M ≅ N) {a b : ℤ}
    (h : HasProEtaleTorAmplitude W A N a b) : HasProEtaleTorAmplitude W A M a b := by
  refine ⟨h.1, ?_⟩
  rintro L P ⟨q⟩ f hf hP V i hi
  exact h.2 L P ⟨q ≪≫ e⟩ f hf hP V i hi

private theorem tor_mono {W : Scheme.{u}} {A : Type u} [CommRing A]
    {M : proEtaleDerivedCategory W A} {a b B : ℤ} (hb : b ≤ B)
    (h : HasProEtaleTorAmplitude W A M a b) : HasProEtaleTorAmplitude W A M a B := by
  refine ⟨h.1.trans hb, ?_⟩
  intro L P hL f hf hP V i hi
  exact h.2 L P hL f hf hP V i (hi.imp_right (lt_of_le_of_lt hb))

private theorem dimension_bound {k : Type u} [Field k]
    (W : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] :
    ∃ d : ℕ, topologicalKrullDim W.left ≤ (d : WithBot ℕ∞) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le_of_isPullback W.hom
  exact ⟨d, hd k (𝟙 _) (𝟙 _) W.hom (IsPullback.of_horiz_isIso ⟨by simp⟩)⟩

private theorem support_of_tor (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (W : Over (Spec (CommRingCat.of D.k))) (n : ℕ)
    (M : proEtaleDerivedCategory W.left (Padic.coefficientExtensionRing l E (n + 1)))
    (hc : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W.left M)
    {a b : ℤ} (ht : HasProEtaleTorAmplitude W.left
      (Padic.coefficientExtensionRing l E (n + 1)) M a b) :
    proEtaleCohomologicalSupport M ⊆ Set.Icc a b := by
  let (x : W.left) : Invertible (l : W.left.residueField x) :=
    (show IsUnit (l : W.left.residueField x) from by
      simpa only [map_natCast] using (finiteFieldDatumPrimeUnit D l hl).map
        (W.hom.residueFieldAlgebraMap x)).invertible
  obtain ⟨P, _, hz, ⟨eP⟩⟩ :=
    (finiteCoefficient_torAmplitude_iff_flatModel D l hl E (n + 1) (Nat.succ_pos n)
      W.left M hc a b ht.1).1 ht
  intro i hi
  by_contra h
  apply hi
  have hout : i < a ∨ b < i := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using h
  exact ((HomologicalComplex.ExactAt.of_isZero (hz i hout)).isZero_homology).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso eP ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app P)

private theorem open_estimate (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) {U V : Over (Spec (CommRingCat.of D.k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (j : U ⟶ V) [IsOpenImmersion j.left]
    (M : System l E U.left) (hM : Good l E U.left M) :
    refinementOpenEstimate l E o j.left M := by
  let : U.left.Over (Spec (.of D.k)) := ⟨U.hom⟩
  let : V.left.Over (Spec (.of D.k)) := ⟨V.hom⟩
  let : j.left.IsOver (Spec (.of D.k)) := ⟨j.w⟩
  have : LocallyOfFiniteType (U.left ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType U.hom›
  have : QuasiCompact (U.left ↘ Spec (.of D.k)) := ‹QuasiCompact U.hom›
  have : LocallyOfFiniteType (V.left ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType V.hom›
  have : QuasiCompact (V.left ↘ Spec (.of D.k)) := ‹QuasiCompact V.hom›
  intro a b ht n
  obtain ⟨c, d, t, v, _, _, hb⟩ := hM.2.1
  have h := finiteStageDerivedExtensionByZero_constructibleFiniteTor
    D l hl E (n + 1) (Nat.succ_pos n) j.left
    ((coefficientSequenceDerivedEvaluation l E U.left n).obj M)
    (hb n).1 ⟨a, b, ht n⟩
  exact tor_of_iso (((o.openEvaluation j.left).evaluation n).app M) (h.2.2 a b (ht n))

private theorem proper_estimate (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) {U V : Over (Spec (CommRingCat.of D.k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (p : U ⟶ V) [IsProper p.left]
    (M : System l E U.left) (hM : Good l E U.left M) :
    refinementProperEstimate l E o p.left M := by
  intro d hd a b ht n
  obtain ⟨c, v, t, w, _, _, hb⟩ := hM.2.1
  have h := ProEtale.finiteCoefficientDirectImage_boundedConstructible_torAmplitude
    D l hl E (n + 1) (Nat.succ_pos n) U V p d hd a b
    ⟨(hb n).1, a, b, ht n⟩ (ht n)
  exact tor_of_iso (((o.evaluation p.left).evaluation n).app M) h.2

private theorem geometric_root {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {W : Over B} (e : Expression B I X W) (h : e.geometric) :
    LocallyOfFiniteType W.hom ∧ QuasiCompact W.hom := by
  cases e <;> exact ⟨h.1, h.2.1⟩

private theorem word_interval (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))} (e : Expression _ I X W)
    (ge : e.geometric) (he : e.isSupportWord) (K : ∀ i, Integral l E (X i).left)
    (hK : ∀ i, sfIntegralConstructible l E (X i).left (K i)) (a b : ℤ) (hab : a ≤ b)
    (ht : ∀ i, refinementTorInterval l E (X i).left
      ((calculus l E (X i).left).reduction.obj (K i)) a b) :
    ∃ B : ℤ, a ≤ B ∧
      refinementTorInterval l E W.left
        (e.systemObj l E o ((inputReduction l E X).obj K)) a B ∧
      e.refinementStepBounds l E o ((inputReduction l E X).obj K) := by
  induction e with
  | var i => exact ⟨b, hab, ht i, trivial⟩
  | pull f e ih => exact False.elim he
  | tensor e t ihe iht => exact False.elim he
  | @push U V f hp e ih =>
    obtain ⟨B, hB, htor, _⟩ := ih ge.2.2 he
    have : IsProper f.left := hp
    have : LocallyOfFiniteType U.hom := (geometric_root e ge.2.2).1
    have : QuasiCompact U.hom := (geometric_root e ge.2.2).2
    have : LocallyOfFiniteType V.hom := ge.1
    have : QuasiCompact V.hom := ge.2.1
    obtain ⟨d, hd⟩ := dimension_bound U
    have hg := (completedShriekIntegralBounds l E D hl o R e ge.2.2 he K hK).1.2
    have hs := proper_estimate l E D hl o f _ (e.admissibleGood l E o _ hg)
    exact ⟨B + 2 * (d : ℤ), by omega, hs d hd a B htor, hs⟩
  | @shriek U V j hj hq e ih =>
    obtain ⟨B, hB, htor, _⟩ := ih ge.2.2 he
    have : IsOpenImmersion j.left := hj
    have : LocallyOfFiniteType U.hom := (geometric_root e ge.2.2).1
    have : QuasiCompact U.hom := (geometric_root e ge.2.2).2
    have : LocallyOfFiniteType V.hom := ge.1
    have : QuasiCompact V.hom := ge.2.1
    have hg := (completedShriekIntegralBounds l E D hl o R e ge.2.2 he K hK).1.2
    have hs := open_estimate l E D hl o j _ (e.admissibleGood l E o _ hg)
    exact ⟨B, hB, hs a B htor, hs⟩
  | @compactSupport U V f c e ih =>
    have ge' := ge.2.2.2.2.2
    obtain ⟨B, hB, htor, _⟩ := ih ge' he
    have : LocallyOfFiniteType U.hom := (geometric_root e ge').1
    have : QuasiCompact U.hom := (geometric_root e ge').2
    have : LocallyOfFiniteType V.hom := ge.1
    have : QuasiCompact V.hom := ge.2.1
    have : LocallyOfFiniteType (compactAmbient (f := f) c).hom :=
      inferInstanceAs (LocallyOfFiniteType (c.g ≫ V.hom))
    have : QuasiCompact (compactAmbient (f := f) c).hom :=
      inferInstanceAs (QuasiCompact (c.g ≫ V.hom))
    have : IsOpenImmersion (compactOpen (f := f) c).left := c.isOpenImmersion
    have : IsProper (compactProper (f := f) c).left := c.isProper
    obtain ⟨d, hd⟩ := dimension_bound (compactAmbient (f := f) c)
    have hg := (completedShriekIntegralBounds l E D hl o R
      (.compactSupport f c e) ge he K hK).1.2
    have hs := open_estimate l E D hl o (compactOpen (f := f) c) _
      (e.admissibleGood l E o _ hg.2.1)
    have hp := proper_estimate l E D hl o (compactProper (f := f) c) _ hg.2.2
    exact ⟨B + 2 * (d : ℤ), by omega, hp d hd a B (hs a B htor), hs, hp⟩

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
  classical
  have (i : Fin 3) : LocallyOfFiniteType (compactAmbient (f := f) (c i)).hom :=
    inferInstanceAs (LocallyOfFiniteType ((c i).g ≫ Y.hom))
  have (i : Fin 3) : QuasiCompact (compactAmbient (f := f) (c i)).hom :=
    inferInstanceAs (QuasiCompact ((c i).g ≫ Y.hom))
  have ge (q : Fin 18) : (refinementDiagramWords f c r s hq q).2.geometric := by
    fin_cases q <;> dsimp [refinementDiagramWords, Expression.geometric]
    all_goals repeat' apply And.intro
    all_goals first | trivial | infer_instance
  have hw (q : Fin 18) : (refinementDiagramWords f c r s hq q).2.isSupportWord := by
    fin_cases q <;> trivial
  have hd (q : Fin 18) := geometric_root _ (ge q)
  have hdims (q : Fin 18) : ∃ d : ℕ,
      topologicalKrullDim (refinementDiagramWords f c r s hq q).1.left ≤
        (d : WithBot ℕ∞) := by
    have := (hd q).1
    have := (hd q).2
    exact dimension_bound _
  choose ds hds using hdims
  have hdom (q : Fin 18) := completedShriekIntegralBounds l E D _hl o R
    (refinementDiagramWords f c r s hq q).2 (ge q) (hw q) (fun _ ↦ K) (fun _ ↦ hK)
  have hinput : ∀ i : ULift.{u} Unit, refinementTorInterval l E X.left
      ((calculus l E X.left).reduction.obj K) a b := by
    intro i n
    exact tor_of_iso (((calculus l E X.left).reductionEvaluation n).app K) (hTor n)
  have hwords (q : Fin 18) := word_interval l E D _hl o R
    (refinementDiagramWords f c r s hq q).2 (ge q) (hw q) (fun _ ↦ K) (fun _ ↦ hK)
    a b hab hinput
  choose Bs hBs using hwords
  obtain ⟨B, hB⟩ := (Set.finite_range Bs).bddAbove
  have hle (q : Fin 18) : Bs q ≤ B := hB (Set.mem_range_self q)
  refine ⟨⟨Finset.univ.sup ds, fun q ↦ (hds q).trans ?_⟩,
    ⟨B, (hBs 0).1.trans (hle 0), ?_⟩, fun q ↦ (hBs q).2.2, ?_⟩
  · exact_mod_cast Finset.le_sup (Finset.mem_univ q)
  · intro q n
    have ht : refinementTorInterval l E
        (refinementDiagramWords f c r s hq q).1.left
        ((refinementDiagramWords f c r s hq q).2.systemObj l E o
          ((inputReduction l E (fun _ : ULift.{u} Unit ↦ X)).obj (fun _ ↦ K))) a B :=
      fun n ↦ tor_mono (hle q) ((hBs q).2.1 n)
    have hg := (refinementDiagramWords f c r s hq q).2.admissibleGood l E o _
      (hdom q).1.2
    obtain ⟨v, w, t, z, _, _, hb⟩ := hg.2.1
    exact ⟨support_of_tor l E D _hl _ n _ (hb n).1 (ht n), ht⟩
  · intro q
    refine ⟨ge q, (hdom q).1, (hdom q).2, ?_⟩
    have hn := R.normalization (refinementDiagramWords f c r s hq q).2 (ge q)
      ⟨(fun _ ↦ K), (hdom q).1⟩
    rw [← hn, ← Category.assoc, ← Functor.map_comp]
    simp

end WeilConjectures.IntegralSystemRealization
