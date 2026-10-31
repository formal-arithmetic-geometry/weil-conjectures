/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralCompactificationSystemRealization
public import WeilConjectures.SixFunctors.IntegralOperationShiftData
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SixFunctors.GeneratorReductionStatement
import WeilConjectures.SixFunctors.SystemPrimitiveComparisonShift
import Mathlib.CategoryTheory.Shift.CommShift

/-! # System proper/open, exchange and projection shift squares

Source: blueprint fix-prop-coherence.proof.md, maps-used sentence, adic transport Step 2;
the conditional obligation and its six proof steps are agent-formulated
(blueprint: lem-pur-system-proper-open-projection-shift).

The indices below are the actual published maps. A single-slot context fixes every
other operand. Finite pastings retain their intermediate contexts as domain tests.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
namespace SystemShift

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {B : Scheme.{u}} (o : Operations l E)

/-- The existing explicit one-slot context on the actual strict-system interpretation.
Source: the designated-slot convention
(blueprint: lem-pur-system-proper-open-projection-shift). -/
abbrev Slot (A W : Over B) := Expression.SlotContext (systemInterpretation l E o) A W

/-- The equation uses exactly the fixed cochain comparisons, including the signed
second tensor slot. Source: obligation, displayed chi equation
(blueprint: lem-pur-system-proper-open-projection-shift). -/
def Square {A W : Over B} (e t : Slot l E o A W)
    (τ : ∀ M : System l E A.left, e.evaluate.obj M ⟶ t.evaluate.obj M)
    (M : System l E A.left) (r : ℤ) : Prop :=
  τ (M⟦r⟧) ≫ (t.shift (systemShifts l E o) r M).hom =
    (e.shift (systemShifts l E o) r M).hom ≫ (τ M)⟦r⟧'

/-- Finite-type geometry of every scheme and separated finite-type pullback in a slot.
Source: the field-base and operation-domain hypotheses
(blueprint: lem-pur-system-proper-open-projection-shift). -/
def Geometry {A : Over B} : {W : Over B} → Slot l E o A W → Prop
  | _, .input => LocallyOfFiniteType A.hom ∧ QuasiCompact A.hom
  | W, .pull f e => LocallyOfFiniteType W.hom ∧ QuasiCompact W.hom ∧
      IsSeparated f.left ∧ LocallyOfFiniteType f.left ∧ QuasiCompact f.left ∧ Geometry e
  | W, .push _ _ e => LocallyOfFiniteType W.hom ∧ QuasiCompact W.hom ∧ Geometry e
  | W, .shriek _ _ _ e => LocallyOfFiniteType W.hom ∧ QuasiCompact W.hom ∧ Geometry e
  | W, .compactSupport f _ e => LocallyOfFiniteType W.hom ∧ QuasiCompact W.hom ∧
      IsSeparated f.left ∧ LocallyOfFiniteType f.left ∧ QuasiCompact f.left ∧ Geometry e
  | _, .tensorLeft e _ | _, .tensorRight _ e => Geometry e

/-- All vertices and fixed operands have compatible origins and common finite bounds.
Source: the admissible-system hypothesis
(blueprint: lem-pur-system-proper-open-projection-shift). -/
def Domain {A : Over B} (M : System l E A.left) (lo hi tl th : ℤ) :
    {W : Over B} → Slot l E o A W → Prop
  | W, e => GeneratorReduction.SystemAdmissible l E W.left (e.evaluate.obj M) lo hi tl th ∧
    match e with
    | .input => True
    | .pull _ e | .push _ _ e | .shriek _ _ _ e => Domain M lo hi tl th e
    | .compactSupport _ cf e => Domain M lo hi tl th e ∧
        GeneratorReduction.SystemAdmissible l E cf.Z
          ((Operations.shriek l E o cf.i).obj (e.evaluate.obj M)) lo hi tl th
    | .tensorLeft e N | .tensorRight N e =>
        Domain M lo hi tl th e ∧ GeneratorReduction.SystemAdmissible l E W.left N lo hi tl th

variable (c : Compositors l E o) (a : OpenComparisons l E o c)

/-- Exactly the primitive factors used in the displayed formulas: pullback and tensor
comparisons, clopen component maps, adjunctions, compositors and normalized beta/gamma.
These are hypotheses of the conditional obligation, not its conclusions.
Source: obligation, primitive-map hypothesis and proof steps 1--2, 4--6
(blueprint: lem-pur-system-proper-open-projection-shift). -/
inductive Generator : {A W : Over B} → (e t : Slot l E o A W) →
    (∀ M : System l E A.left, e.evaluate.obj M ⟶ t.evaluate.obj M) → Prop where
  | pullComp {U V W : Over B} (f : U ⟶ V) (g : V ⟶ W) :
    Generator (.pull (f ≫ g) .input) (.pull f (.pull g .input))
      (fun M ↦ (c.pullComp f.left g.left).hom.app M)
  | square {U V W Z : Over B} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      (w : k.left ≫ p.left = r.left ≫ i.left) :
    Generator (.pull r (.pull i .input)) (.pull k (.pull p .input))
      (fun M ↦ (c.square l E k.left r.left p.left i.left w).hom.app M)
  | tensorPullLeft {U V : Over B} (f : U ⟶ V) (N : System l E V.left) :
    Generator (.pull f (.tensorLeft .input N))
      (.tensorLeft (.pull f .input) ((pull l E f.left).obj N))
      (fun M ↦ (pullbackTensorSystemComparison l E f.left).hom.app (M, N))
  | tensorPullRight {U V : Over B} (f : U ⟶ V) (M : System l E V.left) :
    Generator (.pull f (.tensorRight M .input))
      (.tensorRight ((pull l E f.left).obj M) (.pull f .input))
      (fun N ↦ (pullbackTensorSystemComparison l E f.left).hom.app (M, N))
  | pushUnit {U V : Over B} (f : U ⟶ V) (hp : IsProper f.left) :
    Generator .input (.push f hp (.pull f .input))
      (fun M ↦ (o.direct f.left).adj.unit.app M)
  | pushCounit {U V : Over B} (f : U ⟶ V) (hp : IsProper f.left) :
    Generator (.pull f (.push f hp .input)) .input
      (fun M ↦ (o.direct f.left).adj.counit.app M)
  | openUnit {U V : Over B} (j : U ⟶ V) [hj : IsOpenImmersion j.left]
      (qj : QuasiCompact j.left) :
    Generator .input (.pull j (.shriek j hj qj .input))
      (fun M ↦ (o.extension j.left).adj.unit.app M)
  | openCounit {U V : Over B} (j : U ⟶ V) [hj : IsOpenImmersion j.left]
      (qj : QuasiCompact j.left) :
    Generator (.shriek j hj qj (.pull j .input)) .input
      (fun M ↦ (o.extension j.left).adj.counit.app M)
  | pushComp {U V W : Over B} (f : U ⟶ V) (g : V ⟶ W)
      (hf : IsProper f.left) (hg : IsProper g.left) (hfg : IsProper (f ≫ g).left) :
    Generator (.push g hg (.push f hf .input)) (.push (f ≫ g) hfg .input)
      (fun M ↦ (c.pushComp l E f.left g.left).hom.app M)
  | openComp {U V W : Over B} (j : U ⟶ V) (k : V ⟶ W)
      [hj : IsOpenImmersion j.left] [hk : IsOpenImmersion k.left]
      (qj : QuasiCompact j.left) (qk : QuasiCompact k.left)
      (qjk : QuasiCompact (j ≫ k).left) :
    Generator (.shriek k hk qk (.shriek j hj qj .input))
      (.shriek (j ≫ k) (inferInstance : IsOpenImmersion (j.left ≫ k.left)) qjk .input)
      (fun M ↦ (c.openComp l E j.left k.left).hom.app M)
  | beta {U' U V' V : Over B} (v : U' ⟶ U) (j' : U' ⟶ V')
      (j : U ⟶ V) (g : V' ⟶ V)
      [hj : IsOpenImmersion j.left] [hj' : IsOpenImmersion j'.left]
      (qj : QuasiCompact j.left) (qj' : QuasiCompact j'.left)
      (w : v.left ≫ j.left = j'.left ≫ g.left)
      (sq : IsPullback v.left j'.left j.left g.left) :
    Generator (.pull g (.shriek j hj qj .input)) (.shriek j' hj' qj' (.pull v .input))
      (fun M ↦ (a.beta v.left j'.left j.left g.left w sq).hom.app M)
  | tensorOpenLeft {U V : Over B} (j : U ⟶ V) [hj : IsOpenImmersion j.left]
      (qj : QuasiCompact j.left) (N : System l E V.left) :
    Generator (.tensorLeft (.shriek j hj qj .input) N)
      (.shriek j hj qj (.tensorLeft .input ((pull l E j.left).obj N)))
      (fun M ↦ (a.projection j.left).hom.app (M, N))
  | tensorOpenRight {U V : Over B} (j : U ⟶ V) [hj : IsOpenImmersion j.left]
      (qj : QuasiCompact j.left) (M : System l E U.left) :
    Generator (.tensorRight ((Operations.shriek l E o j.left).obj M) .input)
      (.shriek j hj qj (.tensorRight M (.pull j .input)))
      (fun N ↦ (a.projection j.left).hom.app (M, N))
  | clopen {U V : Over B} (s : U ⟶ V) [hs : IsOpenImmersion s.left]
      [IsClosedImmersion s.left] (qs : QuasiCompact s.left) (hp : IsProper s.left) :
    Generator (.shriek s hs qs .input) (.push s hp .input)
      (fun M ↦ (a.clopen s.left).hom.app M)
  | component {U V : Over B} (s : U ⟶ V) [hs : IsOpenImmersion s.left]
      [IsClosedImmersion s.left] (qs : QuasiCompact s.left) :
    Generator .input (.shriek s hs qs (.pull s .input))
      (fun M ↦ ((o.direct s.left).adj.unit ≫
        Functor.whiskerLeft (pull l E s.left) (a.clopen s.left).inv).app M)

/-- Check each actual intermediate system of a displayed factorization in one common
pair of finite intervals. Source: obligation, domain restriction
(blueprint: lem-pur-system-proper-open-projection-shift). -/
def termsBounded (terms : List (Σ W : Scheme.{u}, System l E W))
    (lo hi tl th : ℤ) : Prop :=
  ∀ T ∈ terms, GeneratorReduction.SystemAdmissible l E T.1 T.2 lo hi tl th

/-- The actual systems in both clopen factorizations, including the intermediate
systems of alpha before applying S_p. The fiber product and clopen lift are the
published ones. Source: obligation, lambda, alpha and Gamma
(blueprint: lem-pur-system-proper-open-projection-shift). -/
def properOpenTerms {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (w : k ≫ p = r ≫ i) (M : System l E U) :
    List (Σ T : Scheme.{u}, System l E T) :=
  let b := pullback.fst p i
  let q := pullback.snd p i
  let s := ProEtale.StrictTower.squareLift k r p i w
  let sr := (Operations.push l E o r).obj M
  let ji := (Operations.shriek l E o i).obj sr
  let pq := (pull l E q).obj sr
  let ps := (pull l E s).obj pq
  let js := (Operations.shriek l E o s).obj ps
  let jbpq := (Operations.shriek l E o b).obj pq
  let jbjs := (Operations.shriek l E o b).obj js
  let jkr := (Operations.shriek l E o k).obj ((pull l E r).obj sr)
  let jk := (Operations.shriek l E o k).obj M
  let pbjk := (pull l E b).obj jk
  let jsm := (Operations.shriek l E o s).obj M
  let ssm := (Operations.push l E o s).obj M
  [⟨U, M⟩, ⟨W, sr⟩, ⟨Z, ji⟩, ⟨V, (pull l E p).obj ji⟩,
    ⟨pullback p i, pq⟩, ⟨U, ps⟩, ⟨pullback p i, js⟩, ⟨V, jbpq⟩, ⟨V, jbjs⟩,
    ⟨U, (pull l E r).obj sr⟩, ⟨V, jkr⟩, ⟨V, jk⟩,
    ⟨Z, (Operations.push l E o p).obj ((pull l E p).obj ji)⟩,
    ⟨Z, (Operations.push l E o p).obj jbpq⟩,
    ⟨Z, (Operations.push l E o p).obj jbjs⟩,
    ⟨Z, (Operations.push l E o p).obj jkr⟩,
    ⟨Z, (Operations.push l E o p).obj jk⟩,
    ⟨W, (pull l E i).obj ((Operations.push l E o p).obj jk)⟩,
    ⟨pullback p i, pbjk⟩, ⟨W, (Operations.push l E o q).obj pbjk⟩,
    ⟨pullback p i, jsm⟩, ⟨W, (Operations.push l E o q).obj jsm⟩,
    ⟨pullback p i, ssm⟩, ⟨W, (Operations.push l E o q).obj ssm⟩]

/-- The actual unit, square-comparison and counit intermediates of Ex_*.
Source: obligation, exchange formula
(blueprint: lem-pur-system-proper-open-projection-shift). -/
def exchangeTerms {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z) (M : System l E V) :
    List (Σ T : Scheme.{u}, System l E T) :=
  let sm := (Operations.push l E o p).obj M
  let a := (pull l E i).obj sm
  let b := (pull l E r).obj a
  let c := (pull l E k).obj ((pull l E p).obj sm)
  let d := (pull l E k).obj M
  [⟨V, M⟩, ⟨Z, sm⟩, ⟨W, a⟩, ⟨U, b⟩, ⟨W, (Operations.push l E o r).obj b⟩,
    ⟨V, (pull l E p).obj sm⟩, ⟨U, c⟩, ⟨W, (Operations.push l E o r).obj c⟩,
    ⟨U, d⟩, ⟨W, (Operations.push l E o r).obj d⟩]

/-- The actual tensor-pullback, counit and unit intermediates of proper projection.
Source: obligation, pi formula
(blueprint: lem-pur-system-proper-open-projection-shift). -/
def projectionTerms {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : System l E X) (N : System l E Y) : List (Σ T : Scheme.{u}, System l E T) :=
  let sm := (Operations.push l E o f).obj M
  let src := (calculus l E Y).systemClosed.tensor.obj (sm, N)
  let psrc := (pull l E f).obj src
  let pn := (pull l E f).obj N
  let psm := (pull l E f).obj sm
  let middle := (calculus l E X).systemClosed.tensor.obj (psm, pn)
  let target := (calculus l E X).systemClosed.tensor.obj (M, pn)
  [⟨X, M⟩, ⟨Y, N⟩, ⟨Y, sm⟩, ⟨Y, src⟩, ⟨X, psrc⟩,
    ⟨Y, (Operations.push l E o f).obj psrc⟩, ⟨X, pn⟩, ⟨X, psm⟩, ⟨X, middle⟩,
    ⟨Y, (Operations.push l E o f).obj middle⟩, ⟨X, target⟩,
    ⟨Y, (Operations.push l E o f).obj target⟩]

/-- The open projection intermediates, including its pullback compositor.
Source: obligation, compactification-relative PF formula
(blueprint: lem-pur-system-proper-open-projection-shift). -/
def compactProjectionTerms {X Y : Scheme.{u}} {f : X ⟶ Y} (cf : Compactification f)
    (M : System l E X) (N : System l E Y) : List (Σ T : Scheme.{u}, System l E T) :=
  let jm := (Operations.shriek l E o cf.i).obj M
  let pn := (pull l E cf.g).obj N
  let jpn := (pull l E cf.i).obj pn
  let fn := (pull l E f).obj N
  let mid := (calculus l E X).systemClosed.tensor.obj (M, jpn)
  let fin := (calculus l E X).systemClosed.tensor.obj (M, fn)
  projectionTerms l E o cf.g jm N ++
    [⟨X, M⟩, ⟨cf.Z, jm⟩, ⟨cf.Z, pn⟩, ⟨X, jpn⟩, ⟨X, fn⟩,
      ⟨X, mid⟩, ⟨X, fin⟩, ⟨cf.Z, (Operations.shriek l E o cf.i).obj mid⟩,
      ⟨cf.Z, (Operations.shriek l E o cf.i).obj fin⟩,
      ⟨Y, (Operations.push l E o cf.g).obj ((Operations.shriek l E o cf.i).obj mid)⟩,
      ⟨Y, (Operations.push l E o cf.g).obj ((Operations.shriek l E o cf.i).obj fin)⟩]

/-- The proper/open, exchange and projection maps, with each tensor occurrence
listed separately. The maps are the published composites, not arbitrary arrows.
Source: obligation, the displayed lambda, Gamma, exchange and projection formulas
(blueprint: lem-pur-system-proper-open-projection-shift). -/
inductive Composite (bridge : CanonicalBridge l E o)
    (h : ProperOpenCoherence l E o c a bridge) : {A W : Over B} →
    (e t : Slot l E o A W) →
    (∀ M : System l E A.left, e.evaluate.obj M ⟶ t.evaluate.obj M) →
    (System l E A.left → ℤ → ℤ → ℤ → ℤ → Prop) → Prop where
  | gamma {U V W Z : Over B} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [hk : IsOpenImmersion k.left] [hi : IsOpenImmersion i.left]
      [qk : QuasiCompact k.left] [qi : QuasiCompact i.left]
      [hr : IsProper r.left] [hp : IsProper p.left]
      (w : k.left ≫ p.left = r.left ≫ i.left) :
    Composite bridge h (.shriek i hi qi (.push r hr .input))
      (.push p hp (.shriek k hk qk .input))
      (fun M ↦ (h.gamma k.left r.left p.left i.left w).app M)
      (fun M ↦ termsBounded l E (properOpenTerms l E o k.left r.left p.left i.left w M))
  | lambda {U V W Z : Over B} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [hk : IsOpenImmersion k.left] [hi : IsOpenImmersion i.left]
      [qk : QuasiCompact k.left] [qi : QuasiCompact i.left]
      [hr : IsProper r.left] [hp : IsProper p.left]
      (w : k.left ≫ p.left = r.left ≫ i.left) :
    Composite bridge h (.pull i (.push p hp (.shriek k hk qk .input))) (.push r hr .input)
      (fun M ↦ (properOpenLambda l E o c a k.left r.left p.left i.left w).hom.app M)
      (fun M ↦ termsBounded l E (properOpenTerms l E o k.left r.left p.left i.left w M))
  | exchange {U V W Z : Over B} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      (hr : IsProper r.left) (hp : IsProper p.left)
      (w : k.left ≫ p.left = r.left ≫ i.left)
      (_sq : IsPullback k.left r.left p.left i.left) :
    Composite bridge h (.pull i (.push p hp .input)) (.push r hr (.pull k .input))
      (fun M ↦ (properExchange l E o c k.left r.left p.left i.left w).app M)
      (fun M ↦ termsBounded l E (exchangeTerms l E o k.left r.left p.left i.left M))
  | projectionLeft {U V : Over B} (f : U ⟶ V) (hp : IsProper f.left)
      (N : System l E V.left) :
    Composite bridge h (.tensorLeft (.push f hp .input) N)
      (.push f hp (.tensorLeft .input ((pull l E f.left).obj N)))
      (fun M ↦ ((properProjection l E o f.left).app M).app N)
      (fun M ↦ termsBounded l E (projectionTerms l E o f.left M N))
  | projectionRight {U V : Over B} (f : U ⟶ V) (hp : IsProper f.left)
      (M : System l E U.left) :
    Composite bridge h (.tensorRight ((Operations.push l E o f.left).obj M) .input)
      (.push f hp (.tensorRight M (.pull f .input)))
      (fun N ↦ ((properProjection l E o f.left).app M).app N)
      (fun N ↦ termsBounded l E (projectionTerms l E o f.left M N))
  | compactExchange {U V U' V' : Over B} (f : U ⟶ V) (f' : U' ⟶ V')
      (cf : Compactification f.left) (cf' : Compactification f'.left)
      (x : U' ⟶ U) (y : V' ⟶ V) (z : cf'.Z ⟶ cf.Z)
      (wi : x.left ≫ cf.i = cf'.i ≫ z) (wp : z ≫ cf.g = cf'.g ≫ y.left)
      (si : IsPullback x.left cf'.i cf.i z) (_sp : IsPullback z cf'.g cf.g y.left) :
    Composite bridge h (.pull y (.compactSupport f cf .input))
      (.compactSupport f' cf' (.pull x .input))
      (fun M ↦ (compactificationExchange l E o c a cf cf' x.left y.left z wi wp si).app M)
      (fun M ↦ termsBounded l E
        (exchangeTerms l E o z cf'.g cf.g y.left ((Operations.shriek l E o cf.i).obj M)))
  | compactProjectionLeft {U V : Over B} (f : U ⟶ V) (cf : Compactification f.left)
      (N : System l E V.left) :
    Composite bridge h (.tensorLeft (.compactSupport f cf .input) N)
      (.compactSupport f cf (.tensorLeft .input ((pull l E f.left).obj N)))
      (fun M ↦ compactificationProjection l E o c a cf M N)
      (fun M ↦ termsBounded l E (compactProjectionTerms l E o cf M N))
  | compactProjectionRight {U V : Over B} (f : U ⟶ V) (cf : Compactification f.left)
      (M : System l E U.left) :
    Composite bridge h
      (.tensorRight (((systemInterpretation l E o).compactSupport f.left cf).obj M) .input)
      (.compactSupport f cf (.tensorRight M (.pull f .input)))
      (fun N ↦ compactificationProjection l E o c a cf M N)
      (fun N ↦ termsBounded l E (compactProjectionTerms l E o cf M N))

/-- Substitute an actual input context into an outer context.
Source: obligation, finite whiskering
(blueprint: lem-pur-system-proper-open-projection-shift). -/
def insert {A U : Over B} (f : Slot l E o A U) :
    {W : Over B} → Slot l E o U W → Slot l E o A W
  | _, .input => f
  | _, .pull v e => .pull v (insert f e)
  | _, .push v hp e => .push v hp (insert f e)
  | _, .shriek j hj qj e => .shriek j hj qj (insert f e)
  | _, .compactSupport v cf e => .compactSupport v cf (insert f e)
  | _, .tensorLeft e N => .tensorLeft (insert f e) N
  | _, .tensorRight N e => .tensorRight N (insert f e)

/-- Canonical evaluation identification for substitution, constructed recursively
by the actual unary functors and the indicated curried tensor functor.
Source: obligation, recursive composite comparisons
(blueprint: lem-pur-system-proper-open-projection-shift). -/
def insertObjIso {A U : Over B} (f : Slot l E o A U) (M : System l E A.left) :
    {W : Over B} → (e : Slot l E o U W) →
      (insert l E o f e).evaluate.obj M ≅ e.evaluate.obj (f.evaluate.obj M)
  | _, .input => Iso.refl _
  | _, .pull v e => (pull l E v.left).mapIso (insertObjIso f M e)
  | _, .push v _ e => (Operations.push l E o v.left).mapIso (insertObjIso f M e)
  | _, .shriek j hj _ e => letI := hj
      (Operations.shriek l E o j.left).mapIso (insertObjIso f M e)
  | _, .compactSupport v cf e =>
      ((systemInterpretation l E o).compactSupport v.left cf).mapIso (insertObjIso f M e)
  | W, .tensorLeft e N =>
      ((Functor.curry.obj (calculus l E W.left).systemClosed.tensor).flip.obj N).mapIso
        (insertObjIso f M e)
  | W, .tensorRight N e =>
      ((Functor.curry.obj (calculus l E W.left).systemClosed.tensor).obj N).mapIso
        (insertObjIso f M e)

/-- Actual input whiskering, using the recursively constructed endpoint identifications.
Source: obligation, finite pastings
(blueprint: lem-pur-system-proper-open-projection-shift). -/
def before {A U W : Over B} (f : Slot l E o A U) (e t : Slot l E o U W)
    (τ : ∀ M : System l E U.left, e.evaluate.obj M ⟶ t.evaluate.obj M)
    (M : System l E A.left) :
    (insert l E o f e).evaluate.obj M ⟶ (insert l E o f t).evaluate.obj M :=
  (insertObjIso l E o f M e).hom ≫ τ (f.evaluate.obj M) ≫
    (insertObjIso l E o f M t).inv

/-- Common bounds for the two boundary contexts of a map.
Source: obligation, normalized input and intermediate domains
(blueprint: lem-pur-system-proper-open-projection-shift). -/
def boundaries {A W : Over B} (e t : Slot l E o A W)
    (M : System l E A.left) (lo hi tl th : ℤ) : Prop :=
  Geometry l E o e ∧ Geometry l E o t ∧
    Domain l E o M lo hi tl th e ∧ Domain l E o M lo hi tl th t

/-- Finite pastings of the specified maps, indexed also by the actual domain test.
Every constructor retains the boundary contexts and every intermediate test.
Input whiskering uses the recursively constructed evaluation isomorphisms.
Source: obligation, final finite-pasting clause and proof steps 1, 6
(blueprint: lem-pur-system-proper-open-projection-shift). -/
inductive Pasting (bridge : CanonicalBridge l E o)
    (h : ProperOpenCoherence l E o c a bridge) : {A W : Over B} →
    (e t : Slot l E o A W) →
    (∀ M : System l E A.left, e.evaluate.obj M ⟶ t.evaluate.obj M) →
    (System l E A.left → ℤ → ℤ → ℤ → ℤ → Prop) → Type (u + 3) where
  | generator {A W : Over B} {e t : Slot l E o A W} {τ} :
    Generator l E o c a e t τ → Pasting bridge h e t τ (boundaries l E o e t)
  | composite {A W : Over B} {e t : Slot l E o A W} {τ d} :
    Composite l E o c a bridge h e t τ d → Pasting bridge h e t τ
      (fun M lo hi tl th ↦ boundaries l E o e t M lo hi tl th ∧ d M lo hi tl th)
  | id {A W : Over B} (e : Slot l E o A W) :
    Pasting bridge h e e (fun _ ↦ 𝟙 _) (boundaries l E o e e)
  | comp {A W : Over B} {e t v : Slot l E o A W} {τ σ d₁ d₂} :
    Pasting bridge h e t τ d₁ → Pasting bridge h t v σ d₂ →
      Pasting bridge h e v (fun M ↦ τ M ≫ σ M)
        (fun M lo hi tl th ↦ d₁ M lo hi tl th ∧ d₂ M lo hi tl th)
  | inverse {A W : Over B} {e t : Slot l E o A W} {τ d}
      (hτ : Pasting bridge h e t τ d) (iso : ∀ M, IsIso (τ M)) :
    Pasting bridge h t e (fun M ↦ @CategoryTheory.inv _ _ _ _ (τ M) (iso M)) d
  | pull {A U V : Over B} {e t : Slot l E o A V} {τ d} (f : U ⟶ V) :
    Pasting bridge h e t τ d → Pasting bridge h (.pull f e) (.pull f t)
      (fun M ↦ (pull l E f.left).map (τ M))
      (fun M lo hi tl th ↦ d M lo hi tl th ∧
        boundaries l E o (.pull f e) (.pull f t) M lo hi tl th)
  | push {A U V : Over B} {e t : Slot l E o A U} {τ d}
      (f : U ⟶ V) (hp : IsProper f.left) :
    Pasting bridge h e t τ d → Pasting bridge h (.push f hp e) (.push f hp t)
      (fun M ↦ (Operations.push l E o f.left).map (τ M))
      (fun M lo hi tl th ↦ d M lo hi tl th ∧
        boundaries l E o (.push f hp e) (.push f hp t) M lo hi tl th)
  | shriek {A U V : Over B} {e t : Slot l E o A U} {τ d}
      (j : U ⟶ V) [hj : IsOpenImmersion j.left] (qj : QuasiCompact j.left) :
    Pasting bridge h e t τ d → Pasting bridge h (.shriek j hj qj e) (.shriek j hj qj t)
      (fun M ↦ (Operations.shriek l E o j.left).map (τ M))
      (fun M lo hi tl th ↦ d M lo hi tl th ∧
        boundaries l E o (.shriek j hj qj e) (.shriek j hj qj t) M lo hi tl th)
  | compactSupport {A U V : Over B} {e t : Slot l E o A U} {τ d}
      (f : U ⟶ V) (cf : Compactification f.left) :
    Pasting bridge h e t τ d →
      Pasting bridge h (.compactSupport f cf e) (.compactSupport f cf t)
      (fun M ↦ ((systemInterpretation l E o).compactSupport f.left cf).map (τ M))
      (fun M lo hi tl th ↦ d M lo hi tl th ∧
        boundaries l E o (.compactSupport f cf e) (.compactSupport f cf t) M lo hi tl th)
  | tensorLeft {A W : Over B} {e t : Slot l E o A W} {τ d} (N : System l E W.left) :
    Pasting bridge h e t τ d → Pasting bridge h (.tensorLeft e N) (.tensorLeft t N)
      (fun M ↦ (calculus l E W.left).systemClosed.tensor.map (Prod.mkHom (τ M) (𝟙 N)))
      (fun M lo hi tl th ↦ d M lo hi tl th ∧
        boundaries l E o (.tensorLeft e N) (.tensorLeft t N) M lo hi tl th)
  | before {A U W : Over B} (f : Slot l E o A U) {e t : Slot l E o U W} {τ d} :
    Pasting bridge h e t τ d →
      Pasting bridge h (insert l E o f e) (insert l E o f t) (before l E o f e t τ)
      (fun M lo hi tl th ↦ d (f.evaluate.obj M) lo hi tl th ∧
        boundaries l E o (insert l E o f e) (insert l E o f t) M lo hi tl th)
  | tensorRight {A W : Over B} {e t : Slot l E o A W} {τ d} (N : System l E W.left) :
    Pasting bridge h e t τ d → Pasting bridge h (.tensorRight N e) (.tensorRight N t)
      (fun M ↦ (calculus l E W.left).systemClosed.tensor.map (Prod.mkHom (𝟙 N) (τ M)))
      (fun M lo hi tl th ↦ d M lo hi tl th ∧
        boundaries l E o (.tensorRight N e) (.tensorRight N t) M lo hi tl th)

/-- The exact conditional system shift theorem, including both projection slots,
noncartesian proper/open squares and all finite composition/refinement pastings.
No faithfulness of evaluation is assumed or used.
Source: blueprint fix-prop-coherence.proof.md, maps-used sentence, adic transport Step 2;
agent-formulated obligation, proof steps 1--6
(blueprint: lem-pur-system-proper-open-projection-shift).

Proof:
1. Composition, whiskering and inversion preserve the fixed shift square. For a
composite insert the middle comparison and apply the two squares; for an inverse
multiply the square by its inverses. Whiskering uses naturality and the recursive
comparison chi_HF = chi_H H(chi_F).
2. The actual alpha is beta, then the clopen component projection, then the open
and pullback compositors. The assumed primitive squares paste to its square.
Whisker this with the proper adjunction unit and counit to obtain Gamma's square.
The component projection is never inverted.
3. The open-unit adjunct identity says (P_i Gamma) u^i = lambda inverse. Its factors
have their shift squares, so the inverse square gives the actual lambda square,
including its clopen factorization and noncartesian refinement squares.
4. The cartesian exchange is the mate built from eta, the pullback square theta,
and epsilon. Paste their assumed squares; invertibility of exchange is unnecessary.
5. Proper projection is eta followed by S_p of mu and epsilon tensor identity.
For the first slot use the counit square and first tensor naturality; for the
second use naturality in the fixed degree-zero counit and the signed second-slot
comparison (-1)^(ri). Paste with mu and eta. Both squares are natural in both inputs.
6. Compactification exchange is proper exchange on J followed by S of beta.
Compactification projection is proper projection followed by S of gamma, including
the pullback compositor. Paste these squares. Induct on the finite-pasting grammar
for compositions, refinements and their inverses and contexts. All equalities are
in the derived category of whole semilinear systems. The common finite bounds may
translate under shift; no preservation of an unspecified domain is asserted. -/
theorem properOpenProjectionShift (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (bridge : CanonicalBridge l E o) (h : ProperOpenCoherence l E o c a bridge)
    (_generators : ∀ {A W : Over (Spec (.of D.k))} (e t : Slot l E o A W) (τ)
      (_g : Generator l E o c a e t τ), ∀ (M : System l E A.left) (r : ℤ),
        (∃ lo hi tl th : ℤ, boundaries l E o e t M lo hi tl th) →
          Square l E o e t τ M r)
    {A W : Over (Spec (.of D.k))} (e t : Slot l E o A W) (τ)
    (d : System l E A.left → ℤ → ℤ → ℤ → ℤ → Prop)
    (_p : Pasting l E o c a bridge h e t τ d) (M : System l E A.left)
    (_adm : ∃ lo hi tl th : ℤ, d M lo hi tl th) (r : ℤ) :
    Square l E o e t τ M r := by
  sorry

end SystemShift
end WeilConjectures.IntegralSystemRealization
