/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Sheaf.Paper.SixFunctorDualNotation
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.Paper.ExchangeFunctoriality
public import Sheaf.Paper.ConstructibleProjectionMates
public import Sheaf.Paper.CompactExchangeOperationCoordinates
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactSupportCandidate
public import Sheaf.Paper.DirectImagesConstructible

/-! # The middle exchange/projection square under base change

Source: current blueprint, sec-six-functors/sk-thm-sf-kunneth-relative,
lem-sf-kunneth-coherence.proof.md, clause (iii)
(blueprint: lem-sf-middle-exchange-projection-base-change).

The helpers only spell out the cube, its canonical comparisons and the two composites.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor MonoidalCategory
namespace WeilConjectures.MiddleExchangeProjection

/-- The Cartesian cube in the middle square, with arbitrary representatives of its
fibre products. All objects retain their finite-type structure over the fixed field.
Source: current blueprint, coherence (iii)
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
structure Cube (D : FiniteFieldDatum.{u}) where
  X : SixFunctorSpace D
  Y : SixFunctorSpace D
  B : SixFunctorSpace D
  X' : SixFunctorSpace D
  Y' : SixFunctorSpace D
  B' : SixFunctorSpace D
  T : SixFunctorSpace D
  T' : SixFunctorSpace D
  f : X ⟶ B
  g : Y ⟶ B
  b : B' ⟶ B
  f' : X' ⟶ B'
  g' : Y' ⟶ B'
  p : T ⟶ X
  q : T ⟶ Y
  p' : T' ⟶ X'
  q' : T' ⟶ Y'
  bX : X' ⟶ X
  bY : Y' ⟶ Y
  bT : T' ⟶ T
  fg : IsPullback p.hom.left q.hom.left f.hom.left g.hom.left
  fb : IsPullback bX.hom.left f'.hom.left f.hom.left b.hom.left
  gb : IsPullback bY.hom.left g'.hom.left g.hom.left b.hom.left
  fg' : IsPullback p'.hom.left q'.hom.left f'.hom.left g'.hom.left
  qb : IsPullback bT.hom.left q'.hom.left q.hom.left bY.hom.left
  pb : IsPullback bT.hom.left p'.hom.left p.hom.left bX.hom.left
  [separatedX : IsSeparated X.obj.hom]
  [separatedY : IsSeparated Y.obj.hom]
  [separatedB : IsSeparated B.obj.hom]
  [separatedXPrime : IsSeparated X'.obj.hom]
  [separatedYPrime : IsSeparated Y'.obj.hom]
  [separatedBPrime : IsSeparated B'.obj.hom]
  [separatedT : IsSeparated T.obj.hom]
  [separatedTPrime : IsSeparated T'.obj.hom]
  [separatedf : IsSeparated f.hom.left]
  [finitef : LocallyOfFiniteType f.hom.left]
  [compactf : QuasiCompact f.hom.left]
  [separatedg : IsSeparated g.hom.left]
  [finiteg : LocallyOfFiniteType g.hom.left]
  [compactg : QuasiCompact g.hom.left]
  [separatedb : IsSeparated b.hom.left]
  [finiteb : LocallyOfFiniteType b.hom.left]
  [compactb : QuasiCompact b.hom.left]
  [separatedfPrime : IsSeparated f'.hom.left]
  [finitefPrime : LocallyOfFiniteType f'.hom.left]
  [compactfPrime : QuasiCompact f'.hom.left]
  [separatedgPrime : IsSeparated g'.hom.left]
  [finitegPrime : LocallyOfFiniteType g'.hom.left]
  [compactgPrime : QuasiCompact g'.hom.left]
  [separatedp : IsSeparated p.hom.left]
  [finitep : LocallyOfFiniteType p.hom.left]
  [compactp : QuasiCompact p.hom.left]
  [separatedq : IsSeparated q.hom.left]
  [finiteq : LocallyOfFiniteType q.hom.left]
  [compactq : QuasiCompact q.hom.left]
  [separatedpPrime : IsSeparated p'.hom.left]
  [finitepPrime : LocallyOfFiniteType p'.hom.left]
  [compactpPrime : QuasiCompact p'.hom.left]
  [separatedqPrime : IsSeparated q'.hom.left]
  [finiteqPrime : LocallyOfFiniteType q'.hom.left]
  [compactqPrime : QuasiCompact q'.hom.left]
  [separatedbX : IsSeparated bX.hom.left]
  [finitebX : LocallyOfFiniteType bX.hom.left]
  [compactbX : QuasiCompact bX.hom.left]
  [separatedbY : IsSeparated bY.hom.left]
  [finitebY : LocallyOfFiniteType bY.hom.left]
  [compactbY : QuasiCompact bY.hom.left]
  [separatedbT : IsSeparated bT.hom.left]
  [finitebT : LocallyOfFiniteType bT.hom.left]
  [compactbT : QuasiCompact bT.hom.left]

/-- Repackage a base-changed compactification without choosing new factors.
Source: def-exchange-projection, chosen compactification and its base change
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
def compactifiedSquare {D : FiniteFieldDatum.{u}}
    {X Y X' Y' : SixFunctorSpace D} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (sq : IsPullback g'.hom.left f'.hom.left f.hom.left g.hom.left)
    (c : Compactification f.hom.left) : SixFunctorCompactifiedSquare D := by
  letI := Y.property.1
  letI := Y.property.2
  letI := Y'.property.1
  letI := Y'.property.2
  let c' := c.ofIsPullback sq
  let Z : SixFunctorSpace D := ⟨Over.mk (c.g ≫ Y.obj.hom),
    inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y.obj.hom)),
    inferInstanceAs (QuasiCompact (c.g ≫ Y.obj.hom))⟩
  let Z' : SixFunctorSpace D := ⟨Over.mk (c'.g ≫ Y'.obj.hom),
    inferInstanceAs (LocallyOfFiniteType (c'.g ≫ Y'.obj.hom)),
    inferInstanceAs (QuasiCompact (c'.g ≫ Y'.obj.hom))⟩
  let i : X ⟶ Z := ObjectProperty.homMk (Over.homMk c.i (by
    change c.i ≫ c.g ≫ Y.obj.hom = X.obj.hom
    rw [← Category.assoc, ← c.comm]
    exact f.hom.w))
  let i' : X' ⟶ Z' := ObjectProperty.homMk (Over.homMk c'.i (by
    change c'.i ≫ c'.g ≫ Y'.obj.hom = X'.obj.hom
    rw [← Category.assoc, ← c'.comm]
    exact f'.hom.w))
  let p : Z ⟶ Y := ObjectProperty.homMk (Over.homMk c.g rfl)
  let p' : Z' ⟶ Y' := ObjectProperty.homMk (Over.homMk c'.g rfl)
  let h : Z' ⟶ Z := ObjectProperty.homMk (Over.homMk (pullback.fst c.g g.hom.left) (by
    change pullback.fst c.g g.hom.left ≫ c.g ≫ Y.obj.hom =
      pullback.snd c.g g.hom.left ≫ Y'.obj.hom
    rw [← Category.assoc, pullback.condition, Category.assoc, g.hom.w]))
  exact
    { X := X, Y := Y, X' := X', Y' := Y', Z := Z, Z' := Z'
      f := f, f' := f', g := g, g' := g', i := i, i' := i', p := p, p' := p', h := h
      open_i := c.isOpenImmersion, open_i' := c'.isOpenImmersion
      proper_p := c.isProper, proper_p' := c'.isProper
      factorization := by ext; exact c.comm
      factorization' := by ext; exact c'.comm
      square := sq
      properSquare := (c.isPullback_g_ofIsPullback sq).flip
      openSquare := c.isPullback_i_ofIsPullback sq
      squareComm := by ext; exact sq.w
      properComm := by ext; exact pullback.condition
      openComm := by ext; exact (c.ofIsPullback_i_fst sq).symm }

/-- The specified compact-support exchange in operation coordinates, followed by
its canonical compactification comparison to the requested target compactification.
Source: def-exchange-projection and fix-lem-exchanges (1),(4)
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
def exchange {D : FiniteFieldDatum.{u}}
    {A : SixFunctorSpace D → Type v} [∀ X, Category.{w} (A X)]
    (S : SixFunctorPushStage D A) (T : ∀ X, A X ⥤ A X ⥤ A X)
    (ex : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    {X Y X' Y' : SixFunctorSpace D} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (sq : IsPullback g'.hom.left f'.hom.left f.hom.left g.hom.left)
    (c : Compactification f.hom.left) (d : Compactification f'.hom.left) (K : A X) :
    (S.pull g).obj ((S.support f c).obj K) ⟶
      (S.support f' d).obj ((S.pull g').obj K) := by
  let Q := compactifiedSquare sq c
  exact (sixFunctorCompactExchange (ex Q)).app K ≫
    (S.comparison f' Q.compactification' d).hom.app ((S.pull g').obj K)

/-- Pullback composition across a commutative scheme square, in the supplied coordinates.
Source: the pullback-composition comparison in delta and chi
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
def squarePull {D : FiniteFieldDatum.{u}}
    {A : SixFunctorSpace D → Type v} [∀ X, Category.{w} (A X)]
    (S : SixFunctorPushStage D A)
    {X Y X' Y' : SixFunctorSpace D} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (sq : IsPullback g'.hom.left f'.hom.left f.hom.left g.hom.left) :
    S.pull f ⋙ S.pull g' ≅ S.pull g ⋙ S.pull f' :=
  (S.pullComposition g' f).symm ≪≫
    eqToIso (congrArg (fun e ↦ S.pull e) (by ext; exact sq.w)) ≪≫
    S.pullComposition f' g

/-- The displayed beta: tensor exchange with the identity, then the projection map.
Source: the two beta formulas in the middle-square statement
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
def beta {D : FiniteFieldDatum.{u}}
    {A : SixFunctorSpace D → Type v} [∀ X, Category.{w} (A X)]
    (S : SixFunctorPushStage D A) (T : ∀ X, A X ⥤ A X ⥤ A X)
    (ex : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    {X Y B V : SixFunctorSpace D} {f : X ⟶ B} {g : Y ⟶ B}
    {p : V ⟶ X} {q : V ⟶ Y}
    (sq : IsPullback p.hom.left q.hom.left f.hom.left g.hom.left)
    (cf : Compactification f.hom.left) (cq : Compactification q.hom.left)
    (K : A X) (L : A Y) :=
  ((T Y).map (exchange S T ex sq cf cq K)).app L ≫
    compactSupportProjectionComponent ex q cq ((S.pull p).obj K) L

/-- The canonical chi is monoidality of bT followed by the p and q square comparisons.
Source: the chi formula and step 1 of the node's proof
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
def chi {D : FiniteFieldDatum.{u}}
    {A : SixFunctorSpace D → Type v} [∀ X, Category.{w} (A X)]
    (S : SixFunctorPushStage D A) (T : ∀ X, A X ⥤ A X ⥤ A X)
    (mu : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) (M N : A Y),
      (S.pull f).obj (((T Y).obj M).obj N) ≅
        ((T X).obj ((S.pull f).obj M)).obj ((S.pull f).obj N))
    (G : Cube D) (K : A G.X) (L : A G.Y) :=
  (mu G.bT ((S.pull G.p).obj K) ((S.pull G.q).obj L)) ≪≫
    ((T G.T').mapIso ((squarePull S G.pb).app K)).app
      ((S.pull G.bT).obj ((S.pull G.q).obj L)) ≪≫
    ((T G.T').obj ((S.pull G.p').obj ((S.pull G.bX).obj K))).mapIso
      ((squarePull S G.qb).app L)

/-- The canonical delta is monoidality, gb=bg' pullback composition, then tensor
of the f,b exchange with identity. Source: delta in the middle-square statement
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
def delta {D : FiniteFieldDatum.{u}}
    {A : SixFunctorSpace D → Type v} [∀ X, Category.{w} (A X)]
    (S : SixFunctorPushStage D A) (T : ∀ X, A X ⥤ A X ⥤ A X)
    (ex : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (mu : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) (M N : A Y),
      (S.pull f).obj (((T Y).obj M).obj N) ≅
        ((T X).obj ((S.pull f).obj M)).obj ((S.pull f).obj N))
    (G : Cube D) (cf : Compactification G.f.hom.left)
    (cf' : Compactification G.f'.hom.left) (K : A G.X) (L : A G.Y) :=
  (mu G.bY ((S.pull G.g).obj ((S.support G.f cf).obj K)) L).hom ≫
    ((T G.Y').map ((squarePull S G.gb).hom.app ((S.support G.f cf).obj K))).app
      ((S.pull G.bY).obj L) ≫
    ((T G.Y').map ((S.pull G.g').map (exchange S T ex G.fb cf cf' K))).app
      ((S.pull G.bY).obj L)

/-- The requested equality, before any image along g or outer projection formula.
Source: displayed middle square and all four proof steps of the node
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
def equation {D : FiniteFieldDatum.{u}}
    {A : SixFunctorSpace D → Type v} [∀ X, Category.{w} (A X)]
    (S : SixFunctorPushStage D A) (T : ∀ X, A X ⥤ A X ⥤ A X)
    (ex : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (mu : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) (M N : A Y),
      (S.pull f).obj (((T Y).obj M).obj N) ≅
        ((T X).obj ((S.pull f).obj M)).obj ((S.pull f).obj N))
    (G : Cube D) (cf : Compactification G.f.hom.left)
    (cf' : Compactification G.f'.hom.left) (cq : Compactification G.q.hom.left)
    (cq' : Compactification G.q'.hom.left) (K : A G.X) (L : A G.Y) : Prop :=
  (S.pull G.bY).map (beta S T ex G.fg cf cq K L) ≫
      exchange S T ex G.qb cq cq'
        (((T G.T).obj ((S.pull G.p).obj K)).obj ((S.pull G.q).obj L)) ≫
      (S.support G.q' cq').map (chi S T mu G K L).hom =
    delta S T ex mu G cf cf' K L ≫
      beta S T ex G.fg' cf' cq' ((S.pull G.bX).obj K) ((S.pull G.bY).obj L)

/-- The coefficient prime is a unit on a bundled geometric scheme, transported from k.
Source: the standing distinct-prime convention
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
instance residueUnits (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (X : SixFunctorSpace D) : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) :=
  fun x ↦ (by
    simpa only [map_natCast] using (finiteFieldDatumPrimeUnit D C.l C.different).map
      (X.obj.hom.residueFieldAlgebraMap x) : IsUnit (C.l : X.obj.left.residueField x)).invertible

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- The canonical integral monoidal pullback comparison in the datum's coordinates.
Only recorded equalities of its functors are transported; the comparison is not supplied anew.
Source: lem-pur-derived-pullback-tensor-iso, integral coefficients
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
def integralMu (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (M N : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    (S.higher.integral.pull f).obj (((S.higher.integralTensor Y).obj M).obj N) ≅
      ((S.higher.integralTensor X).obj ((S.higher.integral.pull f).obj M)).obj
        ((S.higher.integral.pull f).obj N) := by
  rw [S.higher.integralPullback f, S.higher.integralTensorNormalization X,
    S.higher.integralTensorNormalization Y]
  exact canonicalIntegralPullbackTensor C.l E f.hom.left M N

/-- The canonical rational monoidal pullback comparison in the datum's coordinates.
Only recorded equalities of its functors are transported; the comparison is not supplied anew.
Source: lem-pur-derived-pullback-tensor-iso, rational coefficients
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
def rationalMu (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (M N : sfRationalConstructibleCategory C.l E Y.obj.left) :
    (S.higher.rational.pull f).obj (((S.higher.rationalTensor Y).obj M).obj N) ≅
      ((S.higher.rationalTensor X).obj ((S.higher.rational.pull f).obj M)).obj
        ((S.higher.rational.pull f).obj N) := by
  rw [S.higher.rationalPullback f, S.higher.rationalTensorNormalization X,
    S.higher.rationalTensorNormalization Y]
  exact canonicalRationalPullbackTensor C.l E f.hom.left M N

/-- The canonical common monoidal pullback comparison in the datum's coordinates.
Only recorded equalities of its functors are transported; the comparison is not supplied anew.
Source: lem-pur-derived-pullback-tensor-iso, common coefficients
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
def commonMu (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (M N : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Y.obj.left) :
    (S.closure.commonStage.pull f).obj (((S.closure.commonStageTensor Y).obj M).obj N) ≅
      ((S.closure.commonStageTensor X).obj ((S.closure.commonStage.pull f).obj M)).obj
        ((S.closure.commonStage.pull f).obj N) := by
  rw [S.closure.commonStagePullback f, S.closure.commonStageTensorNormalization X,
    S.closure.commonStageTensorNormalization Y]
  exact canonicalCommonStagePullbackTensor C.l C.Qbar f.hom.left M N

/-- Quantify the displayed equality over its finite-Tor inputs at a supplied stage.
The operation and comparison arguments are instantiated by the recorded actual stages below.
Source: the bounded constructible finite-Tor domains of the middle square
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
def higherLaw
    {A : SixFunctorSpace D → Type v} [∀ X, Category.{w} (A X)]
    (S : SixFunctorPushStage D A) (T : ∀ X, A X ⥤ A X ⥤ A X)
    (ex : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (mu : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) (M N : A Y),
      (S.pull f).obj (((T Y).obj M).obj N) ≅
        ((T X).obj ((S.pull f).obj M)).obj ((S.pull f).obj N))
    (P : ∀ X, ObjectProperty (A X)) : Prop :=
  ∀ (G : Cube D) (cf : Compactification G.f.hom.left)
    (cf' : Compactification G.f'.hom.left) (cq : Compactification G.q.hom.left)
    (cq' : Compactification G.q'.hom.left) (K : A G.X) (L : A G.Y),
    P G.X K → P G.Y L → equation S T ex mu G cf cf' cq cq' K L

namespace Fixed

variable (R : Type (u + 1)) [CommRing R] [Finite R]

/-- The existing fixed-module derived category, retaining the small pro-etale site sizes.
Source: finite coefficient convention
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
abbrev category (X : Scheme.{u}) :=
  DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R))

/-- The given bounded-below etale-origin presentation of an input in fixed coordinates.
Source: fix-lem-exchanges, witnessed finite domain
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
abbrev origin (X : Scheme.{u}) (K : category R X) :=
  ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} R) X K

/-- Canonical exchange followed by the canonical comparison of compactifications,
evaluated at the retained origin of the pulled input. No exchange is inverted.
Source: def-exchange-projection and fix-lem-exchanges(4)
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
def exchange {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [QuasiCompact f']
    (sq : IsPullback g' f' f g) (c : Compactification f) (d : Compactification f')
    (K : category R X)
    (W : origin R X' ((ProEtale.upperStar (ModuleCat.{u + 1} R) g').leftDerivedFunctor.obj K)) :=
  (ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (ModuleCat.{u + 1} R) sq c).app K ≫
    (ProEtale.rightDerivedLowerShriekOfCompactificationEtaleOriginIso R
      (c.ofIsPullback sq) d).hom.app ⟨_, W⟩

/-- Fixed-coefficient beta, using the actual counit-defined compactification projection.
Source: beta in the middle-square statement
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
def beta {X Y B T : Scheme.{u}} {f : X ⟶ B} {g : Y ⟶ B}
    {p : T ⟶ X} {q : T ⟶ Y} [QuasiCompact q]
    (sq : IsPullback p q f g) (cf : Compactification f) (cq : Compactification q)
    (K : category R X) (L : category R Y)
    (W : origin R T ((ProEtale.upperStar (ModuleCat.{u + 1} R) p).leftDerivedFunctor.obj K)) :=
  ((ProEtale.derivedTensor (ModuleCat.{u + 1} R) Y).map
    (exchange R sq cf cq K W)).app L ≫
    ((ProEtale.projectionMapOfCompactification (ModuleCat.{u + 1} R) cq).app
      ((ProEtale.upperStar (ModuleCat.{u + 1} R) p).leftDerivedFunctor.obj K)).app L

/-- The fixed-coefficient external tensor D in the displayed cube.
Source: the definition of D and D' in the middle-square statement
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
def external {X Y T : Scheme.{u}} (p : T ⟶ X) (q : T ⟶ Y)
    (K : category R X) (L : category R Y) :=
  ((ProEtale.derivedTensor (ModuleCat.{u + 1} R) T).obj
    ((ProEtale.upperStar (ModuleCat.{u + 1} R) p).leftDerivedFunctor.obj K)).obj
      ((ProEtale.upperStar (ModuleCat.{u + 1} R) q).leftDerivedFunctor.obj L)

/-- Canonical finite chi: distribute bT pullback and use the p and q square comparisons.
Source: chi in the middle-square statement
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
def chi {D : FiniteFieldDatum.{u}} (G : Cube D)
    (K : category R G.X.obj.left) (L : category R G.Y.obj.left) :=
  ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} R) G.bT.hom.left
      ((ProEtale.upperStar (ModuleCat.{u + 1} R) G.p.hom.left).leftDerivedFunctor.obj K)
      ((ProEtale.upperStar (ModuleCat.{u + 1} R) G.q.hom.left).leftDerivedFunctor.obj L) ≪≫
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} R) G.T'.obj.left).mapIso
      ((ProEtale.leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} R)
        G.pb.flip.toCommSq).app K)).app
      ((ProEtale.upperStar (ModuleCat.{u + 1} R) G.bT.hom.left).leftDerivedFunctor.obj
        ((ProEtale.upperStar (ModuleCat.{u + 1} R) G.q.hom.left).leftDerivedFunctor.obj L)) ≪≫
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} R) G.T'.obj.left).obj
      ((ProEtale.upperStar (ModuleCat.{u + 1} R) G.p'.hom.left).leftDerivedFunctor.obj
        ((ProEtale.upperStar (ModuleCat.{u + 1} R) G.bX.hom.left).leftDerivedFunctor.obj K))).mapIso
      ((ProEtale.leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} R)
        G.qb.flip.toCommSq).app L)

/-- Canonical finite delta, retaining the f,b exchange and its origin presentation.
Source: delta in the middle-square statement
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
def delta {D : FiniteFieldDatum.{u}} (G : Cube D) [QuasiCompact G.f'.hom.left]
    (cf : Compactification G.f.hom.left) (cf' : Compactification G.f'.hom.left)
    (K : category R G.X.obj.left) (L : category R G.Y.obj.left)
    (W : origin R G.X'.obj.left
      ((ProEtale.upperStar (ModuleCat.{u + 1} R) G.bX.hom.left).leftDerivedFunctor.obj K)) :=
  (ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} R) G.bY.hom.left
    ((ProEtale.upperStar (ModuleCat.{u + 1} R) G.g.hom.left).leftDerivedFunctor.obj
      ((ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cf).obj K))
    L).hom ≫
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} R) G.Y'.obj.left).map
      ((ProEtale.leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} R)
        G.gb.flip.toCommSq).hom.app
          ((ProEtale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} R) cf).obj K))).app
        ((ProEtale.upperStar (ModuleCat.{u + 1} R) G.bY.hom.left).leftDerivedFunctor.obj L) ≫
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} R) G.Y'.obj.left).map
      ((ProEtale.upperStar (ModuleCat.{u + 1} R) G.g'.hom.left).leftDerivedFunctor.map
        (exchange R G.fb cf cf' K W))).app
      ((ProEtale.upperStar (ModuleCat.{u + 1} R) G.bY.hom.left).leftDerivedFunctor.obj L)

/-- The finite equation with every comparison evaluated at the supplied origin class.
Source: the displayed middle square, finite stage
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
def equation {D : FiniteFieldDatum.{u}} (G : Cube D)
    [QuasiCompact G.f'.hom.left] [QuasiCompact G.q.hom.left]
    [QuasiCompact G.q'.hom.left]
    (cf : Compactification G.f.hom.left) (cf' : Compactification G.f'.hom.left)
    (cq : Compactification G.q.hom.left) (cq' : Compactification G.q'.hom.left)
    (K : category R G.X.obj.left) (L : category R G.Y.obj.left)
    (WP : origin R G.T.obj.left
      ((ProEtale.upperStar (ModuleCat.{u + 1} R) G.p.hom.left).leftDerivedFunctor.obj K))
    (WK' : origin R G.X'.obj.left
      ((ProEtale.upperStar (ModuleCat.{u + 1} R) G.bX.hom.left).leftDerivedFunctor.obj K))
    (WP' : origin R G.T'.obj.left
      ((ProEtale.upperStar (ModuleCat.{u + 1} R) G.p'.hom.left).leftDerivedFunctor.obj
        ((ProEtale.upperStar (ModuleCat.{u + 1} R) G.bX.hom.left).leftDerivedFunctor.obj K)))
    (WD' : origin R G.T'.obj.left
      ((ProEtale.upperStar (ModuleCat.{u + 1} R) G.bT.hom.left).leftDerivedFunctor.obj
        (external R G.p.hom.left G.q.hom.left K L))) : Prop :=
  (ProEtale.upperStar (ModuleCat.{u + 1} R) G.bY.hom.left).leftDerivedFunctor.map
      (beta R G.fg cf cq K L WP) ≫
    exchange R G.qb cq cq' (external R G.p.hom.left G.q.hom.left K L) WD' ≫
    (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cq').map
      (chi R G K L).hom =
    delta R G cf cf' K L WK' ≫
      beta R G.fg' cf' cq'
        ((ProEtale.upperStar (ModuleCat.{u + 1} R) G.bX.hom.left).leftDerivedFunctor.obj K)
        ((ProEtale.upperStar (ModuleCat.{u + 1} R) G.bY.hom.left).leftDerivedFunctor.obj L) WP'

/-- The finite-coefficient inverse image in compact fixed-module coordinates.
Source: the finite-stage pullbacks in the middle square
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
def pull {X Y : Scheme.{u}} (f : X ⟶ Y) : category R Y ⥤ category R X :=
  (ProEtale.upperStar (ModuleCat.{u + 1} R) f).leftDerivedFunctor

/-- The finite equation on all retained bounded-below presentations of finite-Tor inputs.
P is specialized below to the existing finite-Tor constructible predicate, through the
canonical coefficient realization. Every additional origin is a proof on the prescribed
object, so none introduces a different complex or comparison map.
Source: the witnessed finite-domain paragraph
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
def law (D : FiniteFieldDatum.{u})
    (P : ∀ X : Scheme.{u}, category R X → Prop) : Prop :=
  ∀ (G : Cube D) [QuasiCompact G.f'.hom.left] [QuasiCompact G.q.hom.left]
    [QuasiCompact G.q'.hom.left]
    (cf : Compactification G.f.hom.left) (cf' : Compactification G.f'.hom.left)
    (cq : Compactification G.q.hom.left) (cq' : Compactification G.q'.hom.left)
    (K : DerivedCategory.Plus (Sheaf (ProEt.topology G.X.obj.left) (ModuleCat.{u + 1} R)))
    (L : DerivedCategory.Plus (Sheaf (ProEt.topology G.Y.obj.left) (ModuleCat.{u + 1} R)))
    (_WK : FixedEtaleOriginWitness G.X.obj.left R K)
    (_WL : FixedEtaleOriginWitness G.Y.obj.left R L),
    P G.X.obj.left K.obj → P G.Y.obj.left L.obj →
    ∀ (WP : origin R G.T.obj.left ((pull R G.p.hom.left).obj K.obj))
    (WK' : origin R G.X'.obj.left ((pull R G.bX.hom.left).obj K.obj))
    (WP' : origin R G.T'.obj.left
      ((pull R G.p'.hom.left).obj ((pull R G.bX.hom.left).obj K.obj)))
    (WD' : origin R G.T'.obj.left
      ((pull R G.bT.hom.left).obj (external R G.p.hom.left G.q.hom.left K.obj L.obj))),
    equation R G cf cf' cq cq' K.obj L.obj WP WK' WP' WD'

end Fixed

/-- Specialization to the actual quotient ring and intrinsic finite-Tor predicate.
The fixed-module category is merely its canonical coefficient realization.
Source: the positive finite quotient coefficient convention
(blueprint: lem-sf-middle-exchange-projection-base-change). -/
def finiteLaw (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n) : Prop :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  Fixed.law (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) D
    (fun X K ↦ finiteTorConstructible C.l E n hn X
      ((sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing C.l E n)).functor.obj K))

/-- Base change of the middle exchange/projection composite at all four coefficient stages.
The finite clause is in the canonical fixed-module realization; the other clauses use the
recorded completed, rationalized and common-finite-stage operations of the given datum.
Source: current blueprint, lem-sf-kunneth-coherence.proof.md, clause (iii)
(blueprint: lem-sf-middle-exchange-projection-base-change).

Proof (postponed, following the four steps of the node):
1. Put P=Lp*K, v=LbY*, w=LbT*. Expand beta, chi and delta as in the definitions above.
The canonical tensor comparison identifies wD with wP tensor Lq'*L', and the p-square
comparison c:wP to P' completes chi. Delta is mu followed by r tensor identity and
Lg'*(Ex(f,b)) tensor identity. Every object is in the supplied finite-Tor domain.
2. Apply horizontal exchange pasting from fix-lem-exchanges to f along g then bY,
and to f along b then g'. Both outer squares have the same bottom gbY=bg'.
Naturality under square comparisons gives A v(Ex(f,g))=Ex(f',g') Lg'*(Ex(f,b)) r,
where A=Rq'!(c) Ex(q,bY) on P. Insert the recorded compactification comparisons;
their cocycle and exchange naturality give the same equation for all choices above.
3. Apply the base-change square of prop-sf-pf-coherence to q along bY on (P,L).
Then use its naturality in the first input at c. The target comparison is chi, so
Rq'!(chi) Ex(q,bY) v(PF(q,P,L))=PF(q',P',L') (A tensor identity) mu.
4. Precompose with v(Ex(f,g) tensor identity). Naturality of the tensor-pullback
comparison moves this map through mu. Substitute step 2 and tensor functoriality:
the resulting right composite is beta' delta. This proves the displayed equation.
At finite coefficients retain all origin witnesses through the canonical comparisons.
At integral coefficients the cited equations hold on strict reduction diagrams before
the completed realization; no detection of integral morphisms by reductions is used.
Rationalization and passage to a common finite coefficient field preserve the equations.
-/
theorem middle_exchange_projection_base_change
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorDatum D C E n hn) :
    finiteLaw D C E n hn ∧
    higherLaw S.higher.integral S.higher.integralTensor S.higher.integralExchange
      (integralMu S) (S.toSixFunctorOperationDatum.integralFiniteTorDomain) ∧
    higherLaw S.higher.rational S.higher.rationalTensor S.higher.rationalExchange
      (rationalMu S) (fun _ ↦ ⊤) ∧
    higherLaw S.closure.commonStage S.closure.commonStageTensor S.closure.commonStageExchange
      (commonMu S) (fun _ ↦ ⊤) := by
  sorry

end WeilConjectures.MiddleExchangeProjection
