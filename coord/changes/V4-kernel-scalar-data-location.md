# KernelSplittingData and kernel scalar normalization interfaces

## Reason

The two strictly smaller geometric lemmas must refer to the existing kernel data.
Keeping those data in the theorem module would create an import cycle. Move the
existing declarations verbatim (apart from blueprint ownership docstrings) into
Sheaf.Paper.TowerP1KernelScalarData and publicly re-export them from the original
module. This is for independent proof dependencies, not a compile-time split.
All declaration names, universe parameters, signatures, structure fields and
construction bodies remain identical. No mathematical definition changes.

## Old

In lean/Sheaf/Paper/TowerP1KernelScalarNormalization.lean:

```lean
/-- Shift the specified roots-and-coefficients pullback isomorphism.
Source: base change of trace, twist identification
(blueprint: lem-sp-tower-p1-kernel-scalar-normalization). -/
def kernelShiftedLine {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}}
    {f : X ⟶ Y} {g : SpTowerShriek.Geometry l E b f}
    {cY : Chern l E Y} {cX : Chern l E X} (t : LinePullback l E f g cY cX) :
    (SpTowerShriek.pull l E b g).obj ((line l E cY)⟦(2 : ℤ)⟧) ≅
      (line l E cX)⟦(2 : ℤ)⟧ :=
  ((SpTowerShriek.pull l E b g).commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso (t.derivedIso l E)

/-- Unit/Chern splitting at q and at each product projection. Every comparison is
normalized on ordinary sections by CoefficientPullback or LinePullback. The maps
of the splittings are fixed by their two components; they are not arbitrary isomorphisms.
The relative hyperplane for projection a is the pullback along the other projection.
Source: base change of trace, unit and hyperplane components
(blueprint: lem-sp-tower-p1-kernel-scalar-normalization). -/
structure KernelSplittingData (p : Presentation l E S hS) where
  coefficientQ : CoefficientPullback l E p.classes.base (ProjectiveLine S ↘ S)
    (p.operations.geometry (ProjectiveLine S ↘ S))
  lineQ : LinePullback l E (ProjectiveLine S ↘ S)
    (p.operations.geometry (ProjectiveLine S ↘ S)) p.classes.chernS p.classes.chernP
  coefficientProjection : ∀ a : Bool,
    CoefficientPullback l E p.classes.base (Etale.projectiveLineDiagonalProjection S a)
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))
  lineProjection : ∀ a : Bool,
    LinePullback l E (Etale.projectiveLineDiagonalProjection S a)
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))
      p.classes.chernP p.classes.chernW
  splittingQ : (line l E p.classes.chernS)⟦(2 : ℤ)⟧ ⊞ unit S (Arings l E S) ≅
    (p.F l E).obj ((line l E p.classes.chernP)⟦(2 : ℤ)⟧)
  splittingQ_hom : splittingQ.hom = biprod.desc
    ((SpTowerShriek.adjunction l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).homEquiv _ _
        (kernelShiftedLine l E lineQ).hom)
    ((SpTowerShriek.adjunction l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).homEquiv _ _
        ((coefficientQ.derivedIso l E).hom ≫
          firstChern l E p.classes.chernP (hyperplanePic S)))
  traceQ : splittingQ.inv ≫ biprod.snd = p.trace l E
  splittingProjection : ∀ a : Bool,
    (line l E p.classes.chernP)⟦(2 : ℤ)⟧ ⊞
      unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) ≅
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).obj
      ((line l E p.classes.chernW)⟦(2 : ℤ)⟧)
  splittingProjection_hom : ∀ a : Bool, (splittingProjection a).hom = biprod.desc
    ((SpTowerShriek.adjunction l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).homEquiv _ _
        (kernelShiftedLine l E (lineProjection a)).hom)
    ((SpTowerShriek.adjunction l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).homEquiv _ _
        (((coefficientProjection a).derivedIso l E).hom ≫
          firstChern l E p.classes.chernW
            (Scheme.Pic.map (Etale.projectiveLineDiagonalProjection S (!a))
              (hyperplanePic S))))

variable {p : Presentation l E S hS}

/-- The trace for either projection is its splitting inverse followed by pr2.
Source: base change of trace (blueprint: lem-sp-tower-p1-kernel-scalar-normalization). -/
def KernelSplittingData.trace (k : KernelSplittingData l E p) (a : Bool) :
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).obj
      ((line l E p.classes.chernW)⟦(2 : ℤ)⟧) ⟶
    unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) :=
  (k.splittingProjection a).inv ≫ biprod.snd

/-- The proper exchange mate followed by the canonical shifted Tate-line comparison.
The argument !a chooses the horizontal projection, leaving a as the direct-image edge.
Source: base change of trace (blueprint: lem-sp-tower-p1-kernel-scalar-normalization). -/
def KernelSplittingData.exchange (k : KernelSplittingData l E p) (a : Bool) :
    (SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).obj
      ((p.F l E).obj ((line l E p.classes.chernP)⟦(2 : ℤ)⟧)) ⟶
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).obj
      ((line l E p.classes.chernW)⟦(2 : ℤ)⟧) :=
  match a with
  | false => p.exchangeSwap l E ((line l E p.classes.chernP)⟦(2 : ℤ)⟧) ≫
      (SpTowerShriek.push l E p.classes.base
        (p.operations.geometry (Etale.projectiveLineDiagonalProjection S false))).map
        (kernelShiftedLine l E (k.lineProjection true)).hom
  | true => p.exchange l E ((line l E p.classes.chernP)⟦(2 : ℤ)⟧) ≫
      (SpTowerShriek.push l E p.classes.base
        (p.operations.geometry (Etale.projectiveLineDiagonalProjection S true))).map
        (kernelShiftedLine l E (k.lineProjection false)).hom

/-- Canonical comparison of the two splitting sources, component by component.
Source: base change of trace, d_i
(blueprint: lem-sp-tower-p1-kernel-scalar-normalization). -/
def KernelSplittingData.sumComparison (k : KernelSplittingData l E p) :
    (SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).obj
      ((line l E p.classes.chernS)⟦(2 : ℤ)⟧ ⊞ unit S (Arings l E S)) ⟶
    (line l E p.classes.chernP)⟦(2 : ℤ)⟧ ⊞
      unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) :=
  biprod.lift
    ((SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).map
        (biprod.fst (X := (line l E p.classes.chernS)⟦(2 : ℤ)⟧)
          (Y := unit S (Arings l E S))) ≫ (kernelShiftedLine l E k.lineQ).hom)
    ((SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).map
        (biprod.snd (X := (line l E p.classes.chernS)⟦(2 : ℤ)⟧)
          (Y := unit S (Arings l E S))) ≫ (k.coefficientQ.derivedIso l E).hom)

/-- Exactly alpha_i, Rp_i(delta), and the splitting trace, in composition order.
Source: Levelwise check, displayed c_i
(blueprint: lem-sp-tower-p1-kernel-scalar-normalization). -/
def KernelSplittingData.scalar (k : KernelSplittingData l E p) (a : Bool) :
    unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) ⟶
      unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) :=
  p.sourceUnitAt l E a (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))) ≫
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).map
      (p.delta l E) ≫ k.trace l E a

/-- The ordinary etale trace for p_a, transported from the standard P1 over P.
Source: finite diagonal integrals, comparison of the product projections
(blueprint: lem-sp-tower-p1-kernel-scalar-normalization). -/
def kernelFiniteTrace (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (c : ProjectiveCoordinates l E n p)
    (bP : Etale.ArbitraryBaseFiniteP1Splitting (levelRing l E n) (l ^ (n + 1))
      (levelAnnihilates l E n) c.transport (ProjectiveLine S) (lineExponentUnit l n hS))
    (a : Bool) :
    (EtaleWords.push (levelRing l E n) (Etale.projectiveLineDiagonalProjection S a)).obj
      (EtaleWords.line (levelRing l E n) (l ^ (n + 1)) (levelAnnihilates l E n)
        (diagonalSurface S)) ⟶
      Etale.ordinaryFiniteUnit (levelRing l E n) (ProjectiveLine S) :=
  Etale.ordinaryFiniteP1DiagonalChartMap (levelRing l E n) (l ^ (n + 1))
    (levelAnnihilates l E n) c.transport S (baseExponentUnit l n hS) a ≫ bP.trace

/-- The specified finite composite, including the canonical composition source alpha.
The supported boundary in EtaleWords.delta has the positive divisor-Chern sign.
Source: finite diagonal integrals, c_i at level n+1
(blueprint: lem-sp-tower-p1-kernel-scalar-normalization). -/
def kernelFiniteScalar (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (c : ProjectiveCoordinates l E n p)
    (bP : Etale.ArbitraryBaseFiniteP1Splitting (levelRing l E n) (l ^ (n + 1))
      (levelAnnihilates l E n) c.transport (ProjectiveLine S) (lineExponentUnit l n hS))
    (hD : (diagonalImmersion S).ker.IsInvertible) (a : Bool) :
    Etale.ordinaryFiniteUnit (levelRing l E n) (ProjectiveLine S) ⟶
      Etale.ordinaryFiniteUnit (levelRing l E n) (ProjectiveLine S) :=
  Etale.projectiveLineDiagonalAlpha (levelRing l E n) S a ≫
    (EtaleWords.push (levelRing l E n) (Etale.projectiveLineDiagonalProjection S a)).map
      (EtaleWords.delta (levelRing l E n) (l ^ (n + 1))
        (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime l)) _) (levelAnnihilates l E n)
        S hD (surfaceExponentUnit l n hS)) ≫ kernelFiniteTrace l E n c bP a

/-- Every part of the finite scalar comparison is an equation of the specified maps.
In particular alpha is the canonical composition source, not a free source isomorphism.
Source: Levelwise check, finite composite and sign
(blueprint: lem-sp-tower-p1-kernel-scalar-normalization). -/
structure KernelFiniteNormalization (k : KernelSplittingData l E p)
    (n : ℕ) [Finite (SpTowerShriek.R l E n)] (c : ProjectiveCoordinates l E n p)
    (bP : Etale.ArbitraryBaseFiniteP1Splitting (levelRing l E n) (l ^ (n + 1))
      (levelAnnihilates l E n) c.transport (ProjectiveLine S) (lineExponentUnit l n hS))
    (hD : (diagonalImmersion S).ker.IsInvertible) : Prop where
  alpha : ∀ a : Bool, WordComparison l E n (c.unitP l E n)
    (c.push l E n (Etale.projectiveLineDiagonalProjection S a)
      (c.push l E n (diagonalImmersion S) (c.unitP l E n)))
    (p.sourceUnitAt l E a (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))))
    (Etale.projectiveLineDiagonalAlpha (levelRing l E n) S a)
  pushed_delta : ∀ a : Bool, WordComparison l E n
    (c.push l E n (Etale.projectiveLineDiagonalProjection S a)
      (c.push l E n (diagonalImmersion S) (c.unitP l E n)))
    (c.push l E n (Etale.projectiveLineDiagonalProjection S a) (c.lineW l E n))
    ((SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).map (p.delta l E))
    ((EtaleWords.push (levelRing l E n) (Etale.projectiveLineDiagonalProjection S a)).map
      (EtaleWords.delta (levelRing l E n) (l ^ (n + 1))
        (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime l)) _) (levelAnnihilates l E n)
        S hD (surfaceExponentUnit l n hS)))
  trace : ∀ a : Bool, WordComparison l E n
    (c.push l E n (Etale.projectiveLineDiagonalProjection S a) (c.lineW l E n))
    (c.unitP l E n) (k.trace l E a) (kernelFiniteTrace l E n c bP a)
  composite : ∀ a : Bool, WordComparison l E n (c.unitP l E n) (c.unitP l E n)
    (k.scalar l E a) (kernelFiniteScalar l E n c bP hD a)
  finite_identity : ∀ a : Bool, kernelFiniteScalar l E n c bP hD a =
    𝟙 (Etale.ordinaryFiniteUnit (levelRing l E n) (ProjectiveLine S))

/-- Evaluation at every positive level uses normalized constant, root and site-mate
coordinates, and the ordinary finite unit/Chern splitting over P.
Source: Levelwise check (blueprint: lem-sp-tower-p1-kernel-scalar-normalization). -/
def KernelSplittingData.finiteNormalization (k : KernelSplittingData l E p)
    (hD : (diagonalImmersion S).ker.IsInvertible) (n : ℕ) : Prop :=
  letI : Finite (SpTowerShriek.R l E n) := p.classes.base.finite n
  ∃ (c : ProjectiveCoordinates l E n p)
    (bP : Etale.ArbitraryBaseFiniteP1Splitting (levelRing l E n) (l ^ (n + 1))
      (levelAnnihilates l E n) c.transport (ProjectiveLine S) (lineExponentUnit l n hS)),
    KernelFiniteNormalization l E k n c bP hD

/-- All the asserted equalities in the actual tower derived category, and their
finite etale descriptions. Degree-zero full faithfulness is used only on A_P[0].
Source: base change of trace and Levelwise check
(blueprint: lem-sp-tower-p1-kernel-scalar-normalization). -/
structure KernelScalarNormalization (p : Presentation l E S hS)
    (k : KernelSplittingData l E p) : Prop where
  exchange_iso : ∀ a : Bool, IsIso (k.exchange l E a)
  source_comparison_iso : IsIso (k.sumComparison l E)
  splitting_base_change : ∀ a : Bool,
    (SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).map k.splittingQ.hom ≫
        k.exchange l E a = k.sumComparison l E ≫ (k.splittingProjection a).hom
  inverse_base_change : ∀ a : Bool,
    k.exchange l E a ≫ (k.splittingProjection a).inv =
      (SpTowerShriek.pull l E p.classes.base
        (p.operations.geometry (ProjectiveLine S ↘ S))).map k.splittingQ.inv ≫
          k.sumComparison l E
  trace_base_change : ∀ a : Bool,
    k.exchange l E a ≫ k.trace l E a =
      (SpTowerShriek.pull l E p.classes.base
        (p.operations.geometry (ProjectiveLine S ↘ S))).map (p.trace l E) ≫
          (k.coefficientQ.derivedIso l E).hom
  alpha_iso : ∀ a : Bool, IsIso (p.sourceUnitAt l E a
    (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))))
  scalar_identity : ∀ a : Bool, k.scalar l E a =
    𝟙 (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
  cartier : (diagonalImmersion S).ker.IsInvertible
  levels : ∀ n : ℕ, k.finiteNormalization l E cartier n
  degree_zero_lift : ∀ a : Bool,
    ∃! f : coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)) ⟶
      coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)),
      (DerivedCategory.singleFunctor
        (Systems (ProjectiveLine S) (Arings l E (ProjectiveLine S))) 0).map f = k.scalar l E a
  degree_zero_detection : ∀ (f g :
    coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)) ⟶
      coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S))),
    (∀ n : ℕ, (SpTowerShriek.ev l E (ProjectiveLine S) n).map f =
      (SpTowerShriek.ev l E (ProjectiveLine S) n).map g) → f = g
```

## New

In lean/Sheaf/Paper/TowerP1KernelScalarData.lean:

```lean
/-- Shift the specified roots-and-coefficients pullback isomorphism.
Source: base change of trace, twist identification
(blueprint: def-sp-tower-p1-kernel-scalar-data). -/
def kernelShiftedLine {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}}
    {f : X ⟶ Y} {g : SpTowerShriek.Geometry l E b f}
    {cY : Chern l E Y} {cX : Chern l E X} (t : LinePullback l E f g cY cX) :
    (SpTowerShriek.pull l E b g).obj ((line l E cY)⟦(2 : ℤ)⟧) ≅
      (line l E cX)⟦(2 : ℤ)⟧ :=
  ((SpTowerShriek.pull l E b g).commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso (t.derivedIso l E)

/-- Unit/Chern splitting at q and at each product projection. Every comparison is
normalized on ordinary sections by CoefficientPullback or LinePullback. The maps
of the splittings are fixed by their two components; they are not arbitrary isomorphisms.
The relative hyperplane for projection a is the pullback along the other projection.
Source: base change of trace, unit and hyperplane components
(blueprint: def-sp-tower-p1-kernel-scalar-data). -/
structure KernelSplittingData (p : Presentation l E S hS) where
  coefficientQ : CoefficientPullback l E p.classes.base (ProjectiveLine S ↘ S)
    (p.operations.geometry (ProjectiveLine S ↘ S))
  lineQ : LinePullback l E (ProjectiveLine S ↘ S)
    (p.operations.geometry (ProjectiveLine S ↘ S)) p.classes.chernS p.classes.chernP
  coefficientProjection : ∀ a : Bool,
    CoefficientPullback l E p.classes.base (Etale.projectiveLineDiagonalProjection S a)
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))
  lineProjection : ∀ a : Bool,
    LinePullback l E (Etale.projectiveLineDiagonalProjection S a)
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))
      p.classes.chernP p.classes.chernW
  splittingQ : (line l E p.classes.chernS)⟦(2 : ℤ)⟧ ⊞ unit S (Arings l E S) ≅
    (p.F l E).obj ((line l E p.classes.chernP)⟦(2 : ℤ)⟧)
  splittingQ_hom : splittingQ.hom = biprod.desc
    ((SpTowerShriek.adjunction l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).homEquiv _ _
        (kernelShiftedLine l E lineQ).hom)
    ((SpTowerShriek.adjunction l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).homEquiv _ _
        ((coefficientQ.derivedIso l E).hom ≫
          firstChern l E p.classes.chernP (hyperplanePic S)))
  traceQ : splittingQ.inv ≫ biprod.snd = p.trace l E
  splittingProjection : ∀ a : Bool,
    (line l E p.classes.chernP)⟦(2 : ℤ)⟧ ⊞
      unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) ≅
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).obj
      ((line l E p.classes.chernW)⟦(2 : ℤ)⟧)
  splittingProjection_hom : ∀ a : Bool, (splittingProjection a).hom = biprod.desc
    ((SpTowerShriek.adjunction l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).homEquiv _ _
        (kernelShiftedLine l E (lineProjection a)).hom)
    ((SpTowerShriek.adjunction l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).homEquiv _ _
        (((coefficientProjection a).derivedIso l E).hom ≫
          firstChern l E p.classes.chernW
            (Scheme.Pic.map (Etale.projectiveLineDiagonalProjection S (!a))
              (hyperplanePic S))))

variable {p : Presentation l E S hS}

/-- The trace for either projection is its splitting inverse followed by pr2.
Source: base change of trace (blueprint: def-sp-tower-p1-kernel-scalar-data). -/
def KernelSplittingData.trace (k : KernelSplittingData l E p) (a : Bool) :
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).obj
      ((line l E p.classes.chernW)⟦(2 : ℤ)⟧) ⟶
    unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) :=
  (k.splittingProjection a).inv ≫ biprod.snd

/-- The proper exchange mate followed by the canonical shifted Tate-line comparison.
The argument !a chooses the horizontal projection, leaving a as the direct-image edge.
Source: base change of trace (blueprint: def-sp-tower-p1-kernel-scalar-data). -/
def KernelSplittingData.exchange (k : KernelSplittingData l E p) (a : Bool) :
    (SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).obj
      ((p.F l E).obj ((line l E p.classes.chernP)⟦(2 : ℤ)⟧)) ⟶
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).obj
      ((line l E p.classes.chernW)⟦(2 : ℤ)⟧) :=
  match a with
  | false => p.exchangeSwap l E ((line l E p.classes.chernP)⟦(2 : ℤ)⟧) ≫
      (SpTowerShriek.push l E p.classes.base
        (p.operations.geometry (Etale.projectiveLineDiagonalProjection S false))).map
        (kernelShiftedLine l E (k.lineProjection true)).hom
  | true => p.exchange l E ((line l E p.classes.chernP)⟦(2 : ℤ)⟧) ≫
      (SpTowerShriek.push l E p.classes.base
        (p.operations.geometry (Etale.projectiveLineDiagonalProjection S true))).map
        (kernelShiftedLine l E (k.lineProjection false)).hom

/-- Canonical comparison of the two splitting sources, component by component.
Source: base change of trace, d_i
(blueprint: def-sp-tower-p1-kernel-scalar-data). -/
def KernelSplittingData.sumComparison (k : KernelSplittingData l E p) :
    (SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).obj
      ((line l E p.classes.chernS)⟦(2 : ℤ)⟧ ⊞ unit S (Arings l E S)) ⟶
    (line l E p.classes.chernP)⟦(2 : ℤ)⟧ ⊞
      unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) :=
  biprod.lift
    ((SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).map
        (biprod.fst (X := (line l E p.classes.chernS)⟦(2 : ℤ)⟧)
          (Y := unit S (Arings l E S))) ≫ (kernelShiftedLine l E k.lineQ).hom)
    ((SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).map
        (biprod.snd (X := (line l E p.classes.chernS)⟦(2 : ℤ)⟧)
          (Y := unit S (Arings l E S))) ≫ (k.coefficientQ.derivedIso l E).hom)

/-- Exactly alpha_i, Rp_i(delta), and the splitting trace, in composition order.
Source: Levelwise check, displayed c_i
(blueprint: def-sp-tower-p1-kernel-scalar-data). -/
def KernelSplittingData.scalar (k : KernelSplittingData l E p) (a : Bool) :
    unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) ⟶
      unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) :=
  p.sourceUnitAt l E a (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))) ≫
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).map
      (p.delta l E) ≫ k.trace l E a

/-- The ordinary etale trace for p_a, transported from the standard P1 over P.
Source: finite diagonal integrals, comparison of the product projections
(blueprint: def-sp-tower-p1-kernel-scalar-data). -/
def kernelFiniteTrace (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (c : ProjectiveCoordinates l E n p)
    (bP : Etale.ArbitraryBaseFiniteP1Splitting (levelRing l E n) (l ^ (n + 1))
      (levelAnnihilates l E n) c.transport (ProjectiveLine S) (lineExponentUnit l n hS))
    (a : Bool) :
    (EtaleWords.push (levelRing l E n) (Etale.projectiveLineDiagonalProjection S a)).obj
      (EtaleWords.line (levelRing l E n) (l ^ (n + 1)) (levelAnnihilates l E n)
        (diagonalSurface S)) ⟶
      Etale.ordinaryFiniteUnit (levelRing l E n) (ProjectiveLine S) :=
  Etale.ordinaryFiniteP1DiagonalChartMap (levelRing l E n) (l ^ (n + 1))
    (levelAnnihilates l E n) c.transport S (baseExponentUnit l n hS) a ≫ bP.trace

/-- The specified finite composite, including the canonical composition source alpha.
The supported boundary in EtaleWords.delta has the positive divisor-Chern sign.
Source: finite diagonal integrals, c_i at level n+1
(blueprint: def-sp-tower-p1-kernel-scalar-data). -/
def kernelFiniteScalar (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (c : ProjectiveCoordinates l E n p)
    (bP : Etale.ArbitraryBaseFiniteP1Splitting (levelRing l E n) (l ^ (n + 1))
      (levelAnnihilates l E n) c.transport (ProjectiveLine S) (lineExponentUnit l n hS))
    (hD : (diagonalImmersion S).ker.IsInvertible) (a : Bool) :
    Etale.ordinaryFiniteUnit (levelRing l E n) (ProjectiveLine S) ⟶
      Etale.ordinaryFiniteUnit (levelRing l E n) (ProjectiveLine S) :=
  Etale.projectiveLineDiagonalAlpha (levelRing l E n) S a ≫
    (EtaleWords.push (levelRing l E n) (Etale.projectiveLineDiagonalProjection S a)).map
      (EtaleWords.delta (levelRing l E n) (l ^ (n + 1))
        (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime l)) _) (levelAnnihilates l E n)
        S hD (surfaceExponentUnit l n hS)) ≫ kernelFiniteTrace l E n c bP a

/-- Every part of the finite scalar comparison is an equation of the specified maps.
In particular alpha is the canonical composition source, not a free source isomorphism.
Source: Levelwise check, finite composite and sign
(blueprint: def-sp-tower-p1-kernel-scalar-data). -/
structure KernelFiniteNormalization (k : KernelSplittingData l E p)
    (n : ℕ) [Finite (SpTowerShriek.R l E n)] (c : ProjectiveCoordinates l E n p)
    (bP : Etale.ArbitraryBaseFiniteP1Splitting (levelRing l E n) (l ^ (n + 1))
      (levelAnnihilates l E n) c.transport (ProjectiveLine S) (lineExponentUnit l n hS))
    (hD : (diagonalImmersion S).ker.IsInvertible) : Prop where
  alpha : ∀ a : Bool, WordComparison l E n (c.unitP l E n)
    (c.push l E n (Etale.projectiveLineDiagonalProjection S a)
      (c.push l E n (diagonalImmersion S) (c.unitP l E n)))
    (p.sourceUnitAt l E a (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))))
    (Etale.projectiveLineDiagonalAlpha (levelRing l E n) S a)
  pushed_delta : ∀ a : Bool, WordComparison l E n
    (c.push l E n (Etale.projectiveLineDiagonalProjection S a)
      (c.push l E n (diagonalImmersion S) (c.unitP l E n)))
    (c.push l E n (Etale.projectiveLineDiagonalProjection S a) (c.lineW l E n))
    ((SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).map (p.delta l E))
    ((EtaleWords.push (levelRing l E n) (Etale.projectiveLineDiagonalProjection S a)).map
      (EtaleWords.delta (levelRing l E n) (l ^ (n + 1))
        (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime l)) _) (levelAnnihilates l E n)
        S hD (surfaceExponentUnit l n hS)))
  trace : ∀ a : Bool, WordComparison l E n
    (c.push l E n (Etale.projectiveLineDiagonalProjection S a) (c.lineW l E n))
    (c.unitP l E n) (k.trace l E a) (kernelFiniteTrace l E n c bP a)
  composite : ∀ a : Bool, WordComparison l E n (c.unitP l E n) (c.unitP l E n)
    (k.scalar l E a) (kernelFiniteScalar l E n c bP hD a)
  finite_identity : ∀ a : Bool, kernelFiniteScalar l E n c bP hD a =
    𝟙 (Etale.ordinaryFiniteUnit (levelRing l E n) (ProjectiveLine S))

/-- Evaluation at every positive level uses normalized constant, root and site-mate
coordinates, and the ordinary finite unit/Chern splitting over P.
Source: Levelwise check (blueprint: def-sp-tower-p1-kernel-scalar-data). -/
def KernelSplittingData.finiteNormalization (k : KernelSplittingData l E p)
    (hD : (diagonalImmersion S).ker.IsInvertible) (n : ℕ) : Prop :=
  letI : Finite (SpTowerShriek.R l E n) := p.classes.base.finite n
  ∃ (c : ProjectiveCoordinates l E n p)
    (bP : Etale.ArbitraryBaseFiniteP1Splitting (levelRing l E n) (l ^ (n + 1))
      (levelAnnihilates l E n) c.transport (ProjectiveLine S) (lineExponentUnit l n hS)),
    KernelFiniteNormalization l E k n c bP hD

/-- All the asserted equalities in the actual tower derived category, and their
finite etale descriptions. Degree-zero full faithfulness is used only on A_P[0].
Source: base change of trace and Levelwise check
(blueprint: def-sp-tower-p1-kernel-scalar-data). -/
structure KernelScalarNormalization (p : Presentation l E S hS)
    (k : KernelSplittingData l E p) : Prop where
  exchange_iso : ∀ a : Bool, IsIso (k.exchange l E a)
  source_comparison_iso : IsIso (k.sumComparison l E)
  splitting_base_change : ∀ a : Bool,
    (SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).map k.splittingQ.hom ≫
        k.exchange l E a = k.sumComparison l E ≫ (k.splittingProjection a).hom
  inverse_base_change : ∀ a : Bool,
    k.exchange l E a ≫ (k.splittingProjection a).inv =
      (SpTowerShriek.pull l E p.classes.base
        (p.operations.geometry (ProjectiveLine S ↘ S))).map k.splittingQ.inv ≫
          k.sumComparison l E
  trace_base_change : ∀ a : Bool,
    k.exchange l E a ≫ k.trace l E a =
      (SpTowerShriek.pull l E p.classes.base
        (p.operations.geometry (ProjectiveLine S ↘ S))).map (p.trace l E) ≫
          (k.coefficientQ.derivedIso l E).hom
  alpha_iso : ∀ a : Bool, IsIso (p.sourceUnitAt l E a
    (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))))
  scalar_identity : ∀ a : Bool, k.scalar l E a =
    𝟙 (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
  cartier : (diagonalImmersion S).ker.IsInvertible
  levels : ∀ n : ℕ, k.finiteNormalization l E cartier n
  degree_zero_lift : ∀ a : Bool,
    ∃! f : coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)) ⟶
      coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)),
      (DerivedCategory.singleFunctor
        (Systems (ProjectiveLine S) (Arings l E (ProjectiveLine S))) 0).map f = k.scalar l E a
  degree_zero_detection : ∀ (f g :
    coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)) ⟶
      coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S))),
    (∀ n : ℕ, (SpTowerShriek.ev l E (ProjectiveLine S) n).map f =
      (SpTowerShriek.ev l E (ProjectiveLine S) n).map g) → f = g
```

The original module now contains:

```lean
public import Sheaf.Paper.TowerP1KernelScalarData
```

## Users

`python3 tools/downstream.py Sheaf.Paper.TowerP1KernelScalarNormalization
--uses KernelSplittingData` reports zero downstream modules and just the item
itself as a textual user. A search over both library roots finds no importer.
The DAG parents still require this theorem, and it is retained and proved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.TowerP1KernelScalarNormalization | V4 | Imports the same public declarations from their new owner; proves the original theorem. |
| Sheaf.Paper.TowerP1KernelScalarData | new in this delivery | Owns all eleven existing interfaces, without changing their meaning. |
| Sheaf.Paper.TowerP1KernelSplittingBaseChange | new in this delivery | States the forward splitting square and canonical source isomorphisms. |
| Sheaf.Paper.TowerP1KernelFiniteComparison | new in this delivery | States the finite commuting squares for a specified normalized splitting. |

No consumer adaptation is forced. The target meanings and elaborated statements
are unchanged: the re-export exposes exactly the same constructions and data.

## Status

landed 20261025T164600-L-1037403 2026-10-25 (merge of deliver/V4/Sheaf.Paper.TowerP1KernelScalarNormalization)
