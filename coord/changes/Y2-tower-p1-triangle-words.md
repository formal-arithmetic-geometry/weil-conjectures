# AlgebraicGeometry.ProEtale.SpTowerP1 triangle word module extraction

## Reason

The original file combines sixteen concrete definitions and the six-clause theorem.
The diagonal-free trace rearrangements and the insertion transport must refer to
those exact definitions, while the theorem imports the lemmas. Extracting the
unchanged definitions avoids an import cycle. The original file publicly re-exports
the new word module; every old full name and type remains available. This is a
module relocation, with no mathematical change to any existing definition or statement.
Five further concrete compositions name internal words; none chooses existence data.

## Old

The following definitions were in `Sheaf.Paper.TowerP1TriangleFactorization`:

```lean
def Presentation.qUnitIso (p : Presentation l E S hS) :
    (SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).obj (unit S (Arings l E S)) ≅
        unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) :=
  (eqToIso (congrArg (SpTowerShriek.pull l E p.classes.base) p.q_geometry)).app _ ≪≫
    p.classes.projective.coefficientPullback.derivedIso l E

/-- The shifted Tate pullback for q, with the same root restriction and shift convention.
Source: Reduction, Tate identifications (blueprint: lem-sp-tower-p1-triangle-factorization). -/
def Presentation.qLineIso (p : Presentation l E S hS) :
    (SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).obj
        ((line l E p.classes.chernS)⟦(2 : ℤ)⟧) ≅
          (line l E p.classes.chernP)⟦(2 : ℤ)⟧ :=
  (eqToIso (congrArg (SpTowerShriek.pull l E p.classes.base) p.q_geometry)).app _ ≪≫
    ((SpTowerShriek.pull l E p.classes.base p.classes.projective.geometry).commShiftIso
      (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso (p.classes.projective.linePullback.derivedIso l E)

/-- Pullback of the Tate line along the first projection, through the canonical square.
Source: Reduction, common pulled-back twist (blueprint: lem-sp-tower-p1-triangle-factorization).
-/
def Presentation.line1Iso (p : Presentation l E S hS) :
    (SpTowerShriek.pull l E p.classes.base (p.operations.geometry
      (pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).obj
        ((line l E p.classes.chernP)⟦(2 : ℤ)⟧) ≅
          (line l E p.classes.chernW)⟦(2 : ℤ)⟧ :=
  (SpTowerShriek.pull l E p.classes.base
    (p.operations.geometry (pullback.fst _ _))).mapIso (p.qLineIso l E).symm ≪≫
  (SpTowerShriek.square l E p.classes.base p.operations
    (pullback.fst _ _) (pullback.snd _ _) (ProjectiveLine S ↘ S)
    (ProjectiveLine S ↘ S) pullback.condition).symm.app _ ≪≫
  (SpTowerShriek.pull l E p.classes.base
    (p.operations.geometry (pullback.snd _ _))).mapIso (p.qLineIso l E) ≪≫ p.line2Iso l E

/-- The shifted line, as an object of the full comparison domain.
Source: Reduction, exchange at T (blueprint: lem-sp-tower-p1-triangle-factorization). -/
def shiftedLineObject {p : Presentation l E S hS} {d : Maps l E p}
    (h : EtaleOriginComparisonsWithLine l E p d) : C l E p.classes.base (ProjectiveLine S) :=
  ⟨(line l E p.classes.chernP)⟦(2 : ℤ)⟧, h.line_domain⟩

/-- Canonical base-change of the splitting trace along the first projection. Pulling back
b_q, its inverse and second projection gives exactly this inverse-exchange word.
Source: Reduction, t1 v_T = q* t_q (blueprint: lem-sp-tower-p1-triangle-factorization). -/
def projectionTrace1 {p : Presentation l E S hS} {d : Maps l E p}
    (h : EtaleOriginComparisonsWithLine l E p d) :
    (SpTowerShriek.push l E p.classes.base (p.operations.geometry
      (pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).obj
        ((line l E p.classes.chernW)⟦(2 : ℤ)⟧) ⟶
          unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) :=
  letI := h.exchange_swap (shiftedLineObject l E h)
  (SpTowerShriek.push l E p.classes.base
    (p.operations.geometry (pullback.fst _ _))).map (p.line2Iso l E).inv ≫
    inv (p.exchangeSwap l E (shiftedLineObject l E h).obj) ≫
    (SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).map (p.trace l E) ≫
    (p.qUnitIso l E).hom

/-- Canonical base-change of the same splitting trace along the second projection.
Source: Reduction, t2 u_T = q* t_q (blueprint: lem-sp-tower-p1-triangle-factorization). -/
def projectionTrace2 {p : Presentation l E S hS} {d : Maps l E p}
    (h : EtaleOriginComparisonsWithLine l E p d) :
    (SpTowerShriek.push l E p.classes.base (p.operations.geometry
      (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).obj
        ((line l E p.classes.chernW)⟦(2 : ℤ)⟧) ⟶
          unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) :=
  letI := d.exchange (shiftedLineObject l E h)
  (SpTowerShriek.push l E p.classes.base
    (p.operations.geometry (pullback.snd _ _))).map (p.line1Iso l E).inv ≫
    inv (p.exchange l E (shiftedLineObject l E h).obj) ≫
    (SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).map (p.trace l E) ≫
    (p.qUnitIso l E).hom

/-- Either of the two projection traces, with false denoting p1 and true denoting p2.
Source: Reduction, t_i (blueprint: lem-sp-tower-p1-triangle-factorization). -/
def projectionTrace {p : Presentation l E S hS} {d : Maps l E p}
    (h : EtaleOriginComparisonsWithLine l E p d) (a : Bool) :
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).obj
        ((line l E p.classes.chernW)⟦(2 : ℤ)⟧) ⟶
          unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) :=
  match a with
  | false => projectionTrace1 l E h
  | true => projectionTrace2 l E h

/-- The scalar c_i retains the direct-image composition source alpha_i.
Source: Reduction, the displayed scalars (blueprint: lem-sp-tower-p1-triangle-factorization). -/
def diagonalScalar {p : Presentation l E S hS} {d : Maps l E p}
    (h : EtaleOriginComparisonsWithLine l E p d) (a : Bool) :
    unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) ⟶
      unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) :=
  p.sourceUnitAt l E a (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))) ≫
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).map
        (p.delta l E) ≫ projectionTrace l E h a

/-- Tensor an actual coefficient endomorphism with the identity and use both unitors.
Source: Reduction, scalar contraction (blueprint: lem-sp-tower-p1-triangle-factorization). -/
def scalarContraction (p : Presentation l E S hS)
    (M : SpTowerShriek.D l E (ProjectiveLine S))
    (c : unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) ⟶
      unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))) : M ⟶ M :=
  (p.tensorP.rightUnit l E M).inv ≫
    (SpTowerShriek.tensor l E p.classes.base (ProjectiveLine S)).map (Prod.mkHom (𝟙 M) c) ≫
    (p.tensorP.rightUnit l E M).hom

/-- Projection in the outside-first order, using the specified signed symmetry on both sides.
Source: Reduction, projection reordering (blueprint: lem-sp-tower-p1-triangle-factorization). -/
def outsideProjection (p : Presentation l E S hS) (a : Bool)
    (M : SpTowerShriek.D l E (ProjectiveLine S))
    (N : SpTowerShriek.D l E (diagonalSurface S)) :
    (SpTowerShriek.tensor l E p.classes.base (ProjectiveLine S)).obj
      (M, (SpTowerShriek.push l E p.classes.base
        (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).obj N) ⟶
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).obj
        ((SpTowerShriek.tensor l E p.classes.base (diagonalSurface S)).obj
          ((SpTowerShriek.pull l E p.classes.base
            (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).obj M, N)) :=
  ((p.tensorP.symmetry l E).braiding _ _).hom ≫
    projection l E (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a)) N M ≫
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).map
        (((p.tensorW.symmetry l E).braiding _ _).hom)

/-- The supported projection at either p_i, including Delta^*p_i^*=1 and the left unitor.
Source: Reduction, diagonal source (blueprint: lem-sp-tower-p1-triangle-factorization). -/
def diagonalProjectionAt (p : Presentation l E S hS) (a : Bool)
    (M : SpTowerShriek.D l E (ProjectiveLine S)) :=
  projection l E (p.operations.geometry (diagonalImmersion S))
    (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
    ((SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).obj M) ≫
  (SpTowerShriek.push l E p.classes.base (p.operations.geometry (diagonalImmersion S))).map
    ((SpTowerShriek.tensor l E p.classes.base (ProjectiveLine S)).map
      (Prod.mkHom (𝟙 _) ((p.diagonalPull l E _ (diagonalIdentity S a)).hom.app M)) ≫
        (p.tensorP.leftUnit l E M).hom)

/-- The inverse supported projection is written from its three canonical inverse factors.
Source: Reduction, inverse diagonal projection
(blueprint: lem-sp-tower-p1-triangle-factorization). -/
def diagonalProjectionInverse {p : Presentation l E S hS} {d : Maps l E p}
    (h : EtaleOriginComparisonsWithLine l E p d) (a : Bool)
    (M : C l E p.classes.base (ProjectiveLine S)) :=
  letI := h.projection_diagonal a M
  (SpTowerShriek.push l E p.classes.base (p.operations.geometry (diagonalImmersion S))).map
    ((p.tensorP.leftUnit l E M.obj).inv ≫
      (SpTowerShriek.tensor l E p.classes.base (ProjectiveLine S)).map
        (Prod.mkHom (𝟙 _) ((p.diagonalPull l E _ (diagonalIdentity S a)).inv.app M.obj))) ≫
  inv (projection l E (p.operations.geometry (diagonalImmersion S))
    (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
    ((SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).obj M.obj))

/-- Inverse outside-first projection of the shifted line, retaining the two signed swaps.
Source: Reduction, inverse projection (blueprint: lem-sp-tower-p1-triangle-factorization). -/
def outsideLineProjectionInverse {p : Presentation l E S hS} {d : Maps l E p}
    (h : EtaleOriginComparisonsWithLine l E p d) (a : Bool)
    (M : C l E p.classes.base (ProjectiveLine S)) :=
  letI := h.projection_projections a M
  (SpTowerShriek.push l E p.classes.base
    (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).map
      (((p.tensorW.symmetry l E).braiding
        ((line l E p.classes.chernW)⟦(2 : ℤ)⟧)
        ((SpTowerShriek.pull l E p.classes.base
          (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).obj M.obj)).inv) ≫
  inv (projection l E (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))
    ((line l E p.classes.chernW)⟦(2 : ℤ)⟧) M.obj) ≫
  ((p.tensorP.symmetry l E).braiding M.obj
    ((SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).obj
        ((line l E p.classes.chernW)⟦(2 : ℤ)⟧))).inv

/-- The diagonal part of eta, using p_i on both occurrences, before any final exchange.
Source: Reduction, z_M (blueprint: lem-sp-tower-p1-triangle-factorization). -/
def diagonalInsertion {p : Presentation l E S hS} {d : Maps l E p}
    (h : EtaleOriginComparisonsWithLine l E p d) (a : Bool)
    (M : C l E p.classes.base (ProjectiveLine S)) :=
  p.sourceUnitAt l E a M.obj ≫
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).map
        (diagonalProjectionInverse l E h a M ≫
          (SpTowerShriek.tensor l E p.classes.base (diagonalSurface S)).map
            (Prod.mkHom (p.delta l E) (𝟙 _)) ≫
          ((p.tensorW.symmetry l E).braiding _ _).hom)

/-- Projection of the diagonal arrow has the explicit factor 1_M tensor Rp_i(delta),
with alpha_i on the source; this definition names that factor, not its asserted equality.
Source: Reduction, first-arrow factor (blueprint: lem-sp-tower-p1-triangle-factorization). -/
def diagonalTensorFactor (p : Presentation l E S hS) (a : Bool)
    (M : SpTowerShriek.D l E (ProjectiveLine S)) :=
  (p.tensorP.rightUnit l E M).inv ≫
    (SpTowerShriek.tensor l E p.classes.base (ProjectiveLine S)).map
      (Prod.mkHom (𝟙 M)
        (p.sourceUnitAt l E a (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))) ≫
          (SpTowerShriek.push l E p.classes.base
            (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).map
              (p.delta l E)))

/-- The expanded projection/diagonal/trace word before applying F in the first triangle.
Source: Reduction, expanded composites (blueprint: lem-sp-tower-p1-triangle-factorization). -/
def expandedContraction {p : Presentation l E S hS} {d : Maps l E p}
    (h : EtaleOriginComparisonsWithLine l E p d) (a : Bool)
    (M : C l E p.classes.base (ProjectiveLine S)) :=
  diagonalInsertion l E h a M ≫
    outsideLineProjectionInverse l E h a M ≫
    (SpTowerShriek.tensor l E p.classes.base (ProjectiveLine S)).map
      (Prod.mkHom (𝟙 M.obj) (projectionTrace l E h a)) ≫
    (p.tensorP.rightUnit l E M.obj).hom

```

## New

The definitions above keep the same full names, types and bodies verbatim in
`Sheaf.Paper.TowerP1TriangleWords`. The original module now includes:

```lean
public import Sheaf.Paper.TowerP1TriangleWords
```

The new internal words, given by explicit compositions, are:

```lean
def unitTail {p : Presentation l E S hS} (d : Maps l E p)
    (M : C l E p.classes.base (ProjectiveLine S)) :=
  letI := d.exchange M
  letI := d.projection2 M
  (SpTowerShriek.push l E p.classes.base
    (p.operations.geometry
        (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).map
      ((SpTowerShriek.tensor l E p.classes.base (diagonalSurface S)).map
        (Prod.mkHom (𝟙 ((SpTowerShriek.pull l E p.classes.base
          (p.operations.geometry
        (pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).obj M.obj))
          (p.line2Iso l E).inv)) ≫
  inv (projection l E (p.operations.geometry
        (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))
    ((SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry
        (pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).obj M.obj)
    ((line l E p.classes.chernP)⟦(2 : ℤ)⟧)) ≫
  (SpTowerShriek.tensor l E p.classes.base (ProjectiveLine S)).map
    (Prod.mkHom (inv (p.exchange l E M.obj)) (𝟙 _))

/-- The initial diagonal word of eta, with p2 outside and p1 inside.
Source: Reduction, z_M (blueprint: def-sp-tower-p1-triangle-words). -/
def unitInsertion {p : Presentation l E S hS} (d : Maps l E p)
    (M : C l E p.classes.base (ProjectiveLine S)) :=
  letI := d.diagonalProjection M
  p.sourceUnit l E M.obj ≫
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry
        (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).map
        (inv (p.diagonalProjection l E M.obj) ≫
          (SpTowerShriek.tensor l E p.classes.base (diagonalSurface S)).map
            (Prod.mkHom (p.delta l E) (𝟙 _)) ≫
          ((p.tensorW.symmetry l E).braiding _ _).hom)

/-- The projection/trace tail, before insertion of any supported class.
Source: Reduction, D_M (blueprint: def-sp-tower-p1-triangle-words). -/
def contractionTail {p : Presentation l E S hS} {d : Maps l E p}
    (h : EtaleOriginComparisonsWithLine l E p d) (a : Bool)
    (M : C l E p.classes.base (ProjectiveLine S)) :=
  outsideLineProjectionInverse l E h a M ≫
    (SpTowerShriek.tensor l E p.classes.base (ProjectiveLine S)).map
      (Prod.mkHom (𝟙 M.obj) (projectionTrace l E h a)) ≫
    (p.tensorP.rightUnit l E M.obj).hom

/-- Direct-image composition comparison for qp2 = qp1, the conjugate of the
specified pullback square, with no arbitrary comparison isomorphism.
Source: Reduction, RV=RU (blueprint: def-sp-tower-p1-triangle-words). -/
def Presentation.pushSwap (p : Presentation l E S hS) :=
  (conjugateIsoEquiv
    ((SpTowerShriek.adjunction l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).comp
      (SpTowerShriek.adjunction l E p.classes.base
        (p.operations.geometry
        (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))))
    ((SpTowerShriek.adjunction l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).comp
      (SpTowerShriek.adjunction l E p.classes.base
        (p.operations.geometry
        (pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))))))
    (SpTowerShriek.square l E p.classes.base p.operations
      (pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
        (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
        (ProjectiveLine S ↘ S)
      (ProjectiveLine S ↘ S) pullback.condition).symm

/-- The canonical identification p1*GK = p2*GK uses the square on K and the
specified two shifted-line comparisons on the twist factor.
Source: Reduction, aN=bN (blueprint: def-sp-tower-p1-triangle-words). -/
def rightPullComparison (p : Presentation l E S hS)
    (K : SpTowerShriek.D l E S) :
    (SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry
        (pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).obj ((p.G l E).obj K) ≅
    (SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry
        (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).obj ((p.G l E).obj K) :=
  (p.operations.geometry
        (pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))).tensorPullback.app
    ((SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).obj K,
      (line l E p.classes.chernP)⟦(2 : ℤ)⟧) ≪≫
  (SpTowerShriek.tensor l E p.classes.base (diagonalSurface S)).mapIso
    (Iso.prod
      ((SpTowerShriek.square l E p.classes.base p.operations
        (pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
        (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
        (ProjectiveLine S ↘ S)
        (ProjectiveLine S ↘ S) pullback.condition).symm.app K)
      (p.line1Iso l E ≪≫ (p.line2Iso l E).symm)) ≪≫
  ((p.operations.geometry
        (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))).tensorPullback.app
    ((SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).obj K,
      (line l E p.classes.chernP)⟦(2 : ℤ)⟧)).symm

```

The original theorem keeps its signature verbatim and has a complete combining proof.
No target statement or target meaning changes. This is not a split to evade the
compiler limit: the original extracted file compiled in 31 seconds; the separation
exists to make the dependency direction acyclic.

## Users

`python3 tools/downstream.py Sheaf.Paper.TowerP1TriangleFactorization` reports zero
current Lean importers. This is not used to withdraw anything: unfinished DAG
parents remain attached to the unchanged theorem. A `--uses diagonalInsertion`
search reports only the original module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.TowerP1TriangleFactorization | Y2 | Publicly re-exports every old definition; theorem uses the new lemmas. |
| Sheaf.Paper.TowerP1TriangleWords | new in Y2 delivery | Contains all old definitions and explicit internal compositions. |
| Sheaf.Paper.TowerP1FirstTraceReordering | new in Y2 delivery | Imports the canonical word module. |
| Sheaf.Paper.TowerP1SecondTraceReordering | new in Y2 delivery | Imports the canonical word module. |
| Sheaf.Paper.TowerP1DiagonalTransport | new in Y2 delivery | Imports the canonical word module. |
| Sheaf.Paper.TowerP1DiagonalProjectionFactor | new in Y2 delivery | Imports the canonical word module. |

## Status

landed 20261025T164820-L-1092122 2026-10-25 (merge of deliver/Y2/Sheaf.Paper.TowerP1TriangleFactorization)
