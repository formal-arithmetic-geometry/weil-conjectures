# Stage-2 statement: lem-sfb-snc-pointed-affine-common-refinement

## Worker report

The module `Sheaf.AlgebraicGeometry.SNCPointedAffineCommonRefinement` states the
pointed common-refinement lemma and its unique, composable ring comparisons. All
three theorems have only `sorry` proofs. All structures and definitions have real
data or explicit logical formulas. The original node statement, proof, dependency
lists, and review metadata are unchanged; only `lean` is set in the delivered node.

The accepted Q76 delivery recorded in the ledger is the stage-1 split. It has no
Lean record. The earlier worker's statement that this merge prevents stage 2 is
not a stage-2 completion: there was no retained module, node copy or report. I read
that accepted split and built on it. There is no released repair note for this item.

Hypotheses and clauses are represented as follows:

1. The field is `{k : Type u} [Field k]`. The scheme is `Y : Scheme.{u}` with
   its structural map `a : Y ⟶ Spec (.of k)`. `[LocallyOfFiniteType a]` and
   `[QuasiCompact a]` are finite type; `[IsSeparated a]` is separatedness.
   `_hY : IsRegularScheme Y` includes local Noetherianity and stalkwise regularity.
2. The finite labelled boundary is `D`, `_hD`, `n`, `C : Fin n → Y.IdealSheafData`,
   and `_hC`. The last hypothesis specifies that THIS labelled component list
   witnesses the boundary: distinct supports, integral regular components, their
   support union equal to `D.support`, and regular intersections of codimension
   `J.card` for every subset. These are the clauses of the recorded SNC definition;
   the theorem does not use an unrelated component list from its existential.
   Using `Fin n` represents every finite labelled family, including the empty one.
3. `I : Finset (Fin n)` selects the labels. The bound open `U` and `_hU` say
   exactly `U = (⨆ j : {j : Fin n // j ∉ I}, (C j.val).support).compl`.
   This binds the actual open rather than introducing a second definition of the
   existing stratum-open notion in the downstream residual-chart package.
4. The reduced intersection `S` is written inline as
   `((⨆ i ∈ I, (C i).comap U.ι).radical).subscheme`. The geometric point is
   `s : Spec (.of Ω) ⟶ S`, with `[Field Ω] [IsAlgClosed Ω]`. The points supplied
   to the chart structures are its composites with `S.subschemeι` into `U`.
5. The finite input family is `{A : Type w} [Finite A]` and
   `Q : A → SNCPointedAffineChart ...`. Each chart carries its actual
   `B : CommRingCat.{u}`, `v : Spec B ⟶ U.toScheme`, and `etale : Etale v`.
   The chart's `t` has one entry for each selected label.
6. `equations` says `(C i).comap v = ofIdealTop (Ideal.span {ΓSpecIso.inv (t i)})`.
   Here the `C` in the chart is already the selected component restricted to `U`.
   Thus each equation generates the ideal of the actual pulled-back closed
   subscheme, and the generators are not allowed to define some other boundary.
7. `parameters` tests every prime `q`. It supplies Noetherianity of the local ring,
   an ordering of the labels, and a full `IsLocalRing.IsRegularSystemOfParameters`
   list. The distinct equations vanishing at `q` map to a sublist of that list.
   Units are filtered out; no nonvanishing equation is required to be a parameter.
   The ordering can be chosen at each prime because the stated property is that
   the labelled vanishing equations are part of a regular parameter system.
8. `SNCPointedAffineChart.ideal` is exactly `Ideal.span (Set.range t)`, without
   inserting a radical. `residual_regular` and `residual_connected` assert the
   regular nonempty connected residual spectrum. `ConnectedSpace` includes
   nonemptiness. `point` is its lift of the specified geometric point, and
   `point_base` is the required equality over `U`.
9. `HasSNCPointedAffineCommonRefinement Q` is an explicit existential: a chart
   `W` of the same type and a refinement `f i` for every input. The refinement
   consists of the contravariant ring map, the equality over `U`, its étaleness,
   and the equality of the lifted points. The next conjunct states exactly
   `(Q i).ideal.map (f i).ringMap.hom = W.ideal`, namely `J_i B = J`.
10. The same existential supplies `SNCAffineCoverData` for every input and for
    `W`. Its `henselization` is the actual cocone of the recorded étale
    neighbourhood diagram, with `isColimit`. It also records henselianness and
    the bijective residue quotient from `pair_henselization`. The marked point
    reduces to the chart point. Connectedness of the henselized spectrum permits
    use of the existing pointed universal cover. These are supplied in the
    conclusion, not assumed as stronger hypotheses on the input charts.
11. In each cover datum, `H`, `h`, `b`, `b_factor`, `universalIso`, and its base
    and marked-point equations identify `Spec H` with the existing pointed
    universal cover of the henselization. `residualCoverIso` identifies precisely
    `Spec (H ⧸ JH)` with the pointed universal cover of the residual scheme;
    its base and point equations preserve these identifications.
12. `SNCAffineCoverMap` supplies the henselization map and the universal-cover
    ring map. `henselization_base`, `cover_henselization`, `cover_base` and the
    marked-point equations give the stated commutative squares. `residualBaseMap`
    is `B_i/J_i → B/J`, with its quotient square. `residualMap` is
    `H_i/J_i H_i → H/JH`; `reduction` and `residual_base` are the reduction and
    residual-base squares, and `residual_point` ensures it is the pointed map.
13. `sncAffineCoverMap_unique` gives existence and uniqueness for ANY pointed
    refinement and ANY actual cover data, as well as equality of extended ideals.
    Base and marked-point equations uniquely characterize the existing canonical
    pointed-limit map: after projection to any finite cover, pointed sections
    agree on the connected source. No arbitrary map replaces that construction.
14. `sncAffineCoverMap_composition` writes the composition equalities on all four
    levels: henselization rings, universal-cover rings, residual base rings, and
    residual-cover rings. The comparison is independent of the chosen affine
    models and cofinal small systems: any such system is canonically identified
    with the existing universal-cover object by its pointed limit property, and
    the uniqueness assertion applies to these identifications as well.

The auxiliary structures and predicate package just this node's charts and its
specified diagrams. They are public declarations of the owning module, listed
in `lean.declarations`, with source and blueprint docstrings. They introduce no
independent extra mathematical assumption and choose no object from a bare
existence theorem. The generic index universes `v` (component labels) and `w`
(family indices) are independent of the scheme/ring universe `u`; in particular,
using the small type underlying `I : Finset (Fin n)` does not force `u = 0`.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, and
  `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.SpecToEquivOfField` read as
  the recorded geometric-point interpretation. Geometric points are inline.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `WeilConjectures.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters`.
- `WeilConjectures.RingTheory.PairHenselization`: `RingTheory.pair_henselization`;
  the cocone diagram is exactly its diagram, not a different henselian ring.
- `Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech`: the recorded
  `nonempty_pointedLimitCechCoordinates`, its naturality and composition statements
  were read; the statement uses the underlying `Scheme.UniversalCover.cover`,
  `proj`, and `pt` supplied by its public upstream import
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCoverConstruction`.
  The explicit construction of `UniversalCover.map` and its base/point signatures
  were also read. No extra choice of fundamental-group realization is needed here.

Proof imports additionally include the recorded henselization universal property,
Noetherian connected-component theorem, and the Mathlib affine/Noetherian,
principal-open and clopen-idempotent tools. The still unstated proof prerequisites
are named in the proof docstrings and retain their existing DAG records; they
are not statement prerequisites. The downstream residual-chart module is not
imported, preventing a future proof import cycle and avoiding its extra root-tower
and characteristic data.

Edge cases checked before writing: `A` empty still requires a reference chart,
which exists through the given point; the conclusion has no nonempty-family
hypothesis. `I` empty has zero parameters and residual ideal zero; the connected
component is chosen in the whole affine chart, and no nonexistent parameter is
introduced. An empty stratum has no geometric point, so there is no spurious
existence assertion. Dimension zero allows the empty full parameter list, and
all components absent at a prime are filtered out. Residual disconnectedness
of fibre products is handled by localizing at a lift of the residual component's
idempotent; the lift is not claimed to be idempotent in the ambient ring. There
is no restriction on characteristic. The common equations need generate the same
ideals as the images of the input equations; equality of generators is not imposed.

Searches actually made (logged by `msearch.py` in `searches.jsonl`):

- LeanFinder: `Pointed common affine etale refinements of strict normal crossings
  charts compatible with pair henselizations and universal covers`. Eight hits:
  standard étale presentations, étale morphisms and smooth local presentations;
  none is the common-refinement statement with the specified diagrams.
- Loogle: `"Etale", "pullback"`. Two hits are the pullback instances on
  `Scheme.Etale` and `Scheme.AffineEtale`; neither states this node.
- Mathlib grep in `AlgebraicGeometry`:
  `commonRefinement|common_refinement|pointedLimitMap`. Zero hits.
- LeanSearch: `Finite pointed affine etale strict normal crossings charts have a
  common pointed refinement compatible with henselization and universal finite
  etale covers`. Eight hits include directed-cover point refinements, affine
  refinements, and finite-type limit factorization. None has the SNC equations,
  henselizations, and residual universal covers together.
- Direct `rg` over both `lean/WeilConjectures` and `lean/Sheaf`, for the node id,
  `SNCPointedAffine`, and related chart/refinement names, found no existing exact
  declaration. I read `SNCUniversalResidualCharts.lean`; its `SNCResidualChart`
  contains additional parameter-root towers and choices absent from this node,
  so it cannot be used as the type of the arbitrary input charts here.

Sources read: the node's six proof steps; Stacks `more-algebra.tex`
`lemma-henselization` (0A02), including its actual étale-colimit construction and
adjunction; `pione.tex` `lemma-gabber` (09ZS), and the existing pointed-limit
construction/naturality declarations. No mathematical statement correction or
STATEMENT-DISPUTED finding is needed.

## Second reading by Q68

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
