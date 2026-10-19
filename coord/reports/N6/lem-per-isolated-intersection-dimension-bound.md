## Worker report

The module `Sheaf.RingTheory.IsolatedIntersectionDimensionBound` states
`PrimeSpectrum.isolated_intersection_dimension_bound`, with its sole proof `sorry`.
The accompanying definition module constructs `ModuleCat.localCohomologicalDimension`
as an actual supremum, using the existing ideal-power torsion functor and Mathlib's
right derived functors. No object is chosen from an existence theorem.

Read the node's full statement and five proof steps, its three recorded statement
dependencies, the two Mathlib proof leaves, and the two currently unstated local
cohomology proof dependencies. Read Stacks `local-cohomology.tex`, Definition 0DX8,
Lemma 0DX7, and Lemmas 0DXA, 0DXE, 0DXF, especially the quotient argument at 0DXF.
No correction to the item is necessary.

Hypothesis and clause correspondence:

- The commutative ring `(A,m)` is `(A : Type u) [CommRing A] [IsLocalRing A]`.
  Mathlib's `IsLocalRing` includes nontriviality, so it also supplies the node's
  nonzero hypothesis. The maximal ideal point is `IsLocalRing.closedPoint A`.
- Noetherianity is `[IsNoetherianRing A]`, exactly the recorded declaration.
- Finite dimension is `hfinite : topologicalKrullDim (PrimeSpectrum A) < ⊤`.
  Nonemptiness of the spectrum follows from locality, so this is finite dimension.
- The proper ideal is `(I : Ideal A) (hI : I ≠ ⊤)`.
- `X = Spec A` is represented by `PrimeSpectrum A`, definitionally the underlying
  topological space of `AlgebraicGeometry.Spec (CommRingCat.of A)`.
- The first conjunct quantifies over every `Z : Set (PrimeSpectrum A)`, requires
  `IsClosed Z`, and renders the isolated intersection as
  `Z ∩ zeroLocus (I : Set A) = {IsLocalRing.closedPoint A}`.
- Its conclusion `topologicalKrullDim Z ≤ ModuleCat.localCohomologicalDimension I`
  uses the subtype topology on Z, exactly the recorded notion of dimension.
- The second conjunct quantifies over `p : PrimeSpectrum A`; this bundles precisely
  a prime ideal, available as `p.asIdeal`. Its premise is the stated intersection
  property of `V(p)` and `V(I)`, and its conclusion uses
  `topologicalKrullDim (PrimeSpectrum (A ⧸ p.asIdeal))` for `dim(A/p)`.
- `H_I^j(M)` is `((ModuleCat.idealPowerTorsion I).rightDerived j).obj M`.
  The definition uses `¬ CategoryTheory.Limits.IsZero` to record its nonvanishing.
  It takes the supremum of exactly these nonvanishing natural degrees over all
  `ModuleCat.{u} A`. A supremum in `WithBot ℕ∞` represents the empty case by bottom
  (the integer -1 for cohomological dimension), and preserves all natural values.
  For Noetherian rings every ideal is finitely generated and the source supplies a
  finite bound, so this is precisely the least integer in the node. Restricting
  module carriers to the ring universe follows the existing torsion interface;
  larger modules give the same dimension by the source's ring-module criterion
  (0DX7), so this omits no nonvanishing degree.

Dependency declarations used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; read its definition,
  docstring, and `isNoetherianRing_iff_ideal_fg`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`;
  read both definitions and docstrings. Only the underlying space is needed here.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`; read its chain definition
  and `topologicalKrullDim_subspace_le`.
- New node `def-per-local-cohomological-dimension` supplies
  `ModuleCat.localCohomologicalDimension` from
  `Sheaf.Algebra.Homology.LocalCohomologicalDimension`.
- Its construction reuses `ModuleCat.idealPowerTorsion` and its additive instance
  from `Sheaf.Algebra.Homology.IdealPowerTorsionFunctor`, belonging to the existing
  `def-sbc-ideal-power-torsion-functor`. Read the full module and the underlying
  `Ideal.primaryComponent` construction. Mathlib's `Functor.rightDerived` computes
  cohomology after applying the functor to an injective resolution; module-category
  Abelian and enough-injectives instances are explicitly imported.
- For the stated proof plan, the quotient-spectrum and radical leaves are provided
  by `Mathlib.RingTheory.Spectrum.Prime.Topology`, imported without `public`.
  Read `PrimeSpectrum.isClosedEmbedding_comap_of_surjective`,
  `PrimeSpectrum.range_comap_of_surjective`, `PrimeSpectrum.zeroLocus_eq_iff`,
  and `Ideal.radical_eq_sInf`. The change-of-rings and top-nonvanishing nodes have
  no declaration yet, so no import is invented for them. Their ids and exact use
  appear in the proof docstring, following the five recorded proof steps.

Edge cases checked before drafting: a field and I=0 give cd=dim=0, with H^0
nonzero; an empty Z cannot satisfy the singleton intersection; I=top is explicitly
excluded by hI; I=0 and Z supported only at the closed point give dimension zero;
p equal to the maximal ideal gives a field quotient and the zero-dimensional
bound; the prime clause includes nonmaximal primes whenever its premise holds.
For the new definition, the zero ring and I=top have no nonvanishing degrees and
hence value bottom, representing -1. I=0 on a nonzero ring has nonvanishing degree
zero and no positive degrees. No characteristic or equidimensionality assumption
is imposed. The proof docstring includes the zero-generator case in the radical
argument. There are no disputed statements.

Searches actually run through `msearch.py`:

- LeanFinder: “For a Noetherian local ring, the dimension of a closed subset
  intersecting V(I) only at the closed point is bounded by local cohomological
  dimension”. Eight hits on ordinary Krull/support-dimension inequalities; no match.
- Loogle: `localCohomology, topologicalKrullDim`. Zero hits.
- grep: `localCohomology|localCohomologicalDimension|idealPowerTorsion`.
  Five hits in Mathlib's LocalCohomology file, whose model is a colimit of Ext.
- LeanSearch: “local cohomological dimension of an ideal defined by vanishing of
  right derived ideal power torsion”. Eight hits including localCohomology and
  the finite-dimensionality instance for Noetherian local rings; no definition of cd.
- LeanFinder: “local cohomological dimension of an ideal supremum of degrees where
  right derived torsion is nonzero”. Eight support-dimension hits; no match.
- Loogle: `CategoryTheory.Functor.rightDerived`. Twelve hits supplying the general
  right-derived API; no dimension definition or intersection theorem.
- grep: `localCohomologicalDimension|cohomologicalDimension|idealPowerTorsion`.
  Zero Mathlib hits.

Direct `rg` searches in `WeilConjectures` and `lean/Sheaf` found the existing
ideal-power torsion functor and unrelated étale cohomological dimensions, but no
ideal local-cohomological dimension or isolated-intersection bound. Searches by
the item id and chosen declaration names in upstream sources and
`dag/lean_names_upstream.json` found no prior statement. DAG definition-node searches
for local cohomological dimension found no node; the finite-level-amplification hit
is unrelated. `tools/blueprint_refs.py search` for “local cohomological dimension”
and “cohomological dimension of an ideal” each returned zero blueprint nodes.
The ancestor command returned `lem-per-artin-gabber-affine-curve`.

Validation: both modules compiled separately through `scompile.py`. An initial
missing Abelian instance was fixed by importing ModuleCat.Abelian. An overlapping
Nontrivial binder was removed because IsLocalRing already contains it. Final
compilation of both modules was clean, with no warnings. The first dry run found
only that the new definition signature record must begin at `def` rather than
`noncomputable def`; the record was adjusted to the preflight signature format.

## New nodes

`def-per-local-cohomological-dimension` defines the local-cohomological dimension
of an ideal in a Noetherian ring, from the existing torsion functor. Its source is
Stacks Definition 0DX8 and the all-modules criterion 0DX7. Its three recorded search
kinds all ran; none gave the missing dimension. It cites the existing Noetherian-ring
and ideal-power-torsion nodes instead of duplicating either notion. The definition
is a literal supremum, with no sorry, and it is a new statement dependency of the
item. The inherited blueprint ancestor and route identify the dimension comparison
this definition serves.

## Second reading by N6

No second reading by a worker: this dispatched worker delivers directly under the
current brief; the maintainer's independent review reads the delivery. The worker
self-check above matches every hypothesis and both conclusions explicitly.
