## Worker report

The new module `Sheaf.AlgebraicGeometry.LocalFibreDimensionOpen` states
`AlgebraicGeometry.isOpen_localFibreDimension_le`, with its entire proof `sorry`.
No definitions or other theorems are introduced. The source was read at
`literature/stacks-project/morphisms.tex:5467–5485`, Tag 02FZ,
`lemma-openness-bounded-dimension-fibres`. It assumes exactly a morphism locally
of finite type and a nonnegative integer bound, and concludes openness of this locus.
The node needs no correction and no new or repaired dependency node.

Hypothesis and clause correspondence:

- Schemes X and S: `{X S : Scheme.{u}}`, with `universe u` explicitly declared.
  The arbitrary common universe is Mathlib's category of schemes; it does not impose
  a countability, cardinality, or dimension restriction.
- A scheme morphism f: `(f : X ⟶ S)`.
- Locally of finite type: `[LocallyOfFiniteType f]`. No properness, quasi-compactness,
  Noetherian, finite-presentation, or flatness assumptions occur.
- Every integer n ≥ 0: `(n : ℕ)`, with the bound embedded in `WithBot ℕ∞`.
  Nonnegative integers are exactly naturals, including zero.
- The fibre X_(f(x)) and its unique point over x: `f.asFiber x`, whose type is
  `f.fiber (f x)`. Its definition is `(f.fiberHomeo (f x)).symm ⟨x, rfl⟩`;
  `Scheme.Hom.fiberι_asFiber` verifies its projection is x, and the homeomorphism
  makes this point unique. No arbitrary choice or extra point is supplied.
- The minimum dimension of open fibre neighbourhoods: `topologicalKrullDimAt
  (f.asFiber x)`. Its definition is the infimum of `topologicalKrullDim U` over
  open neighbourhoods U; the well-ordered extended-natural codomain makes this
  the minimum in the node. This is dimension at a point, not local-ring dimension.
- The specified subset U_n: `{x : X | topologicalKrullDimAt (f.asFiber x) ≤
  (n : WithBot ℕ∞)}`.
- Openness in the source: `IsOpen` applied to that set.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` (lines 36–47)
  and `AlgebraicGeometry.Scheme.Hom` (73–75), for def-pc-scheme; also
  `AlgebraicGeometry.Spec` and `Spec.map` (469–480), for the proof's
  def-weil-affine-spectrum.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` (38–46), for
  def-weil-finite-type-morphism. It imposes finite type on affine coordinate maps.
- `Mathlib.AlgebraicGeometry.Fiber`: `AlgebraicGeometry.Scheme.Hom.fiber`,
  `fiberι`, `fiberToSpecResidueField`, `fiberHomeo`, and `asFiber`
  (37–46, 102–123), for def-pc-scheme-fibre. The fibre is the pullback along
  the canonical spectrum of the residue field, and fiberHomeo identifies its
  underlying space with the set-theoretic fibre.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`
  (341–344), for def-kun-topological-dimension-at-point; and
  `IsOpen.topologicalKrullDimAt_eq` (354–358), for
  lem-weil-pbc-dimension-at-point-open-subspace.
- `Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart.CoordinateFibreDimension`:
  `AlgebraicGeometry.affine_coordinate_fibre_dimension_eq`; its complete signature
  and docstring were read, including the induced coordinate algebra and prime.
  Imported without `public` for lem-sbc-affine-coordinate-fibre-dimension.
- `Sheaf.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs`:
  `Algebra.fibre_dimension_bounded_open_upstairs`; its complete signature and
  proof-plan docstring were read. It supplies a neighbourhood of a prime of a
  finite type algebra where the local fibre dimension is bounded by the dimension
  at the chosen prime. Imported without `public` for
  lem-weil-pbc-fibre-dimension-bounded-open-upstairs.

The module docstring gives the source and node. The theorem docstring follows
all four proof steps of the node: choose affine neighbourhoods with a finite type
coordinate map; compare restricted and coordinate fibres; apply the algebraic
bounded-dimension neighbourhood theorem with the local value d ≤ n; transport
that neighbourhood back and take the union. Statement dependencies are public
imports; additional proof dependencies are ordinary imports. No local notation,
instance, unbound variable, hidden let, or second copy of a notion is used.

Edge cases checked: n = 0 is included (the zero-dimensional local-fibre locus);
the empty scheme or empty locus gives the open empty set; an empty fibre contributes
no x, because the fibre over f(x) always contains asFiber x. Infinite local dimensions
are represented by the codomain and fail any finite bound, without imposing a
finiteness hypothesis in the statement. The theorem covers non-quasi-compact and
non-Noetherian schemes, arbitrary characteristics, and non-flat morphisms. For an
identity map every fibre is the spectrum of a field, so every point is in every U_n;
for affine space over a field the locus is empty below its dimension and all points
at or above it. These agree with the source and the inequality's direction.

Searches actually performed with `msearch.py NN lem-weil-pbc-local-fibre-dimension-open`:

- leanfinder: `For a locally finite type morphism of schemes the locus where the
  local dimension of the fibre at x is at most n is open`. Eight hits; they concern
  open maps, the definition LocallyOfFiniteType, open immersions, restrictions, and
  LocallyQuasiFinite. None states the desired locus theorem.
- loogle: `"LocallyOfFiniteType", "topologicalKrullDimAt"`. Zero hits.
- grep: `(fiber|asFiber).*topologicalKrullDimAt|topologicalKrullDimAt.*(fiber|asFiber)|02FZ`.
  Zero Mathlib hits.
- leansearch: `The set of points where a locally finite type scheme morphism has
  local fibre dimension at most n is open`. UNAVAILABLE, Internal Server Error;
  not treated as evidence of absence.

Direct source searches actually performed: rg for the item ID, for
`topologicalKrullDimAt.*asFiber`, and for openness/fibre-dimension names in
`WeilConjectures` and `lean/Sheaf`; then all `topologicalKrullDimAt` occurrences in
upstream `Mathlib/AlgebraicGeometry` and `isOpen.*[dD]im|[dD]im.*isOpen` in the
project's AlgebraicGeometry directory. Upstream has
`Smooth.isLocallyConstant_topologicalKrullDimAt_asFiber`, which requires smoothness
and is not this statement. Project hits are fibre comparisons, flat strata, and
Cohen–Macaulay loci, not the bounded local dimension locus. Searching
`dag/lean_names_upstream.json` for `topologicalKrullDimAt`, the item name words,
and 02FZ found no recorded declaration. The new declaration name was searched
in these source trees and is not already present.

Validation: server-only `scompile.py` and the delivery dry run are run for this
single module. The second reading is left to the independently dispatched reader.

## Second reading by NN

I independently read the node's statement and four proof steps, its source
morphisms.tex at Tag 02FZ (5467–5485), the chapter introduction and surrounding
fibre-dimension discussion, and the delivered Lean file. Tag 02FZ states this
exact openness result for locally finite type morphisms; no standing Noetherian,
flatness, separatedness, or finite-presentation hypothesis is imposed.

Object/hypothesis/conclusion checklist, matched against the Lean (H3):

- Schemes X and S: `{X S : Scheme.{u}}`. Exact. I opened Mathlib's
  `Scheme` and `Scheme.Hom`: locally ringed spaces locally affine and their
  morphisms. The arbitrary common universe is the ambient scheme category;
  it imposes no cardinality bound beyond choosing that category.
- Morphism f: `(f : X ⟶ S)`. Exact, without an extra base field.
- Locally of finite type: `[LocallyOfFiniteType f]`. Exact. I read its
  `finiteType_appLE` field in FiniteType.lean; its all-affine-pairs condition
  is the affine-local characterization of the node's cover condition.
  There are no additional geometric assumptions or instances.
- Scheme-theoretic fibre X_s: `f.fiber s`, used by `asFiber`. Exact.
  I read its definition `pullback f (S.fromSpecResidueField s)` and its
  projections `fiberι` and `fiberToSpecResidueField` in Fiber.lean.
- Unique point of X_(f(x)) over x: `f.asFiber x`. Exact. Its definition is
  `(f.fiberHomeo (f x)).symm ⟨x, rfl⟩`; the homeomorphism identifies the
  fibre with the set-theoretic fibre. `fiberι_asFiber` gives the projection
  x, and injectivity gives uniqueness. This does not assert the whole
  fibre is a singleton.
- Topological dimension at that point: `topologicalKrullDimAt (f.asFiber x)`.
  Exact. I opened the upstream definition in Topology/KrullDimension.lean:
  it is the infimum of `topologicalKrullDim U` over open neighbourhoods U.
  This nonempty family in the well-ordered extended naturals has a minimum,
  agreeing with the node; it is not local-ring dimension.
- Every integer n ≥ 0: `(n : ℕ)`, embedded as `(n : WithBot ℕ∞)`. Exact.
  Naturals represent exactly the nonnegative integer bounds, including zero.
- The entire conclusion: `IsOpen {x : X | topologicalKrullDimAt
  (f.asFiber x) ≤ (n : WithBot ℕ∞)}`. Exact locus and inequality in the
  topology of X. Quantification is over all schemes, f, and bounds n.

I opened the four statement-dependency nodes and their recorded declarations,
and also the proof-dependency nodes and actual declarations of `Spec`/`Spec.map`,
`IsOpen.topologicalKrullDimAt_eq`,
`AlgebraicGeometry.affine_coordinate_fibre_dimension_eq`, and
`Algebra.fibre_dimension_bounded_open_upstairs`. The latter two respectively
compare the specified affine fibre points and give the neighbourhood bound
for finite type algebras, with no Noetherian assumption. These declarations
supply the objects and proof steps claimed in the module. There are no new
nodes or dependency modules in this delivery (H12/H13); none is needed.
There is no statement correction, so no correction/citer verdicts are required.

Edge cases: n = 0 is included; empty X gives the empty open locus. A morphism
to empty S has empty domain. Empty fibres at other base points contribute
nothing, and the fibre over f(x) contains `asFiber x`. The zero ring gives
an empty spectrum, already covered. There is no index set or module here.
The dimension codomain represents infinity without an added finite-dimension
instance; an infinite value fails a finite bound. All characteristics and
arbitrary scheme universes are covered. Identity morphisms give all X for
every n. Affine space of dimension d over a field gives the empty locus for
n < d and all points for n ≥ d, checking the inequality direction.

Independent searches, with other queries than the first worker (H4):

- msearch.py leanfinder: `Upper semicontinuity on the domain of local
  dimensions of scheme fibres for a morphism locally of finite type`.
  Eight hits: general semicontinuity, LocallyQuasiFinite, LocallyOfFiniteType,
  and generalizing maps, not the requested theorem.
- msearch.py loogle: `"asFiber", "IsOpen"`. One hit,
  `Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber`, for openness of
  a singleton within one fibre, not this locus in the source.
- msearch.py grep:
  `(upperSemicontinuous|semicontinuous|isOpen).*([fF]ibre|[fF]iber|[dD]imension)`.
  Twenty-four Mathlib hits, concerning ordinary fibre openness,
  quasi-finiteness, and unrelated finite-dimensional open maps.
- Direct rg in Mathlib AlgebraicGeometry and project AlgebraicGeometry for
  `topologicalKrullDimAt|localFibreDimension|localFiberDimension|02FZ`,
  then whole-upstream rg for local dimension with `asFiber` and Tag 02FZ.
  The upstream smooth local-constancy theorem requires smoothness; the
  project contains affine comparisons and flat fibre strata. None gives
  this general theorem. The proposed declaration name is absent from
  dag/lean_names_upstream.json. No duplicate notion was introduced.

H5/H6/H8/H9: only the named theorem is introduced, its proof exactly `sorry`.
There is no definition, hollow data, local instance, private copy, hidden let,
or unbound variable/universe. The module and theorem docstrings cite Tag 02FZ
and the blueprint id. The theorem docstring covers all four proof steps with
their dependency nodes. Statement dependencies are public imports and the
additional proof dependencies are ordinary imports.

Mismatches found: none. I initially suspected escaped newlines in the metadata
from its displayed representation; a direct string comparison disproved that
suspicion. `lean.statement` is already verbatim equal to the file's signature.
No Lean or node fields were changed; this independent review was appended.
Server-only scompile.py passed cleanly: 1.3 s, nice 19, two threads, 60 s limit.
