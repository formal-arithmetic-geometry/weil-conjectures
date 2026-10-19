## Worker report

The module states openness of the locus where the scheme-theoretic fibre of a proper
morphism has topological Krull dimension at most a specified nonnegative integer.
Its only theorem is `AlgebraicGeometry.isOpen_setOf_topologicalKrullDim_fiber_le`,
with proof `sorry`; no definitions or proofs are introduced.

Hypotheses and clauses:
- Schemes X and S: `{X S : Scheme.{u}}`, with arbitrary explicitly bound universe `u`.
- Morphism f: `(f : X ⟶ S)`.
- Properness: `[IsProper f]`. Mathlib's separated, universally closed, locally finite
  type definition agrees with finite type here, since universal closedness implies
  quasi-compactness.
- Each integer d ≥ 0: `(d : ℕ)`, which ranges over precisely the nonnegative integers.
- The fibre over s: `f.fiber s`, the pullback along `S.fromSpecResidueField s`.
- Topological Krull dimension: `topologicalKrullDim (f.fiber s)` in `WithBot ℕ∞`.
- The bound: `≤ (d : WithBot ℕ∞)`.
- The specified subset is open: `IsOpen {s : S | ...}`.
- No Noetherian, flatness, nonemptiness, or finite presentation hypothesis is present.

Dependency declarations read and used:
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`
  (available through the public imports).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`;
  its parents `IsSeparated` and `UniversallyClosed` were also inspected.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, defined as the pullback
  of f along the residue-field point. Its projections and `fiberHomeo` were inspected.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, defined as the
  order Krull dimension of `IrreducibleCloseds`.
- Proof-only import `Sheaf.Topology.DimensionSupremumLocalDimensions`:
  `topologicalKrullDim_eq_iSup_topologicalKrullDimAt`.
- `def-weil-finite-type-morphism` is already available through the properness import.
  The proof dependency `lem-weil-pbc-local-fibre-dimension-open` has no Lean record,
  so no import is available for it. No dependency notion is duplicated.

Source checked: local `literature/stacks-project/more-morphisms.tex`,
`lemma-dimension-fibres-proper` (Tag 0D4I), statement and entire proof.
The node accurately expresses the stated consequence of upper semicontinuity.

Edge cases checked mathematically: for d = 0 the locus includes zero-dimensional
and empty fibres; an empty fibre has dimension bottom, hence satisfies every bound.
For empty X the locus is all S; for empty S it is the empty open set. Arbitrary
non-Noetherian bases are allowed. Infinite dimension fails each finite bound;
no coercion replaces bottom by zero. No nonempty assumption restricts these cases.

Searches for an existing statement (2026-10-15):
- msearch LeanFinder: "For a proper morphism of schemes the set of points where
  the fibre has Krull dimension at most d is open". Eight hits, concerning properness,
  open maps and quasi-finiteness, but no matching statement.
- msearch Loogle: `"IsProper", "topologicalKrullDim"`: zero hits.
- msearch grep: `(fiber|fibre).*(semicontinuous|Semicontinuous)|[Ii]sProper.*[Kk]rull`:
  zero hits.
- msearch LeanSearch: "Fibre dimension of a proper morphism is upper semicontinuous":
  UNAVAILABLE, service Internal Server Error; no verdict from this unavailable service.
- rg in upstream WeilConjectures and project lean/Sheaf for topologicalKrullDim,
  fibre/semicontinuity and openness/dimension combinations: local dimension and
  other fibre-dimension statements found, none this proper-fibre openness statement.
- rg for the exact node id in upstream WeilConjectures: no match.
- rg for the proposed declaration name in Mathlib, upstream, project and
  dag/lean_names_upstream.json: no match.

No new nodes, dependency modules, statement corrections, or disputed statements.

## Second reading by NW

I independently read the node, its four statement dependency records and their
actual declarations, the module, and Stacks More on Morphisms,
lemma-dimension-fibres-proper (Tag 0D4I), including its proof. The surrounding
Dimension of fibres section imposes no standing Noetherian or flatness assumption.
The preceding lemma-base-change-dimension-fibres introduces the fibre-dimension
function for finite type morphisms; properness supplies finite type. Its displayed
codomain omits negative infinity, but for the nonnegative thresholds in this node
this does not affect the locus; the node explicitly retains empty dimension bottom.

Object, hypothesis and conclusion checklist, in the node's order:

- Schemes X and S: `{X S : Scheme.{u}}`. PASS. I read `Scheme` and `Scheme.Hom`
  in Mathlib.AlgebraicGeometry.Scheme: locally ringed spaces locally isomorphic to
  affine spectra, with their locally ringed space morphisms.
- A morphism f from X to S: `(f : X ⟶ S)`. PASS; no structure morphism or base
  field is substituted for the arbitrary scheme morphism in the node.
- Properness of f: `[IsProper f]`. PASS. The actual class extends `IsSeparated f`,
  `UniversallyClosed f`, and `LocallyOfFiniteType f`. I read the separated diagonal
  condition and universally closed condition, and the latter's `QuasiCompact f`
  instance. Consequently this is precisely separated, finite type and universally
  closed, as def-weil-proper-morphism requires, without an extra hypothesis.
- Each integer d >= 0: `(d : ℕ)` after f and its properness instance. PASS;
  nonnegative integers are exactly the natural thresholds, with no positivity bound.
- Each point s of the base: `s : S` in the set comprehension. PASS; all base points
  are included, without a rationality or closed-point restriction.
- Scheme-theoretic fibre X_s: `f.fiber s`. PASS. I opened Mathlib's `Scheme.Hom.fiber`,
  which is `pullback f (S.fromSpecResidueField s)`, its two projections and
  `fiberHomeo`; this is exactly def-pc-scheme-fibre, including its underlying space.
- Dimension of that fibre: `topologicalKrullDim (f.fiber s)`. PASS. Its actual
  definition is `Order.krullDim (IrreducibleCloseds _)`, valued in `WithBot ℕ∞`:
  chains of nonempty irreducible closed subsets, with bottom for the empty space.
  This is def-kun-topological-krull-dimension, not local dimension or cohomology rank.
- Bound and topology: `≤ (d : WithBot ℕ∞)` inside
  `IsOpen {s : S | topologicalKrullDim (f.fiber s) ≤ (d : WithBot ℕ∞)}`. PASS;
  this asserts precisely openness of the specified sublevel set in S.
- Explicit absence of Noetherianity and flatness: there are no such binders or
  instances, nor finite presentation, characteristic, nonemptiness or field
  assumptions. PASS.

Edge cases: d = 0 includes both zero-dimensional and empty fibres. Empty X gives
all of S, and empty S gives the empty open set. Bottom remains strictly below zero
in `WithBot ℕ∞`; no conversion to naturals loses the empty-fibre convention.
The statement is characteristic independent. Universe u is explicitly bound and
arbitrary, following Mathlib's category of schemes and its morphisms; this is not
an independently small test-object universe, and no quantified test family is
restricted. There is no index set or module zero object in this statement.

I also opened the proof dependency
`topologicalKrullDim_eq_iSup_topologicalKrullDimAt` in
Sheaf.Topology.DimensionSupremumLocalDimensions: its signature is for every
`X : Type u` with a topology, with no finiteness/nonemptiness restriction, exactly
the node's supremum identity. It is correctly a non-public proof import. The local
fibre-dimension openness node has no Lean record and hence no module to import.
All usable recorded statement dependencies are public Mathlib imports. There are
no new nodes or dependency modules to audit under H12/H13, and no correction or
citer verdicts to audit under step 4c.

Independent duplicate searches:

- msearch LeanFinder: "Upper semicontinuity of dimensions of fibers for proper
  scheme maps": eight hits about properness, closed maps and quasi-finiteness;
  none states this dimension locus.
- msearch Loogle: `"IsOpen", "fiber", "topologicalKrullDim"`: zero hits.
- msearch LeanSearch: "Proper morphism of schemes has upper semicontinuous fiber
  Krull dimension": service unavailable (Internal Server Error), no verdict.
- Direct rg in upstream WeilConjectures, project lean/Sheaf and Mathlib algebraic
  geometry, using `semicontinu`, fibre/dimension in both orders, and
  `topologicalKrullDim.*fiber|fiber.*topologicalKrullDim`: hits concern generic
  fibre dimension, relative dimension and fibre cohomology semicontinuity, not
  openness of the Krull-dimension sublevel sets for arbitrary proper morphisms.
- Exact declaration name and blueprint id searched in upstream WeilConjectures,
  the upstream-name inventory and project lean/Sheaf: no existing declaration.

No mismatch was found, and no Lean or node content was changed. The module has
no definitions, private copies, local notation, local instances or proved lemmas;
its single proof is `sorry`. Its module and theorem docstrings name Tag 0D4I and
the blueprint id. The theorem docstring follows all four node proof steps: local
openness, closed image, the supremum identity including empty fibres, and taking
the complement. No line exceeds 100 characters. Every variable and universe is
bound, and `lean.statement` is verbatim equal to the file's theorem signature.

Verification: scompile.py compiled the delivered file on the server cleanly in
1.2 seconds, nice 19, two threads, with the 60-second per-file limit. No errors or
warnings were printed.
