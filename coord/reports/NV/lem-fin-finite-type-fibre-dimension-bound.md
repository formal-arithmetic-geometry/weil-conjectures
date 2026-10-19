## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound` states
`AlgebraicGeometry.exists_fibre_dimension_bound`, with its entire proof `sorry`.
It follows Stacks Project, Morphisms, Tag 0A3V,
`lemma-morphism-finite-type-bounded-dimension`; the source and preceding openness
lemma were read directly in `literature/stacks-project/morphisms.tex:5470–5510`.
The docstring includes all four steps of the node's proof and their dependencies.
No definitions, new nodes, dependency repairs, or statement corrections are needed.

Hypothesis and clause correspondence:

- Schemes X and Y and a morphism f: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  The explicitly bound universe u is arbitrary; there are no implicit universes
  or undeclared variables. Schemes and their morphisms use Mathlib's category.
- Finite type f: `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the conjunction
  in the dependency's record. No separatedness, Noetherian, field-base, flatness,
  or surjectivity condition is imposed.
- Quasi-compact Y: `[CompactSpace Y]`, on its underlying topological space,
  without a Hausdorff assumption.
- There exists a nonnegative integer d: `∃ d : ℕ`. Nonnegative integers and
  natural numbers are equivalent here; there is no bound on d.
- Every point y: `∀ y : Y`, after the existential, making d uniform over Y.
- Scheme-theoretic fibre X_y: `f.fiber y`, the recorded pullback along the
  canonical spectrum-of-residue-field morphism, rather than an arbitrary fibre.
- Topological Krull dimension at most d:
  `topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)`.
  The dimension retains both bottom and infinity. In particular empty fibres
  have dimension bottom (minus infinity); no nonempty-fibre restriction occurs.

Statement dependency declarations read at their recorded source locations:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (lines 42–47 and 73–75).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` (class and full field, lines 38–46).
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact` (class and full field, lines 38–46).
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (lines 279–285).
- `Mathlib.AlgebraicGeometry.Fiber`: `AlgebraicGeometry.Scheme.Hom.fiber`,
  `fiberι`, and `fiberToSpecResidueField` (lines 37–49).
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim` (lines 35–40),
  exactly `Order.krullDim (IrreducibleCloseds T) : WithBot ℕ∞`.

The module publicly imports these statement dependencies. Its ordinary imports
also cover every recorded proof dependency: the upstream finite-type dimension
lemma and local dimension definitions/open invariance; the landed affine-coordinate
comparison, algebraic bounded-open lemma and supremum-of-local-dimensions theorem;
and Mathlib quasi-compact preimages, affine pullbacks, open restrictions, affine
quasi-compact/quasi-separated instances, and categorical pullbacks. Proof-only
imports remain ordinary imports even though the proof is `sorry`, as required.

Edge cases checked mathematically: empty Y makes the universal conclusion vacuous
and allows d = 0; empty X makes every fibre empty and also allows d = 0; a morphism
with some empty fibres retains the same bound because bottom ≤ d; d = 0 allows
zero-dimensional or empty fibres. Arbitrarily positive finite relative dimensions
are allowed. The conclusion excludes an infinite-dimensional fibre, as the source
requires. Nonreduced, nonseparated and non-Noetherian schemes are included.
The compact-target assumption is meaningful: over a disjoint union of infinitely
many field spectra, affine spaces of unbounded dimensions give a finite-type
morphism without a uniform bound when the target is not quasi-compact.

Searches performed through `/home/ubuntu/weil-launcher-nt/msearch.py`, with search
logs in this sandbox's `searches.jsonl`:

- LeanFinder: “A finite type morphism of schemes over a quasi compact target has
  a uniform finite bound on dimensions of all fibres”. Eight hits, including
  `LocallyQuasiFinite`, compactness of fibres and finiteness of finite-morphism
  fibres; none gives a dimension bound for general finite-type morphisms.
- Loogle: `AlgebraicGeometry.Scheme, topologicalKrullDim`. One hit,
  `AlgebraicGeometry.IsLocallyArtinian.of_topologicalKrullDim_le_zero`, unrelated
  to uniform bounds.
- Mathlib grep: `dimension.*fib|fib.*dimension|topologicalKrullDim`, within
  `AlgebraicGeometry`. Six hits (elliptic-curve documentation and Artinian
  criteria), none matching.
- LeanSearch: “finite type morphism with quasi compact target admits a uniform
  finite bound on fibre Krull dimensions”. Service unavailable (Internal Server
  Error); no result or mathematical verdict from that service.
- Direct rg of the upstream project and `lean/Sheaf` for fibre/dimension/bound
  names and uniform fibre-dimension prose. Inspected the upstream
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType` module:
  `exists_topologicalKrullDim_le` only handles a scheme over a field, not a
  uniform bound over arbitrary target points. LowerStar modules only mention
  uniform fibre dimensions in finiteness documentation; no matching declaration.
- Direct rg for `lem-fin-finite-type-fibre-dimension-bound` in the upstream
  project and `dag/lean_names_upstream.json`: no matching declaration.
- Direct rg for `exists_fibre_dimension_bound|exists_fiber_dimension_bound` in
  Mathlib, upstream and `lean/Sheaf`: no collision.

No statement dispute or node fault was found. All writes are confined to the
assigned sandbox. Compilation is performed only by `scompile.py` on the server.

## Second reading by NV

I independently read the sandbox node and module against Stacks Morphisms,
Tag 0A3V, `lemma-morphism-finite-type-bounded-dimension`, and the immediately
preceding Tag 02FZ openness lemma in morphisms.tex. The source assumes only a
finite-type morphism and a quasi-compact target here; there is no standing
Noetherian, separation, flatness, characteristic or field-base hypothesis.

Object/hypothesis/conclusion checklist (all verdicts: exact):

- Schemes X and Y: `{X Y : Scheme.{u}}`. I opened the recorded
  `def-pc-scheme` declaration in Mathlib.AlgebraicGeometry.Scheme: Scheme is a
  locally ringed space with local affine charts, and Scheme.Hom is its locally
  ringed-space morphism. These are the node's schemes and morphisms.
- The specified map f: `(f : X ⟶ Y)`, with no additional structure on f.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`. I read the
  `def-weil-finite-type-morphism` node and both recorded Mathlib classes.
  The first imposes finite generation on affine coordinate maps; the second
  says inverse images of compact opens are compact. Their conjunction is the
  node's finite-type condition. Neither finite presentation nor Noetherianity
  has been substituted.
- Quasi-compact target: `[CompactSpace Y]`. I opened the recorded CompactSpace
  definition in Mathlib.Topology.Defs.Filter: it asks only IsCompact univ, with
  no Hausdorff condition, exactly `def-weil-pbc-quasi-compact-scheme`.
- A nonnegative integer bound: `∃ d : ℕ`, equivalent to an integer d ≥ 0.
  It precedes the quantification over y, so there is one uniform bound.
- Every target point: `∀ y : Y`, including points with empty inverse image.
- The scheme-theoretic fibre: `f.fiber y`. I opened the
  `def-pc-scheme-fibre` record and Mathlib.AlgebraicGeometry.Fiber: this is
  `pullback f (Y.fromSpecResidueField y)`, with the recorded projections to X
  and Spec κ(y); it is not a geometric fibre or a reduced fibre.
- Topological Krull dimension at most d:
  `topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)`. I opened the
  `def-kun-topological-krull-dimension` record and Mathlib definition: it is
  Order.krullDim of IrreducibleCloseds, retaining bottom and infinity.
  This is precisely the chain dimension in the node.
- Empty-fibre clause: the same inequality includes dimension bottom = minus
  infinity; no Nonempty instance, surjectivity assumption or dimension-to-Nat
  truncation occurs.

Edge cases: empty Y gives a vacuous universal conclusion (d = 0 works);
empty X, including Spec of the zero ring, has only empty fibres (d = 0 works).
Some fibres may be empty and others positive dimensional. At d = 0 the
inequality includes both zero-dimensional and empty fibres. Infinite dimension
cannot satisfy the bound. There is no index-set hypothesis or characteristic
restriction. The bound universe u is explicit and arbitrary; X and Y live in
Mathlib's same scheme category, so no extra universe restriction is imposed on
its morphisms. No variables or universes are left unbound.

Independent duplicate searches used different phrasing from the worker:

- msearch LeanFinder: "The Krull dimensions of fibres of a quasi compact locally
  finite type map to a compact scheme are bounded by one natural number".
  Eight hits concern compactness of fibres, quasi-compact morphisms and
  locally quasi-finite morphisms; none states this uniform dimension bound.
- msearch Loogle: `topologicalKrullDim, AlgebraicGeometry.Scheme.Hom.fiber`:
  zero hits. The worker's LeanSearch service failure remains documented above.
- Direct rg in Mathlib AlgebraicGeometry, the upstream WeilConjectures tree and
  this project's lean/Sheaf, using uniform/bound and both fiber/fibre spellings,
  dimension and existential names. Also checked the upstream-name JSON for the
  item and proposed declaration name. No exact statement or name collision.
  I opened upstream `exists_topologicalKrullDim_le`: its base is Spec of a
  field, so it supplies a bound for a single finite-type field-scheme, not a
  uniform bound over all points of an arbitrary target. The project's
  `exists_fiber_dimension_nat` is local at one point of affine schemes and
  assumes finite presentation. `exists_away_fibre_dimension_le` concerns a
  localized algebra near a prescribed prime. Neither is this node. Upstream
  Proper.lean mentions bounded fibre dimension only in a base-change docstring.

I also opened all three project proof-dependency modules (coordinate fibre
comparison, bounded-open-upstairs, and supremum of local dimensions), and the
upstream local-dimension and open-invariance declarations. They supply the
notions used in the four-step proof docstring. All recorded statement
 dependencies are usable as recorded; there are no new definition nodes or
 dependency modules in this delivery. No statement correction was necessary,
so no correction/citer review is applicable. No mismatch was found and no Lean
or node content was changed. The only addition is this independent review.

H5/H6/H8/H9: no new definitions, no hollow data, and exactly one theorem whose
entire proof is sorry. Both docstrings name Tag 0A3V and the blueprint node;
the theorem docstring follows all four node proof steps and their dependencies.
Statement imports are public; stated proof dependencies are ordinary imports.
All lines are at most 100 characters. The node's lean.statement was checked
verbatim against the theorem signature.

Validation: server scompile.py compiled the delivered module cleanly in 1.3 s,
nice 19, two threads, with the 60-second per-file limit. No compiler warnings
or errors. An initial invocation from the repository with a sandbox-relative
path failed before compilation; the absolute sandbox path above compiled.
