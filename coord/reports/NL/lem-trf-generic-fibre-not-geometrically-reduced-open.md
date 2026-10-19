## Worker report

The module `Sheaf.AlgebraicGeometry.GenericFibreNotGeometricallyReducedOpen` states
`AlgebraicGeometry.exists_nonempty_open_not_geometricallyReduced_fiber_of_generic`, exactly Stacks Tag 0577,
`more-morphisms.tex`, lemma-not-geometrically-reduced-in-neighbourhood (local lines 7180–7212).
Its only proof is `sorry`; it introduces no definition. The node is unchanged except for `lean`.
No maintenance repair note exists for this item.

Clause-by-clause correspondence:

- Schemes and morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the conjunction specified
  by def-weil-finite-type-morphism (Mathlib does not bundle a finite-type morphism class).
- Irreducible Y: `[IrreducibleSpace Y]`, which includes nonemptiness and preirreducibility.
- Specified generic point: `(η : Y) (hη : IsGenericPoint η Set.univ)`, i.e. closure {η} = Y.
- Generic fibre not geometrically reduced over κ(η):
  `(hred : ¬ GeometricallyReduced (f.fiberToSpecResidueField η))`.
  This is geometric reducedness of the canonical projection of the scheme-theoretic fibre
  to `Spec (Y.residueField η)`, not reducedness of the original morphism or total space.
- Existence of an open subset V of Y: `∃ V : Y.Opens`.
- Nonempty V: `(V : Set Y).Nonempty`.
- Every fibre above V fails geometric reducedness over its own residue field:
  `∀ y : Y, y ∈ V → ¬ GeometricallyReduced (f.fiberToSpecResidueField y)`.
- The node's final sentence is respected by the absence of flatness, reduced-base,
  Noetherianity, or fibre-nonemptiness assumptions. The universe u is explicitly bound;
  there are no extra field/test-object universes, local notation, or hidden structure maps.

Dependency declarations read in full (including their docstrings) and used:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`.
- def-weil-finite-type-morphism: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`; the imported
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- def-weil-irreducible-components: `Mathlib.Topology.Irreducible`,
  `IsIrreducible`, `irreducibleComponents`, and its whole-space form `IrreducibleSpace`.
  This is the recorded notion, not a new predicate.
- def-sc-generic-point: `Mathlib.Topology.Sober`, `IsGenericPoint`.
- def-pc-scheme-fibre: `Mathlib.AlgebraicGeometry.Fiber`, `Scheme.Hom.fiber` and
  `Scheme.Hom.fiberToSpecResidueField`; the latter is the second pullback projection.
- def-weil-residue-field: `Mathlib.AlgebraicGeometry.ResidueField`, `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.fromSpecResidueField`.
- def-pc-geometrically-irreducible: its recorded module
  `Mathlib.AlgebraicGeometry.Geometrically.Integral` imports the recorded
  `AlgebraicGeometry.GeometricallyReduced` class from
  `Mathlib.AlgebraicGeometry.Geometrically.Reduced`. Read the latter definition and
  `geometrically_iff_of_commRing` in `Mathlib.AlgebraicGeometry.Geometrically.Basic`:
  on a map to Spec κ(y), this is precisely reducedness after every field extension.

Proof dependency imports (ordinary imports, not public):
`Sheaf.AlgebraicGeometry.GenericGeometricallyReducedPreparation`,
`Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange`,
`Sheaf.AlgebraicGeometry.GeometricallyReducedAlgebraicClosureTest`,
`Sheaf.AlgebraicGeometry.ReductionGenericFibre`. The other Mathlib proof dependencies
are already exposed through the statement imports or these proof imports. The existing DAG
node lem-trf-nonreduced-fibre-open has no recorded Lean declaration or Mathlib match at this
reading, so its proof import is omitted; its use remains explicit in the theorem's proof
plan for stage 3. It supplies no notion needed to type this statement.

The docstring gives all five node proof steps: preparation over a finite universal
homeomorphism; comparison of generic geometric reducedness; the reduction contradiction;
ordinary nonreduced spreading; and transport of the nonempty open and the fibre comparison.
The Stacks proof and source statement were read directly from the local source.

Edge cases checked mathematically before drafting:

- Empty X or empty generic fibre: an empty scheme remains empty and reduced after any
  field extension, so the negative generic-fibre hypothesis cannot hold. No artificial
  nonemptiness assumption is needed. Empty special fibres are excluded on the resulting V
  by its asserted negative geometric reducedness, rather than by an extra hypothesis.
- Empty Y is already excluded by irreducibility and by the supplied generic point.
- A one-point irreducible base: take the entire base as the open; no dimension bound is used.
- Nonreduced irreducible bases are permitted: e.g. a dual-number base and a finite family
  with a square-zero variable retain the intended generic-fibre interpretation over κ(η).
- Imperfect fields: a nontrivial finite purely inseparable field extension gives a reduced
  but non-geometrically reduced scheme over the base field. The hypothesis uses geometric
  reducedness of the fibre map, so it includes this essential case.
- Families with reduced generic fibre and nonreduced special fibre (e.g.
  k[t,x]/(x²,tx) over k[t]) do not satisfy the hypothesis and impose no false conclusion.
- Positive and zero characteristic, nonflat families, and non-Noetherian bases are not
  restricted. All schemes are in arbitrary explicitly declared universe u, as in Mathlib's
  category of schemes and its geometric-property definitions.

Searches performed using the authorized msearch.py wrapper:

- LeanFinder: "For a finite type morphism over an irreducible scheme a non geometrically
  reduced generic fibre implies non geometrically reduced fibres on a nonempty open".
  Eight hits, including Algebra.IsGeometricallyReduced, AlgebraicGeometry.IsReduced,
  Algebra.isGeometricallyReduced_iff, and integral/reduced implications; no spreading theorem.
- Loogle: `AlgebraicGeometry.GeometricallyReduced`. Twelve hits: the definition,
  base-change instances, fibre instances and reducedness under flatness; no matching theorem.
- grep: `not.*geometrically.reduced|nonreduced.*generic|GeometricallyReduced` in
  Mathlib/AlgebraicGeometry. Fourteen hits, primarily geometric reducedness and integrality
  definitions, plus smooth group/affine-space results; no matching theorem.
- LeanSearch: "Non geometrically reduced generic fibre spreads to an open subset of the
  base". Eight hits on reduced schemes, open covers and algebraic geometric reducedness;
  no spreading theorem.
- Direct rg in slopmaster2/WeilConjectures and the shared lean/Sheaf for
  `GeometricallyReduced|geometricallyReduced|not.*geometrically.reduced` and for
  `non.*[Gg]eometrically|not.*[Gg]eometrically|[Gg]eneric.*[Rr]educed|[Rr]educed.*[Gg]eneric`.
  Read the relevant geometric-reducedness extension and existing fibre-locus and generic
  preparation modules. They provide notions and other statements, not Tag 0577 itself.
- Direct rg for the exact item id in slopmaster2/WeilConjectures found no occurrence.
  Direct rg for the proposed declaration/module names in Mathlib, upstream sources,
  lean/Sheaf and dag/lean_names_upstream.json found no collision.

No disputed statement, node correction, new node, or dependency repair is necessary.

## Second reading by NL

The dispatcher explicitly forbids starting another agent and assigns independent review to
its maintainer. This section records the author's second pass, not an independent-worker
approval. Reopened the node and completed module and matched the binders and conclusion:
finite type uses both required classes; irreducibility is on Y; η is a point of Y with
closure equal to univ; the negative hypothesis and every negative conclusion apply to the
canonical κ(point)-structure map of the fibre. The witness is an open of the original Y,
its nonemptiness is explicit, and the final quantifier covers exactly its points.
There is no integral/reduced/affine-base hypothesis, no characteristic restriction, and no
assumption of nonempty fibres. No mismatch was found and no statement change was made.
The five-step proof docstring was checked against the five proof records and Stacks 0577.
Independent review remains the maintainer's delivery review, as specified in this brief.

Additional searches in the resumed turn: Loogle
`AlgebraicGeometry.GeometricallyReduced, IsGenericPoint` returned zero hits.
LeanFinder for "A non geometrically reduced generic fibre for a finite type scheme
morphism over an irreducible base spreads to a nonempty open" returned eight hits
on dominance, geometric reducedness, generic points and fibres, none matching this statement.
LeanSearch for "Non geometrically reduced generic fibre spreads to a nonempty open of
an irreducible base for a finite type scheme morphism" returned eight hits on reducedness,
spreading stalk maps and integral opens, none matching Tag 0577.
