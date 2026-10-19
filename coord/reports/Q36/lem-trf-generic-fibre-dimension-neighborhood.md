## Worker report

Repair of the stage-2 delivery returned at immutable head `44bd1ceea497` for H1.
The retained sandbox contained only dispatcher markers, with no module, node copy,
report, or citation packet. This repair supplies the missing statement module
`Sheaf.TraceFormula.GenericFibreDimensionNeighborhood` and the node's complete
`lean` record. The statement and all other node fields are unchanged from the
current shared node. The prescribed delivery wrapper rebases this packet onto
current `newtargets-dag`; no direct Git commands or live-source edits are used.

The sole declaration is
`AlgebraicGeometry.exists_nonempty_open_fibre_dimension_eq_of_generic_fibre_dimension_eq`.
Its proof is exactly `by sorry`. Its source and complete three-step mathematical
proof are in the declaration docstring; no definition or auxiliary theorem is added.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes and the morphism are `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  The universe `u` is explicit; all variables are bound explicitly.
- Finite type is `[LocallyOfFiniteType f] [QuasiCompact f]`, precisely the two
  conditions of `def-weil-finite-type-morphism`, with no finite-presentation,
  Noetherian, properness, reducedness, or flatness assumption.
- Irreducibility of the underlying space is `[IrreducibleSpace Y]`, whose
  definition includes nonemptiness and preirreducibility. This is the stated
  irreducibility assumption, also implied by the explicit generic-point condition.
- The generic point is `(η : Y)` with
  `(hη : IsGenericPoint η (Set.univ : Set Y))`, meaning exactly that the closure
  of the singleton is the entire base.
- The nonnegative integer dimension is `(n : ℕ)`; zero is included.
- The scheme-theoretic generic fibre is `f.fiber η`, Mathlib's actual pullback
  along `Y.fromSpecResidueField η`. The hypothesis is
  `(hηdim : topologicalKrullDim (f.fiber η) = (n : WithBot ℕ∞))`.
  The cast denotes the finite integer in the dimension domain that also contains
  negative infinity and infinity.
- The conclusion's subset is `∃ V : Set Y`; `IsOpen V` states openness and
  `V.Nonempty` states nonemptiness. There is no extra conclusion imposed on V.
- Every point of that subset is quantified by `∀ y ∈ V`; its fibre has dimension
  exactly n by `topologicalKrullDim (f.fiber y) = (n : WithBot ℕ∞)`.

Dependency records, full source signatures, and docstrings were read:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `AlgebraicGeometry.QuasiCompact`
  in `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-pc-scheme-fibre`: `AlgebraicGeometry.Scheme.Hom.fiber`, `fiberι`, and
  `fiberToSpecResidueField` in `Mathlib.AlgebraicGeometry.Fiber`. Only the fibre
  object is needed in the signature.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim` in
  `Mathlib.Topology.KrullDimension`, the Krull dimension of `IrreducibleCloseds`.
- `def-sc-generic-point`: `IsGenericPoint` in `Mathlib.Topology.Sober`.
  `Mathlib.Topology.Irreducible` provides `IrreducibleSpace`.

All stated proof dependencies are imported without `public`: the modules
`Sheaf.AlgebraicGeometry.LocalFibreDimensionOpen`,
`Sheaf.AlgebraicGeometry.GenericFibreClosedAvoidance`,
`Sheaf.AlgebraicGeometry.GenericClosedSubsetFibreNonempty`,
`WeilConjectures.Mathlib.Topology.KrullDimension`, and
`WeilConjectures.Topology.DimensionSupremumLocalDimensions`.
The last module's current source was read using `scompile.py --source`, since
its upstream location is newer than the local checkout. Their declarations
give the open bounded local-dimension locus, closed avoidance, closed-subset
nonemptiness spreading, local dimension, and its supremum formula, respectively.

Source checked directly: `literature/stacks-project/more-morphisms.tex`,
`lemma-dimension-in-neighbourhood`, lines 8411--8432 (Tag 05F7). Its statement
has exactly these geometric hypotheses and conclusion. The node explicitly
restricts to nonnegative integer n, and its proof separates n=0; this delivery
preserves that statement. The module docstring follows all three node steps.

Edge cases checked before writing: n=0 is allowed, and the empty generic fibre
has dimension bottom, so it cannot satisfy `hηdim` for any natural n. Thus no
extra nonemptiness hypothesis on the source or generic fibre is needed. An empty
base cannot supply η or its irreducibility instance. Empty special fibres cannot
satisfy the conclusion on V, as intended; the spreading argument removes them.
An irreducible nonreduced base is allowed. Fields of every characteristic are
allowed. Infinite dimension is excluded precisely by the node's finite n
hypothesis. V may be the whole base. No positivity assumption n>0 was introduced.

Searches made with `msearch.py Q36 lem-trf-generic-fibre-dimension-neighborhood`
(the commands' exact results are retained in `searches.jsonl`):

- `leanfinder`: “For a finite type morphism of schemes over an irreducible base,
  if the generic fibre has Krull dimension n, there is a nonempty open where every
  fibre has dimension n”. Eight hits: dominance, Jacobson fibres, openness,
  specializing/generalizing maps, and finite fibres; none states this theorem.
- `loogle`: `AlgebraicGeometry Scheme topologicalKrullDim fiber IsGenericPoint`.
  No hits; parser reported unknown identifier `AlgebraicGeometry`.
- `grep`: `generic.*fibre.*dimension|constant.*fibre.*dimension` in
  `AlgebraicGeometry`. Zero Mathlib hits.
- `leansearch`: “A finite type morphism over an irreducible scheme has constant
  fibre Krull dimension on a nonempty open subset”. Eight hits on finite fibres,
  proper/local finite type, dimension monotonicity, and integral restrictions;
  no exact match.
- `loogle`: `topologicalKrullDim`. Seven hits: the definition, homeomorphism
  invariance, subspace bounds, discrete topology, the spectrum comparison, and
  a locally Artinian criterion; none states constancy of fibre dimension.
- Direct `rg` over the upstream `WeilConjectures/`, shared `lean/Sheaf/`, and
  `dag/lean_names_upstream.json`, and the required upstream `grep -rn` for the
  node id, found no same-tag or same-name theorem. Broader dimension/fibre
  searches found finite-type upper bounds and flat local-dimension results,
  whose hypotheses and conclusions differ. Existing declarations are used for
  all notions; the theorem itself needs a new module.

The missing `citations.json` is now present: one entry for every node in each
proof step's `uses`, quoting that dependency's complete statement verbatim
(18 entries). This is local evidence; stage-2 delivery includes only the module,
node record, and report. There are no new nodes, dependency repairs, statement
corrections, or disputed statements.

Validation: the prescribed `scompile.py` compiled this file both as an isolated
sandbox statement and at its final module path, including all proof imports,
without errors or non-sorry warnings. `lean.statement` is copied verbatim from
the theorem keyword up to the assignment. Every line is at most 100 characters.

## Second reading by Q36

This is the author's fresh reading during the repair; the dispatcher brief
forbids starting another agent, so the maintainer supplies the independent
review. I reread the current node, source Tag 05F7, dependency definitions, and
the complete final module together. The morphism, finite-type pair, irreducible
underlying space, actual generic point, natural integer n, and equality for the
scheme-theoretic generic fibre each have the binders listed above. The output is
exactly an open nonempty subset with equality of Krull dimensions for every
point in it; it does not require additional geometric structures or exclude n=0.

H1 is repaired point by point: the previously absent Lean module is supplied;
the node now has a complete `lean` record with the exact signature and final
module path; this report has both required headings and the full clause audit;
and `citations.json` exists with verbatim quotations for every proof-step use.
The fresh reading also added all stated proof-dependency imports required by
stage 2 rule 7. No mathematical mismatch or missing dependency notion remained.
