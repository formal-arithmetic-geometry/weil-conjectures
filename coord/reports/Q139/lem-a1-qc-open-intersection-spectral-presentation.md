## Worker report

The module `Sheaf.AlgebraicGeometry.QcOpenIntersectionSpectralPresentation` states the entire
node, using two named theorems for its directed-family and arbitrary-family clauses. Both
proofs are `sorry`. Four helpers construct the actual index, diagram, cone and finite
intersections; none has postponed data or an arbitrarily chosen map. The node's statement,
statement dependencies, proof, and proof dependencies are unchanged.

Hypothesis and clause correspondence:

- The scheme is `X : Scheme.{u}`. Its quasi-separatedness is `[QuasiSeparatedSpace X]`,
  equivalent to the absolute morphism definition by
  `AlgebraicGeometry.quasiSeparatedSpace_iff_quasiSeparated`. There is no assumption that X
  is quasi-compact, separated, affine, inhabited or nonempty.
- A nonempty indexing set is `{I : Type v} [Nonempty I]`; the independent universe v allows
  repeated members indexed by any set. `U : I → X.Opens` gives open subsets and
  `hU : ∀ i, IsCompact (U i : Set X)` gives exactly quasi-compactness.
- `hdir : ∀ i j, ∃ k, U k ≤ U i ⊓ U j` is exactly the directedness hypothesis.
  The chosen member is arbitrary, `(i₀ : I)`, and Y is literally `U i₀`.
- `qcOpenIntersectionIndex U i₀` is
  `OrderDual {V : X.Opens // V ∈ Set.range U ∧ V ≤ U i₀}`. Extensional opens identify
  repetitions; the inherited `PartialOrder` is reverse inclusion. Its underlying type lives
  in universe u even if the original indexing set is larger. The first four conclusion
  conjuncts assert `Small.{u}`, `Nonempty`, `IsDirected` and `IsLeast Set.univ` of the member
  whose underlying open is Y. No order is chosen existentially.
- `∀ i, ∃ V, V.val ≤ U i` asserts cofinality. The following equality of set intersections
  gives exactly E as the intersection over J.
- For every V, `QuasiSeparatedSpace V.val.toScheme ∧ SpectralSpace V.val.toScheme`
  uses the actual open subscheme, with its usual subspace topology and structure sheaf.
  In particular spectrality supplies its quasi-compactness.
- `qcOpenIntersectionDiagram` is a functor on `Jᵒᵖ`. A morphism V → W there is the inclusion
  of the underlying open of V into that of W, since J itself has reverse inclusion order.
  Its maps are Mathlib's `Opens.toTopCat` inclusions. `IsSpectralMap` asserts continuity
  and compactness of inverse images of compact opens, exactly the specified meaning.
- `qcOpenIntersectionCone` has point `TopCat.of {x : X // ∀ i, x ∈ U i}`, with its actual
  subtype topology. Every projection sends x to the same underlying x in the target open.
  `Nonempty (IsLimit ...)` asserts the full topological universal property for this cone.
- The next conjunct separately spells out compatible tuples: every compatible dependent
  family t has a unique point x in the intersection with every projection equal to t.
- The last conjunct identifies the subtype topology with the infimum of the topologies
  induced by the projections. Mathlib orders topologies in the reverse direction to their
  collections of opens, so this is precisely the coarsest topology making the projections
  continuous. No arbitrary homeomorphism or unconstrained projections are substituted.
- `qcFiniteOpenIntersection_refinement` has just the arbitrary-family assumptions, without
  `hdir` or i₀. `qcFiniteOpenIntersection U F` is the actual finite infimum
  `F.val.inf' F.property U`, indexed by `{F : Finset I // F.Nonempty}`. Its conclusion states
  nonemptiness of the indexing family, quasi-compactness of every resulting open,
  directedness by reverse inclusion, equality of total intersections, and occurrence of
  each original member. Openness is built into the codomain `X.Opens`. The resulting
  finite intersection is allowed to be the empty open.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its `Hom`, and `Scheme.Opens`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `AlgebraicGeometry.QuasiSeparated`
  and `quasiSeparatedSpace_iff_quasiSeparated`, for the recorded scheme notion.
- `Mathlib.Topology.Spectral.Basic`: `SpectralSpace`, exactly the recorded spectral-space
  notion (T0, compact, quasi-sober, quasi-separated and prespectral).
- Proof imports expose the finite-affine-cover theorem
  `AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens`, both affine-cover
  criterion clauses `quasiSeparatedSpace_iff_forall_affineOpens` and
  `Scheme.quasiSeparatedSpace_of_isOpenCover`, and the scheme topology instances in
  `Mathlib.AlgebraicGeometry.Properties` used with the `SpectralSpace` constructor.
- `Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection`:
  `AlgebraicGeometry.compactSpace_inter_of_quasiSeparated`, the recorded proof dependency.
  Its full signature and proof docstring were read; the equivalent upstream theorem
  `Scheme.isCompact_inf_of_quasiSeparatedSpace` was also inspected. No replacement or
  dependency record repair is needed.
- `Mathlib.Topology.Spectral.Hom`: `IsSpectralMap`.
  `Mathlib.Topology.Category.TopCat.Opens`: `Opens.toTopCat`.
  Mathlib's `Cone`, `IsLimit`, `OrderDual`, subtype order, and `Finset.inf'` give the remaining
  standard constructions. The helpers are constructions for this node, not new notions.

Sources read: the paragraph and equation `equation-sections-of-intersection` in
`literature/stacks-project/more-groupoids.tex` (lines 2967–2993), and
`lemma-make-spectral-space` in `literature/stacks-project/topology.tex` (lines 5005–5065).
The latter states the topological limit and explains finite-intersection refinement.

Edge cases checked mathematically before writing:

- Empty X: every open and E may be empty, while J still contains Y. No point is chosen.
- A member equal to the empty open: J and its limit still make sense; a compatible tuple
  or cone from a nonempty space cannot supply a point of that member. The universal property
  remains valid for the empty intersection.
- Singleton and constant/repeated families: J has one element when all opens coincide;
  E is that open. The subtype index identifies all repetitions.
- Two disjoint compact opens in Spec(k × k): the finite intersection indexed by both indices
  is retained as an empty open, supplying the directed common refinement. Discarding it
  would be incorrect. Nonempty finite index sets do not require nonempty open values.
- Infinite arbitrary families: only finite nonempty subsets index refinement; no compactness
  is asserted for the possibly non-quasi-compact ambient X or arbitrary infinite open
  intersections as open subschemes. E has only a topological subspace structure.
- Universe v of I is unrestricted; all distinct opens index a genuinely small type in u.

Searches actually run:

- `msearch.py`, leanfinder: “A directed family of quasi compact open subsets of a quasi
  separated scheme has its intersection as the topological inverse limit of the cofinal
  spectral inclusion diagram”. Eight hits, including affine-transition scheme limits and
  `Scheme.exists_isQuasiAffine_of_isLimit`; none states this topological cofinal presentation.
- `msearch.py`, loogle: `SpectralSpace, QuasiSeparatedSpace`. Two hits,
  `SpectralSpace.toQuasiSeparatedSpace` and `SpectralSpace.mk`; these are components only.
- `msearch.py`, grep, Topology:
  `(iInter|[Ii]ntersection).*(limit|Limit|[Ss]pectral)|([Ss]pectral|[Ll]imit).*(iInter|[Ii]ntersection)`.
  Eight hits on sheaf-condition pairwise intersections/equalizers; no exact match.
- `msearch.py`, leansearch: “The intersection of a directed family of compact open subsets
  is the inverse limit of the inclusion diagram of spectral spaces”. Eight hits including
  compact closed intersection nonemptiness, `CompHaus.limitCone`, and spectral constructor
  facts; none states the node.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for the node id and
  `intersection.*[Ll]imit|[Ll]imit.*intersection` found related scheme-limit and sheaf-section
  results. `IntersectionStructureSections` is the consumer of this presentation, not a
  duplicate. The precise helper names were searched in both source trees, Mathlib and
  `dag/lean_names_upstream.json`; no collisions occurred.

No statement correction, disputed statement, new node or dependency module is necessary.

## Second reading by Q139

The dispatcher explicitly forbids starting another agent. This is a direct worker delivery;
the maintainer's independent review is the independent reading. I re-read the node against
all conclusion conjuncts above. The finite-refinement theorem deliberately has no directedness
assumption; the cone projections and topology are canonical rather than existentially chosen.
The definition fixes the reverse-inclusion order before taking the opposite for the diagram.
The only drafting repairs were elaboration annotations in the concrete cone and parentheses
around a functor object in the topology expression; neither changes a mathematical clause.

Validation: `scompile.py Q139 lem-a1-qc-open-intersection-spectral-presentation` compiled
both its sandbox probe and its actual library module cleanly, with `autoImplicit false`.
Only the two named stage-2 theorem proofs are postponed. Source checks also included
Properties `lemma-quasi-compact-quasi-separated-spectral` and Schemes
`lemma-characterize-quasi-separated`, matching the proof dependencies' Mathlib signatures.
