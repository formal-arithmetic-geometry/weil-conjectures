## Worker report

The module `Sheaf.Topology.OverlappingOpenIrreducibleIntervals` states
`TopologicalSpace.IrreducibleCloseds.overlappingOpenIrreducibleIntervals`, with a single
`sorry` proof. It supplies no definitions, no extra nodes, and no dependency repairs.
The original node is unchanged except for `lean`.

Hypotheses and objects, matched against the original node:

- An arbitrary topological space is `{X : Type u} [TopologicalSpace X]`, with explicitly
  declared universe `u` and `autoImplicit false`.
- `U V : Opens X` are precisely arbitrary open subsets. Their carrier subtypes, and the
  carrier `↥(U ⊓ V)` of their intersection, use `instTopologicalSpaceSubtype`.
- `Z Z' : IrreducibleCloseds V` encode both irreducibility (including nonemptiness)
  and closedness in the space V. The condition `hZZ' : Z ≤ Z'` is inclusion.
- `hmeet : ((Z : Set V) ∩ Subtype.val ⁻¹' (U : Set X)).Nonempty` is exactly
  `Z ∩ U ≠ ∅`, with no separate assumption on either open.

Every conclusion is represented as follows:

- The existential `C C' : IrreducibleCloseds U` supplies their irreducibility and
  closedness. The first two equalities specify their carrier sets as the closures in U
  of `Subtype.val ⁻¹' (Subtype.val '' Z)` and the analogous expression for Z'.
  The image is the carrier of Z as a subset of X, and the preimage restricts it to U.
  Since Z is already a subset of V, this is exactly `Z ∩ (U ∩ V)` as a subset of U.
  Thus these are the specified closures, rather than arbitrary witnesses.
- `hCC' : C ≤ C'` is the asserted inclusion of closures.
- `A B : IrreducibleCloseds ↥(U ⊓ V)` and the next two carrier equalities specify
  `A = Z ∩ W` and `B = Z' ∩ W` in W, where W = U ⊓ V.
- The next two preimage equalities are `C ∩ W = Z ∩ W` and
  `C' ∩ W = Z' ∩ W`, using A and B. The witness `hAB : A ≤ B` is the inclusion
  inherited from `hZZ'`.
- `Set.Icc Z Z'` is the entire interval of irreducible closed subsets of V between
  Z and Z', ordered by inclusion. `Set.Icc C C'` and `Set.Icc A B` are exactly
  the other two full intervals.
- `e : Set.Icc Z Z' ≃o Set.Icc C C'` supplies inverse inclusion-preserving
  bijections, with forward F = e and reverse G = e.symm. Their first two
  universally quantified carrier equalities give precisely the node's closure
  formulas in the correct ambient topologies U and V.
- `rV` and `rU` identify each full interval with the full interval in W. Their
  universally quantified forward formulas are intersection with W, and their inverse
  formulas are closure in V and U respectively. The equation `rU (e D) = rV D`
  explicitly says these identifications agree with F.
- The four equalities after that commuting identity give F(Z) = C, F(Z') = C',
  G(C) = Z, and G(C') = Z'.
- The final clause quantifies over `saturated : Bool` and `n : ℕ`. For false, its
  relation is strict inclusion; for true it is Mathlib's covering relation `⋖`.
  A `RelSeries` is a sequence with n strict inclusions and n+1 members. The
  subtypes require the specified first and last endpoints and `s.length = n`.
  `ec` is an equivalence between the complete chain types at that length.
  Its two list equalities specify application of F and G to every term, respectively.
  Thus these are the induced inverse chain bijections, not unrelated bijections.
  For covering, every potential inserted irreducible closed subset between two members
  of a full interval is automatically a member of that interval; covering in this
  subtype therefore means exactly the node's condition in the whole ambient space.
  Nonemptiness of equivalent types for each n says precisely that the attainable
  strict-chain lengths and attainable saturated-chain lengths agree. Length-zero
  series are allowed.
- The order isomorphism also applies termwise to chains indexed by other ordered
  sets, if those are considered: its inverse identities preserve strictness and
  covering. The finite length comparison is explicitly exposed by `ec`.
- No affineness, separation, sobriety, Noetherian, nonempty-space, or dimension
  assumption is imposed. No endpoint is assumed distinct from the other.

Dependencies read and used:

- `def-kun-subspace-topology`: `Mathlib.Topology.Defs.Induced`, declaration
  `instTopologicalSpaceSubtype`, read at lines 76–78: the induced topology along
  `Subtype.val`. The recorded declaration and module are imported directly.
- `def-weil-irreducible-components`: `mathlib_match` is `irreducibleComponents`
  in `Mathlib.Topology.Irreducible`, definition at lines 105–108. Its signature
  and docstring, and the underlying `IsIrreducible` definition at lines 50–53,
  were read. This node also defines irreducibility, the relevant notion here.
  `Mathlib.Topology.Sets.Closeds` imports this module and provides
  `TopologicalSpace.IrreducibleCloseds`, which bundles that exact predicate and
  `IsClosed` (lines 394–409). No replacement predicate was introduced.
- Proof dependency `lem-weil-pbc-open-subspace-irreducible-closed-correspondence`:
  `mathlib_match` is `TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding`
  in `Mathlib.Topology.Sets.Closeds`, read in full at lines 510–536. It is
  available through the public import already needed for the statement.
- Existing Mathlib `RelSeries`, `RelSeries.head`, `RelSeries.last`,
  `RelSeries.toList` from `Mathlib.Order.RelSeries`, and the covering relation
  from `Mathlib.Order.Cover`, express chains and saturation without duplicate
  definitions. `Mathlib.Topology.Sets.Opens` provides bundled opens and their
  intersection. Every direct import serves the statement or a recorded dependency.

Source: read the node and all five proof steps, both statement dependencies, and the
single-open proof dependency. Read `literature/stacks-project/topology.tex`,
`lemma-catenary` (Tag 02I2), including its restriction/closure proof at lines
1547–1563. Read the current blueprint ancestor statement and proof at
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality*`.
The node records this result as inherited catenarity support, rather than claiming
that the latest ancestor directly states the overlap lemma. Its source-based proof
is unchanged.

Edge cases checked before writing:

- Z = Z': each full interval is a singleton; the one-term series at n = 0 occurs
  on both sides, while no positive-length strict or covering chain occurs.
- Empty X, U, V, or W: no choice of Z and hmeet can satisfy the hypotheses.
  The theorem does not add a nonemptiness instance to exclude these cases silently.
- U = V, U = X, or V = X: the same preimage/image formulas reduce to the usual
  restriction/closure correspondence, with ambient closure still explicit.
- Non-T0 and non-sober spaces are permitted. An indiscrete nonempty space gives
  singleton irreducible-closed intervals. The Sierpinski space shows why one must
  retain the nonempty intersection assumption.
- No finite-dimensional or finite-length assumption is made: an interval can have
  arbitrarily long strict chains or no saturated chain of a particular finite length.
  The equivalences of potentially empty chain types cover both situations.

Searches actually run for an existing full statement:

- `msearch.py ... leanfinder` with query “Overlapping open subsets induce inverse
  closure restriction order isomorphisms on intervals of irreducible closed subsets
  preserving strict and saturated chains”: OK, 8 hits, including
  `TopologicalSpace.IrreducibleCloseds.orderIsoSubtype`, `orderIsoSubtype'`,
  `irreducibleSetEquivPoints`, scheme open restriction, and prime-spectrum
  correspondences; no full overlap-interval/chain statement.
- `msearch.py ... loogle` with query
  `OrderIso.Icc, TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding`:
  OK, 0 hits for that combined query. The single-open declaration was independently
  located and read in Mathlib rather than inferred absent.
- `msearch.py ... leansearch` with query “Order isomorphisms between intervals of
  irreducible closed subsets in overlapping open subspaces preserve saturated chains
  and their lengths”: OK, 8 hits, including `OrderIso.Icc`, `IsChain.image_iso`,
  `IsChain.image_iso_iff`, and other interval or open congruences; no full statement.
  `OrderIso.Icc` in this Mathlib version assumes lattices and is not itself the
  topological overlap theorem.
- `msearch.py ... grep` with regular expression
  `orderIsoOfIsOpenEmbedding|overlap.*[Ii]rreducible|[Ii]rreducible.*overlap`
  restricted to `Topology`: OK, 2 hits, the single-open definition in
  `Mathlib/Topology/Sets/Closeds.lean` and its use in
  `Mathlib/Topology/KrullDimension.lean`.
- `rg` across both `lean/WeilConjectures` and `lean/Sheaf` for
  `overlapping.*[Ii]rreducible|[Ii]rreducible.*[Ii]nterval|lem-trf-overlapping-open-irreducible-intervals`
  found only the existing parent's proof description in
  `Sheaf/TraceFormula/CatenaryAffineOpenCover.lean`; it states catenarity of
  affine coordinate rings and does not state this arbitrary-space interval lemma.
- `grep -rn` for the exact node id in `lean/WeilConjectures` found no match.
  A further `rg` search for the proposed declaration name in Mathlib, upstream,
  and Sheaf found no collision; searching `dag/lean_names_upstream.json` for that
  name or irreducible interval names also found none.
- Read Mathlib's complete `IrreducibleCloseds` implementation and searched
  `Mathlib/Order/RelSeries.lean` for map, equivalence, LTSeries, length, head,
  last, and CovBy; reused the existing relation series representation.

Validation: `scompile.py Q44 lem-trf-overlapping-open-irreducible-intervals <module>`
passed both its sandbox and final library-module compile, with no errors or
unexpected warnings. An initial carrier-coercion ambiguity in `U ⊓ V` was
repaired by explicitly writing `↥(U ⊓ V)` everywhere a type is required.
No statement defect or `STATEMENT-DISPUTED` issue was found.

## Second reading by Q44

The delivered section with this heading was the worker's own self-check ("a separate
worker self-check, not an independent-agent review"). The maintainer's reviewer replaced it
with the independent clause-by-clause reading below (review of 109d3bbfe4d5, 2026-10-24).
The Lean module and the node record are unchanged.

Node clauses, the Lean that renders each, and the verdict:

1. X a topological space: `{X : Type u} [TopologicalSpace X]`, single declared universe. Exact.
2. U, V open subsets with subspace topologies (def-kun-subspace-topology):
   `U V : Opens X`; carriers `↥U`, `↥V`, `↥(U ⊓ V)` carry `instTopologicalSpaceSubtype`,
   the recorded declaration. Exact.
3. Z ⊆ Z' irreducible closed in V (def-weil-irreducible-components): `Z Z' : IrreducibleCloseds V`,
   bundling Mathlib `IsIrreducible` (the node's irreducibility) and `IsClosed`; `hZZ' : Z ≤ Z'`
   is inclusion (SetLike order). Exact.
4. Z ∩ U ≠ ∅: `hmeet : ((Z : Set V) ∩ Subtype.val ⁻¹' (U : Set X)).Nonempty`. Exact, nothing stronger.
5. W = U ∩ V, C = cl_U(Z ∩ W), C' = cl_U(Z' ∩ W): `C C'` carriers are
   `closure (Subtype.val ⁻¹' (Subtype.val '' Z))` in `↥U`; since Z ⊆ V the set is Z ∩ W in U.
   Closure is taken in U's topology. Exact.
6. C ⊆ C' irreducible closed in U: `C C' : IrreducibleCloseds U`, `hCC' : C ≤ C'`. Exact.
7. C ∩ W = Z ∩ W, C' ∩ W = Z' ∩ W: `A B : IrreducibleCloseds ↥(U ⊓ V)` with carriers the
   preimages of Z, Z' under W → V, and the preimages of C, C' under W → U equal to A, B. Exact
   (and A, B being irreducible closed in W is also true by the single-open correspondence).
8. Intervals [Z,Z']_V, [C,C']_U of irreducible closed subsets, inclusion order: `Set.Icc Z Z'`,
   `Set.Icc C C'` in `IrreducibleCloseds`, full intervals, subtype order. Exact.
9. F, G inverse inclusion-preserving bijections with F(D) = cl_U(D ∩ W), G(E) = cl_V(E ∩ W):
   `e : Set.Icc Z Z' ≃o Set.Icc C C'` with carrier formulas for `e D` and `e.symm E`. Exact;
   F and G are pinned, so the existential is not an arbitrary choice.
10. Endpoints to endpoints: the four equalities `e Z = C`, `e Z' = C'`, `e.symm C = Z`,
    `e.symm C' = Z'`. Exact.
11. Identification with the W-interval by intersection with W: `rV`, `rU` order isos onto
    `Set.Icc A B` with intersection formulas, inverse closure formulas, and `rU (e D) = rV D`. Exact.
12. Length-preserving inverse bijections on finite strict / saturated chains with these endpoints:
    for each `saturated : Bool` and `n`, `ec` between `RelSeries` over `<` (resp. `⋖`) in the
    intervals with head/last the endpoints and length n, given termwise by `e` and `e.symm`
    (`toList` equalities). Length = number of strict inclusions = `RelSeries.length`. Covering in
    the full interval equals the node's saturation (any inserted irreducible closed set between
    interval members lies in the interval; `⋖` implies `<`). Exact.
13. Equal attainable lengths: follows from `ec` for each n (equivalent types are simultaneously
    nonempty); the Lean states the stronger-in-form but node-asserted bijections. Exact.
14. No affineness/separation/sobriety/Noetherian hypothesis: none imposed. Exact.

Edge cases: Z = Z' (singleton intervals, only n = 0 series on both sides); empty X/U/V/W excluded
only through `hmeet`, as in the node; non-T0 spaces allowed; infinite intervals allowed (chain
types may be empty for given n on both sides).

Source: Stacks topology.tex lemma-catenary (Tag 02I2), lines 1547-1563, proof's closure
bijection for an open U ⊆ X, applied to W in V and in U; matches the node's source place.

Searches: Mathlib `TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding`
(Topology/Sets/Closeds.lean:515) is only the single-open correspondence (the proof dependency);
no overlap-interval theorem in Mathlib or lean/Sheaf, and the declaration name is unused in
the live tree. One statement per notion: no new definitions are introduced.

Mismatches found: none in the Lean or the node record. Only this report section was replaced.
