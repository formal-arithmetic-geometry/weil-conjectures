## Worker report

`Sheaf.Topology.StoneanCover` states `stonean_cover` with `sorry` as its entire
proof. It states the three clauses of `det-pe-stonean-cover`, including the
specified ultrafilter-limit map, using existing definitions only. There is one
module, no new node, no dependency module, and no statement correction. The
sandbox node differs from its shared original only in `lean`.

Source read: the current blueprint statement and proof at
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/`
`sk-prop-pe-stonean/det-pe-stonean-cover.md` and
`det-pe-stonean-cover.proof.md`. The full node, both statement dependencies,
the extension proof dependency, their recorded declarations, and the example
`CompactObject.lean` and its node record were read. No repair note exists for
this item.

Hypotheses and objects, clause by clause:

- A compact Hausdorff space `T` is `(T : Type u) [TopologicalSpace T]
  [CompactSpace T] [T2Space T]`. The universe `u` is explicitly declared and
  arbitrary. No nonemptiness, total disconnectedness, metrizability or
  finiteness is assumed for `T`. Profinite spaces are included as examples.
- `D` is the underlying set of `T`, represented by the type argument `T` to
  `Ultrafilter`. This type argument does not use the topology on `T`.
  `Ultrafilter.topologicalSpace` is generated from `ultrafilterBasis T`,
  whose defining sets are exactly `{p : Ultrafilter T | E ∈ p}`.
  In particular this is the discrete-set Stone-Cech construction, not the
  Stone-Cech compactification of `T` with its given topology.
  `Ultrafilter.extend` itself installs the bottom (discrete) topology on its
  domain set, as its source shows. An additional discrete-space binder would
  add no data to this construction and would confuse the two topologies.
- The principal map is `(pure : T → Ultrafilter T)`. The documented Mathlib
  `Pure Ultrafilter` instance makes this exactly the principal ultrafilter
  at the point; `Ultrafilter.mem_pure` is membership in that point.
- Clause 1, compact Hausdorff: the first two conjuncts are
  `CompactSpace (Ultrafilter T)` and `T2Space (Ultrafilter T)`.
- Clause 1, all membership sets clopen:
  `∀ (E : Set T), IsClopen {p : Ultrafilter T | E ∈ p}`.
- Clause 1, density: `DenseRange (pure : T → Ultrafilter T)`.
  The specified membership basis is already the dependency's definition
  of the topology; no alternative or unspecified topology is introduced.
- Clause 2, extremal disconnectedness: `ExtremallyDisconnected (Ultrafilter T)`.
  This class says precisely that the closure of every open subset is open.
- Clause 2, profiniteness: `TotallyDisconnectedSpace (Ultrafilter T)` together
  with the compact and Hausdorff conjuncts of clause 1. This is exactly
  Mathlib's definition of profinite space: see `Profinite` and `Profinite.of`
  in `Mathlib.Topology.Category.Profinite.Basic`. It is also the encoding
  used by the recorded `det-pe-stonean-projective` theorem. This clause does
  not assert the space has any point, so includes the empty profinite space.
- Clause 2, projectivity: `CompactT2.Projective (Ultrafilter T)`. Its full
  signature, read in `Mathlib.Topology.ExtremallyDisconnected`, quantifies
  over continuous surjections `g : Y → Z` of compact Hausdorff spaces and
  continuous maps `f : Ultrafilter T → Z`, and gives a continuous lift with
  `g ∘ h = f`. It is the predicate used by the statement dependency.
- Clause 3, the specified map: `Ultrafilter.extend (id : T → T)`. This is
  Mathlib's existing extension construction applied to the underlying
  identity, not a new map, an arbitrary chosen map, or an assumed map.
- Clause 3, continuity: `Continuous (Ultrafilter.extend (id : T → T))`.
- Clause 3, surjectivity: `Surjective (Ultrafilter.extend (id : T → T))`.
- Clause 3, extends the identity: for every `t : T`,
  `Ultrafilter.extend (id : T → T) (pure t) = t`.
- Clause 3, unique limit characterization: for every `p : Ultrafilter T`
  and `x : T`, `(↑p : Filter T) ≤ 𝓝 x ↔
  x = Ultrafilter.extend (id : T → T) p`.
  The left side is exactly convergence of `p` in the original topology of
  `T`, since filter order is reverse inclusion. The right-to-left implication
  at the value itself asserts existence; the left-to-right implication asserts
  uniqueness and identifies this same map with the map in the node.

Dependency declarations read and used:

- `lem-weil-pbc-ultrafilter-compact-hausdorff-basis` is a Mathlib leaf with
  no `lean` record, as permitted. Its recorded declarations are
  `ultrafilter_compact`, `Ultrafilter.t2Space`, `ultrafilterBasis_is_basis`,
  `ultrafilter_isOpen_basic`, `ultrafilter_isClosed_basic` in
  `Mathlib.Topology.Compactification.StoneCech`. The defining
  `ultrafilterBasis`, `Ultrafilter.topologicalSpace`, and `Ultrafilter`
  signatures and docstrings were also read. These definitions give exactly
  the ultrafilters, topology and membership sets of the node.
- `det-pe-stonean-projective` is the published
  `CompactT2.extremallyDisconnected_iff_projective_iff_section` in
  `Sheaf.Topology.StoneanProjective`. Its full signature and proof docstring
  were read. The module is publicly imported, providing the existing
  extremal-disconnectedness and projectivity predicates and the theorem
  that stage 3 uses for clause 2.
- The additional proof dependency
  `lem-weil-pbc-ultrafilter-continuous-extension` is also a Mathlib leaf:
  `continuous_ultrafilter_extend` and `ultrafilter_extend_pure` in
  `Mathlib.Topology.Compactification.StoneCech`. The construction
  `Ultrafilter.extend` is used directly in the statement, so that module is
  publicly imported. Its definition and the full signatures of these
  lemmas, `ultrafilter_extend_extends` and `ultrafilter_extend_eq_iff` were
  read. The seven-step docstring preserves the DAG's elementary proof of
  limit identification and its explicit closure argument.

Edge cases checked before finalizing:

- Empty `T`: a proper ultrafilter cannot exist on the empty underlying set.
  Thus its ultrafilter space is empty. Density, the clopen assertions,
  extremal disconnectedness, total disconnectedness, and projectivity
  still hold. The empty extension map is continuous and surjective, and
  both pointwise assertions are vacuous. No `Nonempty` occurs in the statement.
- Singleton and finite discrete spaces: ultrafilters are principal and the
  extension has the expected identity values; no different choice of limit
  is permitted by the final equivalence.
- `E = ∅` and `E = Set.univ` yield the empty and full basic clopens.
  The closure proof includes the empty union explicitly.
- Infinite compact Hausdorff spaces, including connected ones, are covered:
  the original topology of `T` enters only the target and its limit
  characterization. No discrete assumption is made on the target topology.
- The ultrafilter type and the target have the same arbitrary universe `u`;
  the dependency's projectivity predicate uses that universe for its tests.
  No new size restriction is introduced.

Existing-statement searches performed:

- `msearch.py ... leanfinder`: “The space of ultrafilters on the underlying
  set of a compact Hausdorff space is compact Hausdorff extremally disconnected
  and projective, has dense principal ultrafilters and clopen membership sets,
  and the unique limit map is a continuous surjection”. Eight hits, including
  `CompHaus.projective_ultrafilter`, `Profinite.projective_ultrafilter`,
  `CompHaus.projectivePresentation`, `CompHaus.Gleason` and
  `Compactum.ofTopologicalSpace`. These are components, not the complete
  three-clause statement with the specified topology, density, clopens,
  extremal disconnectedness and unique-limit characterization.
- `msearch.py ... loogle`: `"ultrafilter_extend", "Ultrafilter"`.
  Four hits: `continuous_ultrafilter_extend`, `ultrafilter_extend_pure`,
  `ultrafilter_extend_extends`, `ultrafilter_extend_eq_iff`. Their full
  signatures agree with the extension and limit components used here.
- `msearch.py ... leansearch`: “The ultrafilter space on a set has a clopen
  basis, dense principal ultrafilters, and is extremally disconnected with a
  continuous limit surjection onto any compact Hausdorff topology on the set”.
  Eight hits: `ultrafilterBasis`, `Ultrafilter.topologicalSpace`,
  `Ultrafilter.t2Space`, `TopologicalSpace.isTopologicalBasis_clopens`,
  `ultrafilterBasis_is_basis`, `isDenseEmbedding_pure`,
  `instTotallyDisconnectedSpaceUltrafilter`, `ultrafilter_compact`.
  These match individual components and the existing topology; no full match.
- `msearch.py ... grep` in Mathlib `Topology`:
  `stonean_cover|denseRange_pure|projective_ultrafilter|ultrafilter_extend_eq_iff`.
  Eighteen hits: density, the limit equivalence and categorical projectivity
  components in StoneCech and CompHaus/Profinite projectivity modules,
  plus unrelated completion density results.
- `rg -n` for those same four patterns in upstream `WeilConjectures`, shared
  `lean/Sheaf`, and `dag/lean_names_upstream.json` found no existing match.
  `grep -rn det-pe-stonean-cover` in upstream `WeilConjectures` also found none.
  The published `StoneanProjective.lean` was independently read in full.

No STATEMENT-DISPUTED flag or unresolved node fault remains. Only `stonean_cover`
is postponed; it has the source citation, blueprint tag and complete seven-step
natural-language proof. No data definition or other DAG node is stated.

Validation: prescribed `scompile.py Q46 det-pe-stonean-cover` compiled both the
sandbox wrapper and `Sheaf/Topology/StoneanCover.lean` cleanly with no warnings,
within the 60-second file limit. The final clean compile took 3.0 seconds for
the sandbox and 3.4 seconds for the module. The second reading and delivery are
left to the independent next worker.

Dry run: `deliver2.py Q46 det-pe-stonean-cover --no-push` printed
`OK (dry run): commit 9575b92eac compiles and passes the preflight except for the
second reading, which the second reader writes; nothing pushed.` The independent
second-reading section remains for the next worker, as the wrapper instructs.


## Second reading by Q46

I independently opened the sandbox node and module, the blueprint statement and
proof at `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/`
`sk-prop-pe-stonean/det-pe-stonean-cover{,.proof}.md`, both statement-dependency
records, and the continuous-extension proof-dependency record. The item's source
is this blueprint, rather than a Stacks lemma. I also read the dependencies'
Stacks source, `literature/stacks-project/topology.tex`, section
`section-stone-cech` (Tag 0908), and the following definition and discussion of
extremal disconnectedness. The Stone-Cech universal property permits every
compact Hausdorff target; it introduces no nonemptiness, finiteness, or
profinite hypothesis. No repair note exists for this item.

Objects, hypotheses, and conclusion, checked against the node clause by clause:

- Object and hypotheses: `T : Type u`, `[TopologicalSpace T]`,
  `[CompactSpace T]`, `[T2Space T]` introduce exactly a compact Hausdorff
  space, including but not requiring profinite spaces. Verdict: exact.
- Underlying discrete set `D`: the argument `T` in `Ultrafilter T` is the
  underlying type, without its topology. `Ultrafilter` in
  `Mathlib/Order/Filter/Ultrafilter/Defs.lean` extends a proper filter and
  asserts maximality (minimality in the reverse-inclusion filter order).
  No filter is allowed to contain the empty set. Verdict: exact underlying
  set and ultrafilters; a second topology binder on `T` is unnecessary.
- Specified topology on beta D: `Ultrafilter.topologicalSpace` in
  `Mathlib/Topology/Compactification/StoneCech.lean` is `generateFrom
  (ultrafilterBasis T)`; `ultrafilterBasis` is the range of the membership
  sets `{p | E ∈ p}`. `ultrafilterBasis_is_basis` confirms these really form
  a basis. The instance is independent of the original topology of `T`.
  Verdict: the specified topology, with no alternative space substituted.
- Principal map: `(pure : T → Ultrafilter T)` uses the existing
  `Pure Ultrafilter` instance, and `Ultrafilter.mem_pure` says exactly
  `E ∈ pure t ↔ t ∈ E`. Verdict: exact principal ultrafilter map.
- Clause 1, compact Hausdorff: `CompactSpace (Ultrafilter T) ∧
  T2Space (Ultrafilter T)`. These are conclusions, with no extra assumption
  on the cover. Verdict: exact.
- Clause 1, clopens: `∀ (E : Set T), IsClopen {p : Ultrafilter T | E ∈ p}`
  ranges over every subset. The basis itself is fixed by the preceding
  instance, rather than assumed as a new hypothesis. Verdict: exact.
- Clause 1, density: `DenseRange (pure : T → Ultrafilter T)` asserts dense
  image, without a continuity assumption for the original topology on T.
  Verdict: exact.
- Clause 2, extremal disconnectedness:
  `ExtremallyDisconnected (Ultrafilter T)` is the Mathlib class whose field
  says every open subset has open closure. Verdict: exact.
- Clause 2, profiniteness: `TotallyDisconnectedSpace (Ultrafilter T)` together
  with the compact and Hausdorff conclusions is precisely the structure
  bundled by `Profinite.of`, whose signature I read in
  `Mathlib/Topology/Category/Profinite/Basic.lean`. Verdict: exact, including
  empty spaces; no extra inverse-limit data is demanded by this assertion.
- Clause 2, projectivity: `CompactT2.Projective (Ultrafilter T)`. I read its
  definition in `Mathlib/Topology/ExtremallyDisconnected.lean`: for arbitrary
  compact Hausdorff Y and Z in universe u, continuous f from the cover to Z,
  and a continuous surjection g from Y to Z, it gives continuous h with
  `g ∘ h = f`. This is exactly the predicate in the dependency
  `CompactT2.extremallyDisconnected_iff_projective_iff_section`, whose full
  signature and proof docstring I read in `Sheaf.Topology.StoneanProjective`.
  Verdict: exact projectivity convention, not projectivity merely among
  profinite spaces.
- Clause 3, named map: `Ultrafilter.extend (id : T → T)` is Mathlib's actual
  extension construction. I read its definition, which locally equips the
  domain set with the discrete topology, and the signatures of
  `continuous_ultrafilter_extend`, `ultrafilter_extend_pure`, and
  `ultrafilter_extend_eq_iff`. The last conjunct quantifies over every p and x
  and says `(↑p : Filter T) ≤ 𝓝 x ↔ x = Ultrafilter.extend id p`.
  This asserts existence by taking x to be the displayed value, uniqueness
  for all x, and identification with the very same map. Neighborhoods use
  T's original topology. Verdict: exactly the specified unique-limit map.
- Clause 3, continuity, surjectivity, and identity extension: the three
  conjuncts `Continuous (Ultrafilter.extend (id : T → T))`,
  `Surjective (Ultrafilter.extend (id : T → T))`, and
  `∀ t : T, Ultrafilter.extend (id : T → T) (pure t) = t` have precisely the
  stated domains and quantifiers. Verdict: exact.

The basis and continuous-extension Mathlib leaves have the exact recorded
signatures in StoneCech.lean; they are not private copies or specializations
requiring an unavailable instance. The single public Mathlib import supplies
both leaves, and the public StoneanProjective import supplies the other
statement dependency and the project's projectivity interface. No dependency
repair or new definition node is needed.

Edge cases: for empty T there is no proper ultrafilter, so the cover and map
are empty, density and all pointwise assertions are valid, and surjectivity
holds. For a singleton or any finite T, every ultrafilter is principal and
identity extension gives the expected values. Empty and universal membership
sets give empty and universal clopens. The closure argument explicitly handles
an empty family of basic opens. Connected infinite compact Hausdorff targets
are included because the cover topology ignores their topology while the
limit map uses it. Universe u is explicitly bound and arbitrary; ultrafilters
stay in that universe and projectivity uses the dependency's same-universe
category of compact Hausdorff spaces. There are no index, algebraic degree,
characteristic, or scheme binders that could exclude further edge cases.

Independent searches with different wording from the worker's:

- LeanFinder: "Ultrafilters on the discrete underlying set give an extremally
  disconnected projective cover of a compact Hausdorff space with the
  ultrafilter convergence projection". Eight hits, including
  `CompHaus.projective_ultrafilter`, `CompHaus.projectivePresentation`,
  `CompHaus.presentation.π`, and `StoneCech.projective`. I opened the concrete
  projectivePresentation implementation and the Stonean presentation. They
  supply components and constructions, not the full three-clause theorem.
- Loogle: `"Ultrafilter.extend"`. One hit, the existing extension definition
  with arbitrary domain and target universes and only a topology on the
  target. It is already used; no new definition is appropriate.
- LeanSearch: "A dense map of principal ultrafilters into the compact
  Hausdorff ultrafilter space, with extremally disconnected topology and
  continuous surjective unique limit map". Eight hits, including
  `denseRange_pure`, `isDenseEmbedding_pure`, `Ultrafilter.lim`, and
  `CompHaus.presentation`. The first two are component results. The lim
  construction is not needed and would introduce a nonemptiness issue;
  the chosen extension already handles the empty case.
- Mathlib grep via msearch:
  `projectivePresentation|stonean_cover|ultrafilter_extend_eq_iff|denseRange_pure`.
  Twenty-five hits, chiefly the concrete presentations and individual density
  and convergence lemmas. I checked their source signatures. A preliminary
  grep invocation accidentally treated `--help` as a directory and is not
  evidence; the subsequent proper grep above is the search used here.
- Independent `rg -n -i 'ultrafilter|stonean|gleason|stone.?cech'` on the upstream
  WeilConjectures tree, shared lean/Sheaf, and dag/lean_names_upstream.json:
  no full-item match. I opened `Profinite.exists_bounded_extremallyDisconnected_cover`
  in `Sheaf.Topology.BoundedExtremallyDisconnectedCover`; it assumes profinite T
  and a cardinal bound and asserts existence, without the specified cover,
  density, clopens, projectivity, or limit characterization. It cannot replace
  this item. The remaining source hits are references or imports.

No mathematical mismatch was found, so I retained the Lean module verbatim.
The only record repair is whitespace: `lean.statement` now literally copies
the multiline signature from the file, instead of its previous single-line
normalization. There is no statement correction, no citer audit required,
no dependency module and no new node. The only theorem is `stonean_cover`,
its proof is entirely `sorry`, and its docstring carries the source,
blueprint identifier, and all seven DAG proof steps, including the closure
formula and direct identification of the continuous extension's limit.
There are no hollow definitions, extra hypotheses, unbound variables,
file-local notation, or lines over 100 characters.

Second-reader validation: the prescribed scompile.py compiled the sandbox
wrapper (16.3 seconds) and the delivered StoneanCover module (11.4 seconds),
both without errors or warnings. A separate source check confirms exact
lean.statement equality, the unchanged non-lean node fields, and 100-column Lean
lines.
