## Worker report

The module `Sheaf.Topology.WLocalComponents` states
`WLocalSpace.spectralSpace_closedPoints_components`, with exactly one postponed
proof (`sorry`). No definition, helper theorem, new node, dependency repair, or
statement correction is needed. The node copy changes only `lean`.

Source read: the current blueprint file
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-pe-wlocal/det-pe-wlocal-components.md`,
and `literature/stacks-project/proetale.tex`, lemma-spectral-split and
definition-w-local (Tags 0968 and 096A). The blueprint's full four-clause
statement is retained. The docstring supplies all seven proof steps and their
DAG citations, including the compact-open proof of profiniteness, existence of
closed specializations, the homeomorphism construction, converse and prime
localization argument.

Hypotheses and clauses, in the order of the Lean conjunction:

- A spectral topological space: `(T : Type u) [TopologicalSpace T]
  [SpectralSpace T]`. Closedness of the closed-point locus is precisely
  `(hclosed : IsClosed (closedPoints T))`. All later topological terms use the
  original topology or its standard subtype/quotient topology.
- Clause 1: `CompactSpace (closedPoints T) ∧ T2Space (closedPoints T) ∧
  TotallyDisconnectedSpace (closedPoints T)` is exactly profiniteness of the
  closed-point subspace, without assuming uniqueness of specializations.
- Clause 2 hypothesis: `∀ x : T, ∃! c : closedPoints T, x ⤳ c.val` says exactly
  one closed specialization exists for each point. `x ⤳ c.val` has the source
  orientation: c is in the closure of the singleton x.
- Clause 2 map: `∃ r : T → closedPoints T, Continuous r ∧ ...` asserts existence
  of the continuous map, and `∀ x, x ⤳ (r x).val` specifies its value as the
  unique closed specialization. Thus the map is fully determined, rather than
  an arbitrary retraction. No choice-based definition or extra map hypothesis
  is used. `∀ c, r c.val = c` says it retracts the inclusion.
- Clause 2 fibres and components: for every closed c,
  `r ⁻¹' {c} = connectedComponent c.val` and
  `connectedComponent c.val = {x : T | x ⤳ c.val}` identify the fibres,
  components, and generalizations. These account for every component since
  every x specializes to r(x) in its component.
- Clause 2 canonical homeomorphism:
  `IsHomeomorph (ConnectedComponents.mk ∘ (Subtype.val : closedPoints T → T))`
  concerns the specified composite, not an unspecified homeomorphism. The
  following `CompactSpace`, `T2Space`, `TotallyDisconnectedSpace` conjunction
  states profiniteness of the quotient space `ConnectedComponents T`.
- Clause 3 converse hypothesis:
  `∀ x : T, ∃! c : closedPoints T, c.val ∈ connectedComponent x` expresses
  exactly one closed point per connected component, since each component is
  the component of any one of its points. The conclusion is the same
  existence-and-uniqueness specialization formula as clause 2's hypothesis.
- Clause 3 agreement: `WLocalSpace T ↔ ∀ x : T, ∃! c : closedPoints T,
  c.val ∈ connectedComponent x` spells out the equivalence under the ambient
  spectrality and closedness assumptions. The next universally quantified
  ring clause spells it out for the recorded ring definition:
  `IsWLocalRing R ↔ IsClosed (closedPoints (PrimeSpectrum R)) ∧
  ∀ x, ∃! c : closedPoints (PrimeSpectrum R), c.val ∈ connectedComponent x`.
  Closedness is explicitly retained on that right side, because this ring
  clause has its own R and does not inherit hclosed about T.
- Clause 4: `∀ (R : Type v) [CommRing R] [IsWLocalRing R] (m : Ideal R)
  [m.IsMaximal], ...` introduces an arbitrary w-local commutative ring and
  maximal ideal (equivalently a closed point of its spectrum).
  `connectedComponent (⟨m, inferInstance⟩ : PrimeSpectrum R) =
  Set.range (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m)))`
  is the asserted localization image. `PrimeSpectrum R` is exactly the
  underlying Zariski space of `Spec (CommRingCat.of R)`, and `comap` of this
  algebra map is the underlying map of its scheme `Spec.map`.

Dependencies read and reused:

- `def-weil-spectral-space`: `SpectralSpace` from
  `Mathlib.Topology.Spectral.Basic` (T0, compact, quasi-sober, quasi-separated,
  compact-open basis). Available through the public WLocal import.
- `sk-def-pe-wlocal`: the recorded declarations `WLocalSpace` from
  `WeilConjectures.Topology.SpectralSpace.WLocal.Basic` and `IsWLocalRing`
  from `WeilConjectures.RingTheory.ProEtale.WLocal`. These are imported via
  their owning WLocal module. The record's umbrella WContractible module
  additionally contains stronger notions unused in this item; those notions
  and their definitions were read, and are not assumed here.
- `def-weil-pbc-w-local`: the same `IsWLocalRing`/`WLocalSpace`, used in the
  explicit component-based characterization, rather than copied predicates.
- `def-weil-affine-spectrum`: Mathlib's `AlgebraicGeometry.Spec`, whose
  underlying space is `PrimeSpectrum R`, and `Spec.map`, whose underlying
  map is `PrimeSpectrum.comap`. Only those underlying spaces/maps occur here;
  the owning topology module is publicly imported. No scheme structure needs
  redefinition or an additional equivalence assumption.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` in
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, together with its canonical
  algebraMap; this owning module is publicly imported.
- Proof dependencies imported as `import`:
  `Sheaf.Topology.SpectralClosedSubspace`, declaration
  `Topology.spectral_closed_subspace`, and
  `Sheaf.Topology.ProconstructibleClosureSpecialization`, declaration
  `Topology.exists_mem_iInter_closure_singleton`.
- The remaining proof dependencies are already available in these imports:
  `QuasiSeparatedSpace.isRetrocompact_iff_isCompact` and
  `Topology.IsConstructible` (`Mathlib.Topology.Constructible`),
  `IsClosed.exists_closed_singleton` (`Mathlib.Topology.Separation.Basic`),
  `WLocalSpace.isHomeomorph_connectedComponents_closedPoints`
  (`WeilConjectures.Topology.SpectralSpace.WLocal.ConnectedComponents`), and
  `PrimeSpectrum.localization_comap_isEmbedding` /
  `PrimeSpectrum.localization_comap_range`
  (`Mathlib.RingTheory.Spectrum.Prime.Topology`). Their recorded signatures
  and docstrings were read; no missing statement interface was found.

Edge cases checked mathematically before writing:

- Empty spectral T: closed points and components are empty profinite spaces;
  all pointwise uniqueness conditions are vacuous, and the unique empty map
  gives the retraction. There is no Nonempty assumption.
- The zero ring: its spectrum and closed-point locus are empty. The affine
  characterization remains valid; clause 4 has no maximal ideal to quantify.
- A local ring has one closed point, but may have many generalizations;
  clause 4 gives its whole connected spectrum. The fibre is not erroneously
  identified with a singleton in the original space.
- Disconnected spectra, for instance products of fields: each maximal ideal
  has its own component; no connectedness or local-ring hypothesis is added.
- Merely unique closed specializations are not substituted for closedness of
  the closed-point locus. The closedness hypothesis stays explicit.
- `u` and `v` are explicitly bound independent universes. R need not have the
  same universe as T. No automatic implicit variables, file-local notation,
  or file-local instances are used.

Searches for an existing full statement:

- `msearch.py ... leanfinder "A spectral space with closed set of closed points
  retracts continuously onto closed points and its connected components are
  the generalizations of unique closed specializations"`: eight results on
  spectral/quasi-sober spaces and generic points; none states all clauses.
- `msearch.py ... loogle "WLocalSpace, connectedComponent"`: no hits;
  WLocalSpace is unknown to the remote Loogle Mathlib index.
- `msearch.py ... grep "closedPoints|closedPoint|connectedComponent"
  Topology/Spectral`: no hits.
- `msearch.py ... leansearch "In a spectral space with closed set of closed
  points, closed points are profinite and unique closed specializations are
  the connected components"`: eight hits including `closedPoints`,
  `Profinite`, `SpectralSpace.mk`, local-ring specialization facts and
  `PrimeSpectrum.instSpectralSpace`; no full statement.
- Direct `rg` of the upstream `WeilConjectures/Topology` and
  `WeilConjectures/RingTheory/ProEtale` sources and the corresponding
  `lean/Sheaf/Topology` and `lean/Sheaf/RingTheory` sources for closed points,
  connected components and localization found the already-used WLocal
  homeomorphism, closed-point instances, and related ring constructions,
  but no declaration with all four assertions. The upstream WLocal files
  were read in full. The existing clopen-partition statement concerns affine
  partitions and is not this general spectral-space result.
- Direct `rg` of upstream, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  `det-pe-wlocal-components|wlocal_components|wLocal_components`: no matches.
  The chosen full declaration name has no existing match.

Validation: `scompile.py Q96 det-pe-wlocal-components` compiled the delivered
module as both a sandbox and its library module, cleanly in 1.6 seconds each.
All theorem proofs remain `sorry`, as stage 2 requires. No statement fault or
STATEMENT-DISPUTED issue was found.

## Second reading by Q96

I read the node statement, its blueprint source, the Stacks proof at Tags 0968
and 096A, and the complete Lean declaration. The matching is as follows.

- The object `T`, its topology, spectral-space instance, and closed-point
  closedness are rendered by `(T : Type u) [TopologicalSpace T]
  [SpectralSpace T]` and `hclosed : IsClosed (closedPoints T)`. These are exactly
  the standing hypotheses of the node; no separation, finiteness, or
  nonemptiness assumption is added.
- Clause 1, that the closed-point subspace is profinite, is rendered by
  `CompactSpace (closedPoints T) ∧ T2Space (closedPoints T) ∧
  TotallyDisconnectedSpace (closedPoints T)`. This is the project's
  compact-Hausdorff-totally-disconnected rendering of “profinite”.
- Clause 2's unique-specialization premise is rendered by
  `∀ x : T, ∃! c : closedPoints T, x ⤳ c.val`. Its canonical map is the
  existential `r : T → closedPoints T`, with continuity, specialization to
  `r x`, and retraction equations. The two fibre/component equalities are
  rendered literally, and the specified composite
  `ConnectedComponents.mk ∘ (Subtype.val : closedPoints T → T)` is required to
  be a homeomorphism. Compactness, Hausdorffness, and total disconnectedness
  of `ConnectedComponents T` state the final profiniteness clause.
- Clause 3's converse premise and specialization conclusion are rendered in
  the same quantifier order. The space-level agreement is
  `WLocalSpace T ↔ ∀ x : T, ∃! c : closedPoints T,
  c.val ∈ connectedComponent x`; the ring-level agreement is separately
  rendered as `IsWLocalRing R ↔ IsClosed (closedPoints (PrimeSpectrum R)) ∧ …`,
  so the affine closedness condition is retained rather than inferred from
  the earlier `T`.
- Clause 4 quantifies over `(R : Type v) [CommRing R] [IsWLocalRing R]`, a
  maximal ideal `(m : Ideal R) [m.IsMaximal]`, and states exactly the component
  equality with `Set.range (PrimeSpectrum.comap
  (algebraMap R (Localization.AtPrime m)))`. This is the underlying map of
  `Spec R_m → Spec R` and uses the canonical localization construction.

The empty spectral space is covered: the closed-point and component spaces are
empty and all pointwise uniqueness premises are vacuous. The zero ring has empty
spectrum, and the maximal-ideal clause is vacuous. The formulation permits
multiple components (for example a product of fields), permits a local ring's
nontrivial generalizations, and imposes no characteristic or universe equality;
`u` and `v` are independent. The specialization orientation `x ⤳ c.val` is the
source orientation (the closed point lies in the closure of `x`).

I searched the Mathlib and project sources with `rg` for the theorem name and
for `closedPoints`, `connectedComponent`, `WLocalSpace`, and localization-range
formulas, and reran the LeanFinder/Loogle/LeanSearch queries recorded above.
The only matches were the dependency declarations (including
`WLocalSpace.isHomeomorph_connectedComponents_closedPoints` and
`PrimeSpectrum.localization_comap_range`); none states this four-clause result.
I also read every recorded dependency signature: `SpectralSpace`, `WLocalSpace`,
`IsWLocalRing`, `AlgebraicGeometry.Spec`, and `Localization.AtPrime` are the
notions used by the file, with no private duplicate or missing helper.

No mismatch was found, so no Lean or node repair was necessary. The module has
one postponed theorem proof, with source and `(blueprint: det-pe-wlocal-components)`
docstrings, and `scompile.py` passes for both sandbox and library compilation.
