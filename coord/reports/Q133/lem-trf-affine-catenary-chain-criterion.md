## Worker report

The module `Sheaf.AlgebraicGeometry.AffineCatenaryChainCriterion` states
`AlgebraicGeometry.affine_catenary_chain_criterion`, with exactly one postponed
proof (`sorry`). It has no definitions. Only the assigned node's `lean` field
changes. No statement correction, dependency repair, new node, or disputed
statement is needed.

Clause-by-clause correspondence:

- The affine scheme is `(T : Scheme.{u}) [IsAffine T]`. The global section ring is
  written directly as `Γ(T, ⊤)` everywhere; there is no auxiliary ring or chosen
  presentation. The universe `u` is explicit and arbitrary, and `autoImplicit`
  is disabled. There is no Noetherian or nonemptiness hypothesis.
- The homeomorphism is the existential `h : T ≃ₜ PrimeSpectrum Γ(T, ⊤)`.
  Mathlib identifies the underlying space of `Spec Γ(T, ⊤)` with this spectrum.
- `F : PrimeSpectrum Γ(T, ⊤) → IrreducibleCloseds T` supplies the image of every
  prime as an actual nonempty irreducible closed subset. Its first conjunct is
  `(F r : Set T) = h ⁻¹' PrimeSpectrum.zeroLocus (r.asIdeal : Set Γ(T, ⊤))`.
  Thus it is exactly the specified inverse-image assignment, not an arbitrary
  interval equivalence or a correspondence between arbitrary closed subsets.
- A prime interval is quantified as `p q : PrimeSpectrum Γ(T, ⊤)` with `p ≤ q`.
  The order is ideal inclusion. The entire-interval correspondence is
  `e : Set.Icc p q ≃o (Set.Icc (F q) (F p))ᵒᵈ`, with the required value
  `(e r).val = F r.val` for every interval member. `≃o` gives bijectivity and
  preservation/reflection of the dual order, hence inclusion reversal. The
  codomain includes every irreducible closed subset between the endpoints.
- Finite strict chains use Mathlib's `LTSeries`. Subtypes impose `head = p`
  and `last = q`, respectively `head = F q` and `last = F p`.
  The existential `e` is an equivalence of these full chain types.
- Length is `RelSeries.length`, which counts strict inclusions rather than
  terms. `(e s).val.length = s.val.length` states preservation. The further
  identity `(e s).val.toList = (s.val.toList.map F).reverse` fixes the actual
  chain assignment as order reversal of the images, including every term.
- Saturation is `∀ i : Fin s.length, s i.castSucc ⋖ s i.succ`.
  In the partial orders of primes and irreducible closed subsets, `⋖` means
  strict inclusion with no member strictly in between. For a chain with these
  endpoints any such intermediate member automatically lies in the endpoint
  interval. The pointwise iff between saturation of `s` and `e s`, together
  with the equivalence on all chains, is precisely its restriction to a
  bijection on saturated chains.
- The consequence is the biconditional `IsCatenaryRing Γ(T, ⊤) ↔ ...`.
  Its right side quantifies every `Z Z' : IrreducibleCloseds T` with `Z ≤ Z'`.
  The first conjunct `∃ N : ℕ, ∀ s : LTSeries ..., ... → s.length ≤ N`
  is the finite upper bound on all strict chain lengths in that interval.
  The second compares arbitrary chains `s t` with the same endpoints under
  their respective saturation conditions and concludes `s.length = t.length`.
  Neither a global bound independent of the endpoints nor finite cardinality
  of an interval is assumed.
- The next two conjuncts assert saturated-chain existence under a length
  bound, separately in irreducible-closed intervals and prime intervals.
  Each quantifies comparable endpoints, assumes the bound over all finite
  strict chains with those endpoints, and supplies a chain with the stated
  head and last and every adjacent pair a cover. No catenarity or equality
  of saturated lengths is needed for this existence assertion.
- The empty-affine clause is explicit:
  `IsEmpty T → Subsingleton Γ(T, ⊤) ∧ IsEmpty (PrimeSpectrum Γ(T, ⊤)) ∧
  IsEmpty (IrreducibleCloseds T)`. A subsingleton unital ring is the zero ring.
  Empty spectrum and empty irreducible-closed type mean that no intervals
  exist on either side; all the universal interval assertions are vacuous.

Dependencies read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`; affineness uses
  `AlgebraicGeometry.IsAffine` in `Mathlib.AlgebraicGeometry.AffineScheme`.
  Its canonical `Scheme.isoSpec` supplies the proof's affine identification.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`; the underlying set is `PrimeSpectrum`.
  `PrimeSpectrum.zeroLocus` supplies exactly the sets V(r) in the formula.
- `def-weil-irreducible-components`: the recorded Mathlib match is
  `irreducibleComponents` in `Mathlib.Topology.Irreducible`, whose definition
  uses `IsIrreducible`. This is nonempty preirreducibility, equivalent to the
  closed-cover definition in the node. The bundled subtype
  `TopologicalSpace.IrreducibleCloseds` in `Mathlib.Topology.Sets.Closeds` uses
  exactly `IsIrreducible` and `IsClosed`; its order is subset inclusion.
  Maximality is intentionally not imposed: the item concerns all irreducible
  closed subsets, not only irreducible components.
- `def-exc-excellent-ring`: the recorded module
  `Sheaf.RingTheory.ExcellentRing` is imported publicly and its
  `IsCatenaryRing` is used directly. I read `IsPrimeChain` and
  `IsSaturatedPrimeChain` there as well: these encode Fin-indexed chains of
  ideals, primality, strict adjacent inclusions, and absence of prime
  insertions, exactly equivalent to the `LTSeries` and cover encoding used
  on the topological side. The upstream module
  `WeilConjectures.RingTheory.Excellent` also declares `IsCatenaryRing` with a
  different interface; it is not imported, preserving the recorded interface
  and avoiding that duplicate declaration.
- The proof dependencies `lem-weil-pbc-affine-open-spec-points` and
  `lem-weil-pbc-spec-irreducible-closed-subsets-primes` are Mathlib leaves.
  Their recorded signatures/docstrings were read:
  `IsAffineOpen.fromSpec`, `isOpenImmersion_fromSpec`, `range_fromSpec`,
  `primeIdealOf`, `fromSpec_primeIdealOf` in
  `Mathlib.AlgebraicGeometry.AffineScheme`, and
  `PrimeSpectrum.closure_singleton`, `pointsEquivIrreducibleCloseds` in
  `Mathlib.RingTheory.Spectrum.Prime.Topology`. The latter module is already
  publicly imported by `Sheaf.RingTheory.ExcellentRing`; no redundant import
  or missing helper module is necessary. All four proof dependencies are
  named in the theorem's seven-step natural-language proof.

Source and edge-case checks:

I read Stacks `literature/stacks-project/algebra.tex`, definition-catenary and
lemma-catenary (Tags 00NI and 02IH). The former explicitly requires bounded
lengths and equal maximal lengths without Noetherianity; the latter derives
its equivalence from irreducible closed subsets. The affine interpretation
is the existing Mathlib `Scheme.isoSpec`, as in Tag 01HW. The node is an
auxiliary node below the blueprint unit, not the unit's own statement.
The prescribed example `Sheaf.CategoryTheory.CompactObject` is now withdrawn
and contains no declarations; the delivered header follows the current
module-mode conventions and the active `CatenaryAffineOpenCover` module.

I checked equal endpoints and `n = 0`: `LTSeries` includes singleton chains
of length zero, and the saturation condition is vacuous over `Fin 0`.
Their reverse remains the singleton. Distinct comparable endpoints always
admit a two-term strict chain, so boundedness is not being used to infer
existence from an empty set of lengths. No globally finite dimension,
finite interval, Noetherianity, or irreducibility of all of T is required.
Empty T is explicitly allowed. Nonempty irreducible closed subsets exclude
the empty set even in that case. Saturation in the whole partial order and
saturation inside the interval agree because intermediate elements lie
between the fixed endpoints. The bound is endpoint-dependent as required.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "Affine scheme catenarity is equivalent to bounded
  lengths and equal saturated lengths of chains of irreducible closed subsets"`:
  eight hits, including `IsNoetherian`, `IsArtinianScheme`,
  `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`, and
  `PrimeSpectrum.exist_ltSeries_mem_one_of_mem_last`; none gives this theorem.
- `msearch.py ... leansearch "An affine scheme has a catenary coordinate ring
  exactly when chains of irreducible closed subsets with fixed endpoints have
  bounded length and equal saturated lengths"`: eight hits about Artinian,
  affine, and Noetherian schemes; no complete criterion.
- `msearch.py ... loogle "PrimeSpectrum.pointsEquivIrreducibleCloseds"`:
  one exact supporting result, the order isomorphism from the spectrum to
  the order dual of its irreducible closed subsets. It does not assert the
  affine-global-sections chain equivalences, bounds, or saturated existence.
- `msearch.py ... grep "catenar|Catenar"`: zero Mathlib hits.
- `rg` in `lean/WeilConjectures` found the existing catenary ring definitions
  in `RingTheory/Excellent.lean`, not this affine theorem. Searching the
  exact node id there found no match.
- `rg` in `lean/Sheaf` found `ExcellentRing`, `CatenaryAffineOpenCover`, and
  `UniversallyCatenaryAffineCover`, but no affine chain criterion. Their
  definitions and statements were read to distinguish their scopes.
- Full-name search across `dag/lean_names_upstream.json`, Mathlib,
  `lean/WeilConjectures`, and `lean/Sheaf` found no conflicting declaration.

Validation: the required `scompile.py Q133
lem-trf-affine-catenary-chain-criterion <module>` compiles both sandbox and
library-path forms cleanly; there are no errors or unexpected warnings.
The final declaration name uses snake_case. The delivery dry run and actual
push are run using `deliver2.py`, with server preflight and per-file compile.

## Second reading by Q133

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
