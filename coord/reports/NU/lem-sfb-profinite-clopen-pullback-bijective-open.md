## Worker report

Item: lem-sfb-profinite-clopen-pullback-bijective-open. The module
`Sheaf.Topology.ProfiniteClopenPullback` states
`bijective_and_isOpenMap_of_bijective_clopen_preimage`, with its whole proof `by sorry`.
There are no definitions, additional nodes, dependency repairs or statement changes.
The node copy changes only `lean`.

Source read: `literature/stacks-project/topology.tex`, lines 4207–4229,
Tag 08ZZ, `lemma-profinite-refine-open-covering`. The source proves finite clopen
refinement and explains the pointwise clopen basis via finite-discrete projections.
The present criterion is the agent consequence specified by the node, not the
assertion of the tag itself. All four node proof steps are transcribed in the
Lean theorem's docstring, including the possibly empty finite subcover.

Hypotheses and clauses, matched individually:

- The size convention is rendered by explicit `universe u v` and
  `{P : Type u} {Q : Type v}`. These independent universes allow any two spaces
  in the chosen bounds. There is no category, site or derived category to shrink.
- The spaces and their topologies are `[TopologicalSpace P] [TopologicalSpace Q]`.
- Compactness of P and Q is `[CompactSpace P] [CompactSpace Q]`. Mathlib defines
  this by compactness of the universal set, equivalent to every open cover
  having a finite subcover; it does not include a separation assumption.
- Hausdorffness is `[T2Space P] [T2Space Q]`, the disjoint-open-neighborhood
  condition for distinct points.
- Total disconnectedness is `[TotallyDisconnectedSpace P]` and
  `[TotallyDisconnectedSpace Q]`. Mathlib's definition makes each preconnected
  subset a subsingleton, equivalent to the node's statement for connected
  subsets (nonempty preconnected subsets are connected; the empty case is
  automatically a subsingleton).
- The specified continuous function is `{h : P → Q} (hh : Continuous h)`.
- `Clop(Z)` is Mathlib's `TopologicalSpace.Clopens Z`, whose carrier is a set
  with `IsClopen`, meaning closed and open.
- Bijectivity of inverse image is exactly `hclop : Function.Bijective` applied
  to `fun V : TopologicalSpace.Clopens Q ↦
  (⟨h ⁻¹' (V : Set Q), V.isClopen.preimage hh⟩ : TopologicalSpace.Clopens P)`.
  This uses the actual inverse image of the given h and Mathlib's continuity
  lemma for its clopen proof. It is not an arbitrary Boolean-algebra map.
- Injectivity is the first conjunct, `Function.Injective h`.
- Surjectivity is the second conjunct, `Function.Surjective h`.
- For every clopen U in P, `∀ U : TopologicalSpace.Clopens P` quantifies over
  exactly those subsets. `IsClopen (h '' (U : Set P))` states that its image is
  clopen, and `h ⁻¹' (h '' (U : Set P)) = (U : Set P)` states that this image
  has the required inverse image.
- Uniqueness is the remaining universally quantified clause: for every target
  clopen V, `h ⁻¹' (V : Set Q) = (U : Set P) →
  (V : Set Q) = h '' (U : Set P)`. Thus h(U) itself, rather than an unspecified
  chosen clopen, is the unique target clopen with inverse image U.
- Openness is the last conjunct, `IsOpenMap h`. Its Mathlib definition is
  `∀ O : Set P, IsOpen O → IsOpen (h '' O)`, verbatim the node's final clause.
- Empty spaces are admitted: there is no `Nonempty`, `Inhabited`, point, or
  nonempty clopen binder anywhere in the signature.

Dependency declarations and imports:

- `def-weil-size-convention` has `lean.convention = true` and null module and
  declaration. Its note instructs citers to supply their universe binders
  directly; it requires no Lean import. The recorded upstream derived-category
  audit is not used in this topology statement.
- The proof dependency `lem-weil-pbc-profinite-clopen-basis` is a Mathlib leaf
  whose `mathlib_match` is `isTopologicalBasis_isClopen` in
  `Mathlib.Topology.Separation.Profinite`. I read its full signature with the
  section binders `[T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]`,
  its proof and the adjacent pointwise theorem and docstring
  `compact_exists_isClopen_in_isOpen`. Its module is imported as a plain proof
  import, following the visibility rule.
- Public imports `Mathlib.Topology.Connected.TotallyDisconnected` and
  `Mathlib.Topology.Sets.Closeds` expose the statement's space classes and
  bundled clopen subsets. `TopologicalSpace.Clopens`,
  `TopologicalSpace.Clopens.isClopen`, `IsClopen.preimage`, `Continuous` and
  `IsOpenMap` are the existing Mathlib notions, with no private copies.

Edge cases checked before writing:

- P and Q both empty: each clopen collection has one element, and all
  conclusions hold, including the image and inverse-image identities.
- P empty and Q nonempty: clopen pullback cannot be injective because bottom
  and top in Q are different and have the same empty inverse image.
- Q empty: existence of h forces P empty, so there is no excluded case.
- Constant map from a two-point discrete space to a singleton: inverse image
  cannot be surjective on clopens, as the singleton clopens in P are missing.
- Inclusion of a singleton into a two-point discrete space: inverse image
  cannot be injective on clopens, so no false surjectivity consequence occurs.
- Finite discrete bijections, the identity, empty U, full U, and empty open O
  satisfy all clauses. In the surjectivity proof the finite cover may be
  empty; in the openness proof the union may be empty.

Searches for an existing statement (the required msearch wrapper, plus direct
project-source searches):

- LeanFinder query: `A continuous map between compact Hausdorff totally
  disconnected spaces with bijective pullback on clopen subsets is bijective
  and open`. Eight hits: `LightProfinite.isIso_of_bijective`,
  `LightProfinite.isoOfBijective`, `CompHausLike.isoOfBijective`,
  `CompHausLike.isIso_of_bijective`,
  `CompactT2.ExtremallyDisconnected.projective`,
  `ExtremallyDisconnected.homeoCompactToT2`, `Stonean.effectiveEpi_tfae`, and
  `Stonean.instProjective`. None derives pointwise bijectivity from the
  clopen-pullback hypothesis; the Stonean statements use stronger hypotheses.
- LeanSearch query: `A continuous map of profinite spaces with bijective inverse
  image on clopen subsets is bijective and open`. Eight hits, including
  `IsHomeomorph.mk`, `IsOpenMap.of_inverse`,
  `TopCat.isIso_of_bijective_of_isOpenMap`,
  `TopCat.isIso_of_bijective_of_isClosedMap`, and
  `Equiv.toHomeomorphOfContinuousOpen`. Their signatures already assume
  pointwise bijectivity, openness or an inverse. No exact match.
- Loogle query `Clopens.comap, Function.Bijective`: no hits, unknown identifier
  `Clopens.comap`. Source inspection confirms the pinned Clopens namespace
  has no comap operation, so the statement uses its ordinary constructor.
- Loogle query `"IsClopen", "Bijective"`: zero hits, no exact match.
- Mathlib grep query
  `(clopen|Clopens).*(bijective|injective|surjective)|(bijective|injective|surjective).*(clopen|Clopens)`
  in `Topology`: seven hits, in `ClopenBox.lean`, `DiscreteQuotient.lean` and
  `Connected/Clopen.lean`; these concern finite clopen-box unions, encoding
  discrete quotients, or splitting a space into clopen pieces. No criterion.
- Direct `rg` of that pattern over `lean/WeilConjectures` and `lean/Sheaf`:
  algebraic idempotent and coefficient results are specialized to other
  objects. The nearest result is
  `isHomeomorph_connectedComponentsMap_of_bijective_clopen_preimage` in
  `Sheaf.Topology.SpectralSpace.ClopenComponentHomeomorphism`; I read its full
  signature and docstring. It concerns the induced map on component quotients
  of spectral spaces, and does not state this assertion for a given map P → Q
  with the explicit clopen-image/uniqueness conclusions. The other hits in
  `CondensedPointBasis` and `CondensedHenselianLisseRigidity` only discuss a
  similar argument in docstrings of different theorems.
- `grep -rn` of the item id over `lean/WeilConjectures`: no matches.
- `rg` of the new declaration name over Mathlib, both Lean roots, and
  `dag/lean_names_upstream.json`: no matches.
- Read `Mathlib/Topology/Sets/Closeds.lean`, Clopens section, and
  `Mathlib/Topology/Separation/Profinite.lean` to verify the pinned interfaces.

No statement dispute or node fault was found.

Validation: the required scompile.py invocation compiled the sandbox and library
module separately on the server, cleanly (15.0 s and 10.0 s respectively), with
no error or warning. All Lean lines are at most 100 characters. Every universe
and variable is explicitly bound. The node's signature is copied verbatim from
the theorem keyword to immediately before `:=`.

## Second reading by NU

Author's rereading, not an independent review: I reopened the node and module,
matched each hypothesis and conclusion as listed above, and checked that the
three image clauses express that h(U) itself is the unique target clopen with
inverse image U. The conjunction groups both pointwise properties, the full
clopen assertion, and openness; no clause or empty-space case is lost. The
only postponed proof is the item's named theorem. No mismatch required a
change. The maintainer supplies the independent review under the direct-delivery
workflow; no other agent was started.
