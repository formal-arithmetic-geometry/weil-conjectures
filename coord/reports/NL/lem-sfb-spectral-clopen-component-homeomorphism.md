## Worker report

The module `Sheaf.Topology.SpectralSpace.ClopenComponentHomeomorphism` states
`isHomeomorph_connectedComponentsMap_of_bijective_clopen_preimage`, with its sole proof
`sorry`. It introduces no new definitions, helper nodes, or dependency modules. The original
node is unchanged except for its `lean` field. There are no statement disputes or corrections.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The spaces T and S are `{T : Type u} {S : Type v}` with `[TopologicalSpace T]` and
  `[TopologicalSpace S]`. Independent explicitly declared universes preserve all size cases.
- The spectral hypotheses are `[SpectralSpace T] [SpectralSpace S]`, precisely the recorded
  Mathlib declaration of `def-weil-spectral-space`. These include compactness,
  quasi-separatedness, a compact-open basis, and sobriety (T0 plus quasi-sobriety).
- The continuous map is `{f : T → S} (hf : Continuous f)`. No spectral-map, open-map,
  surjectivity, or injectivity hypothesis on f is imposed.
- `Clop(Z)` is Mathlib's `TopologicalSpace.Clopens Z`, whose carrier is a subset of Z and
  whose field `isClopen'` asserts it is closed and open. The hypothesis `hclop` says
  `Function.Bijective` of the function taking U to
  `(⟨f ⁻¹' (U : Set S), U.isClopen.preimage hf⟩ : TopologicalSpace.Clopens T)`.
  Thus both injectivity and surjectivity refer to the exact inverse-image function of
  the node, with no choice or substitute map.
- `π₀(Z)` is Mathlib's `ConnectedComponents Z`: the quotient by equality of connected
  components, endowed with its quotient topology. The node's q_Z is `ConnectedComponents.mk`.
- The canonical component map is the existing `hf.connectedComponentsMap`. Its defining
  quotient lift and `Continuous.connectedComponentsMap_mk` send the class of t to that
  of f(t), exactly as the node specifies.
- The first conclusion `IsHomeomorph hf.connectedComponentsMap` says that this concrete
  map is a homeomorphism; Mathlib's predicate combines continuity, openness, and bijectivity,
  and supplies a bundled homeomorphism with that underlying function.
- The second conclusion is the exact function equality
  `hf.connectedComponentsMap ∘ (ConnectedComponents.mk : T → ConnectedComponents T) =
  (ConnectedComponents.mk : S → ConnectedComponents S) ∘ f`.
  This is the normalization `π₀(f) q_T = q_S f`, explicitly retained despite its being
  built into Mathlib's component-map construction.
- Empty spaces are allowed: there is no `Nonempty` or `Inhabited` binder on either space.

Declarations and sources read:

- Statement dependency `def-weil-spectral-space`: `SpectralSpace` in
  `Mathlib.Topology.Spectral.Basic`, lines 33–39, with its full class signature and docstring.
- `ConnectedComponents`, `ConnectedComponents.mk`, its quotient topology instance, and
  `ConnectedComponents.isQuotientMap_coe` in `Mathlib.Topology.Connected.Clopen`, lines
  502–546; `Continuous.connectedComponentsMap`, `Continuous.connectedComponentsMap_mk`,
  and its continuity in `Mathlib.Topology.Connected.TotallyDisconnected`, lines 291–304.
- `TopologicalSpace.Clopens` and `TopologicalSpace.Clopens.isClopen` in
  `Mathlib.Topology.Sets.Closeds`, lines 305–324; `IsClopen.preimage` in
  `Mathlib.Topology.Clopen`, lines 90–92.
- `IsHomeomorph` and `IsHomeomorph.homeomorph` in `Mathlib.Topology.Homeomorph.Defs`,
  lines 501–530.
- Proof dependency `lem-pe-spectral-components-profinite`:
  `spectralSpace_connectedComponents_profinite` in
  `Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite`; full signature and
  six-paragraph proof docstring read. Imported without `public` for the stage-3 proof plan.
- Proof dependency `lem-weil-pbc-profinite-clopen-basis` is a Mathlib leaf, recorded by
  `mathlib_match`: `isTopologicalBasis_isClopen`, `Mathlib.Topology.Separation.Profinite`,
  line 66, with `compact_exists_isClopen_in_isOpen` at line 76. The standing assumptions
  at line 43 are compactness, Hausdorffness, and total disconnectedness. Imported without
  `public` for the stage-3 proof plan.
- Read `literature/stacks-project/topology.tex`: Tag 005F,
  `lemma-connected-component-intersection` (line 1816); Tag 08ZZ,
  `lemma-profinite-refine-open-covering` (line 4207); Tag 0900,
  `lemma-pi0-profinite` and its clopen-saturation proof (line 4232); and Tag 0906,
  `lemma-spectral-pi0` (line 4561). The item is correctly attributed to an agent
  consequence rather than a verbatim Stacks theorem. The declaration docstring gives
  all six steps of the node's proof, with both proof dependencies named.

Edge cases checked before writing:

- Both spaces empty: both clopen types have one element and both quotient spaces are empty;
  the map and normalization have the asserted interpretation.
- T empty, S nonempty: the distinct clopens empty and univ of S have the same preimage,
  so the bijectivity assumption fails. The proof's finite-cover argument permits an empty
  finite subcover and does not select a source point.
- T nonempty, S empty: a map f cannot exist, without adding any nonemptiness assumption.
- Both spaces nonempty and connected: both clopen types have two elements and both
  component quotients have one point. For example a point mapping into the Sierpinski
  spectral space satisfies the criterion even though f itself is not a homeomorphism;
  the conclusion is correctly about the component map.
- A point mapping into two discrete points: inverse image is not injective on clopens.
  Two discrete points mapping to one point: inverse image is not surjective on clopens.
  Thus neither injectivity nor surjectivity in `hclop` can be discarded.
- Components need not be open, finite, or enumerable. Only the actual quotient topology
  and the supplied clopen criterion appear in the signature.

Searches actually run (msearch.py, group NL, this item):

- LeanFinder: `A continuous map of spectral spaces bijective on clopen inverse images
  induces a homeomorphism of connected component spaces`. Eight hits, including
  `CompHaus.toProfinite_obj'`, `LightProfinite.isoOfBijective`,
  `irreducibleComponentsEquivOfIsPreirreducibleFiber`, `Profinite.toCompHausEquivalence`,
  the CompHausLike iso/homeomorphism conversions, and `Homeomorph.image_connectedComponentIn`.
  None is the clopen inverse-image criterion for spectral component spaces.
- Loogle: `"IsClopen", "ConnectedComponents"`. Six hits: the two equivalences for clopen
  decompositions, their three mk evaluation identities, and
  `ConnectedComponents.exists_fun_isClopen_of_infinite`. No matching theorem.
- Grep: `(clopen|Clopen|Clopens).*(bijective|Bijective|homeomorph|Homeomorph)` in Topology.
  The search wrapper returned zero hits. Direct local rg searches supplemented it.
- LeanSearch: `A continuous map of spectral spaces bijective on clopen inverse images
  induces a homeomorphism on connected component spaces`. Eight hits, including
  `Continuous.connectedComponentsMap`, its continuity, `Continuous.mapsTo_connectedComponent`,
  the quotient projection's continuity, `Equiv.toHomeomorphOfContinuousOpen`, and
  prime-spectrum/CompHausLike homeomorphism conversions. No matching criterion.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for
  `clopen.*(biject|homeomorph)|Clopen.*(Biject|Homeomorph)|connectedComponentsMap`.
  Found uses of the canonical component map and specialized ring/scheme results, including
  `CondensedHenselianLisseRigidity`, but no theorem with this statement for arbitrary spectral
  spaces. `grep -rn` for this node id in `lean/WeilConjectures` had no hits.
- Direct rg for `Clopens.*(comap|preimage)|(?:comap|preimage).*Clopens` across Mathlib
  Topology and both project roots found no general clopen-preimage function declaration.
  The signature therefore uses the ordinary inverse-image lambda, with the existing
  `IsClopen.preimage` proof, rather than defining another notion.
- Exact proposed declaration-name rg across Mathlib, both project roots, and
  `dag/lean_names_upstream.json` had no hits.

Validation: `scompile.py NL lem-sfb-spectral-clopen-component-homeomorphism` compiled
both its sandbox probe and the actual module successfully (1.2 s each), with no errors
or unexpected warnings. All variables and universes are explicitly bound, and all Lean
lines are at most 100 characters. Only the single theorem has a postponed proof.

## Second reading by NL

I reopened the node and the final Lean file for a separate final reading. This is the
same dispatcher-started worker's rereading: the current brief explicitly forbids starting
another agent, and the maintainer's delivery review supplies the independent review.

The two arbitrary spectral spaces, continuity of f, and bijectivity of the inverse-image
function on the actual clopen types match exactly. In particular the two spaces have
independent universes, the inverse-image direction is S to T, and neither a special
spectral map nor nonempty spaces are required. The quotient types and their topology
are the Mathlib constructions read above. `hf.connectedComponentsMap` uses f, rather than
an arbitrary component bijection; the explicit composition equality retains the node's
normalization. `IsHomeomorph` asserts the full topological conclusion. Rechecked the
empty-source finite-cover argument, connected case, and two finite discrete countertests.
No mismatch was found and no statement correction, extra node, or dependency repair
was needed. Compared the copied JSON with its base: only `lean` is changed, and its
signature is copied verbatim from the theorem keyword through the conclusion before `:=`.
