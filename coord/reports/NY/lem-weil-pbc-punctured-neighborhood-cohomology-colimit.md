## Worker report

The main module `Sheaf.Topology.PuncturedNeighborhoodCohomologyColimit` states
`TopCat.puncturedNeighborhoodCohomology_colimit`. Its proof is `sorry`. No statement
correction was required. The source is Stacks, Cohomology, Tag 0A3D (2), read in
`literature/stacks-project/cohomology.tex`, including its proof via Tag 0A37.

Hypothesis and clause correspondence:

- A spectral topological space T: `{T : Type u} [TopologicalSpace T] [SpectralSpace T]`.
  This is the recorded Mathlib definition, including compactness, quasi-separatedness,
  sobriety and the compact-open basis.
- A closed subset Z: `(Z : Set T) (hZ : IsClosed Z)`.
- Its quasi-compact open complement: `(hU : IsCompact Zᶜ)`; openness is
  `hZ.isOpen_compl`, used to form the open complement in the diagram.
- An arbitrary abelian sheaf A: the binder
  `A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}`.
- Every integer p >= 0: `(p : ℕ)`; this includes degree zero.
- W consists of points whose singleton closure meets Z, and S = W minus Z:
  `puncturedGeneralizations Z` is exactly
  `{t | (closure ({t} : Set T) ∩ Z).Nonempty ∧ t ∉ Z}`.
  All spaces used for subsets carry the induced subtype topology. There is no replacement
  of W by Z, its closure, or its complement.
- The neighborhood index is `compactOpenNeighborhoods Z`, the subtype of `Opens T`
  satisfying `Z ⊆ N ∧ IsCompact (N : Set T)`. Its opposite category orders it by
  reverse inclusion, just as in the node. It lives in the space's universe.
- Nonemptiness and directedness are expressed by
  `IsFiltered (compactOpenNeighborhoods Z)ᵒᵖ`. The category is a poset, so the
  parallel-arrow condition is automatic. The intended witness is T and the common
  upper bound in reverse inclusion is intersection, as in the node's proof.
- The term at N is `(puncturedNeighborhoodCohomologyDiagram Z hZ A p).obj (op N)`.
  The diagram is the composite of `N ↦ N ⊓ ⟨Zᶜ,hZ.isOpen_compl⟩` with
  `A.cohomologyPresheaf p`. Thus its value is the recorded `Sheaf.H' A p (N \ Z)`:
  cohomology over the open object, i.e. of the inverse-image restriction of A to
  that open. It is not the cohomology of an unrelated supplied diagram. Its maps
  are precisely `cohomologyPresheaf.map` for inclusions of these opens.
- The target is `Sheaf.H'` at the top open of the sheaf obtained by constructed
  inverse image along `puncturedGeneralizationsInclusion Z : S ⟶ T`. This uses
  `Functor.sheafPullbackConstruction.sheafPullback`, the sheafification of presheaf
  inverse image, as specified in the dependency's Mathlib match.
- The canonical restriction leg is `puncturedNeighborhoodCohomologyLeg`: canonical
  cohomology pullback along S -> T over N \ Z, then the cohomology-presheaf
  restriction to all S. The latter inclusion is named by
  `puncturedGeneralizations_le_preimage`. The family of cohomology pullbacks is
  chosen using the existing existence theorem with the existing unique normalization
  property; the existing uniqueness theorem determines the family uniquely.
- The conclusion is `IsIso (colimit.desc D c)` for this actual diagram D and this
  actual canonical restriction cocone c. It specifies the canonical comparison,
  not merely an unspecified abstract isomorphism of the two groups.

Recorded dependency declarations used:

- `Mathlib.Topology.Spectral.Basic`: `SpectralSpace` (the full class was read).
- `Mathlib.Topology.Sheaves.Functors`: `TopCat.Sheaf.pullback`,
  `TopCat.Sheaf.pullbackPushforwardAdjunction`, `TopCat.Sheaf.pushforward`; its recorded
  match `Mathlib.CategoryTheory.Sites.Pullback` supplies the constructed inverse image
  and its unit-compatible adjunction. The construction and signatures were read.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: `CategoryTheory.Sheaf.H'`
  and `CategoryTheory.Sheaf.cohomologyPresheaf`, read in full. This is exactly the
  record for `def-sc-topological-abelian-cohomology`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colimit.desc`, and `Cocone`;
  filteredness uses `CategoryTheory.IsFiltered` from `Filtered.Basic`.
- `Sheaf.Topology.SpectralDirectedLimit`: `Topology.spectralSpace_directedLimit`;
  its full signature and proof docstring were read. It is a non-public proof import.
- The other non-elementary proof dependency `lem-weil-pbc-spectral-limit-cohomology`
  has no Lean record or module yet, so there is no proof import for it.
- The new canonical-pullback module uses the existing `SiteCohomologyFamily` and
  `SiteCohomologyFamily.IsPullback` from
  `Sheaf.CategoryTheory.SiteCohomologyPullbackData`, together with
  `siteCohomology_pullback_exists` and `siteCohomology_pullback_unique` from their
  recorded modules. Their full signatures, normalization and construction were read.
  Additivity is obtained by applying Mathlib's finite-product-preservation theorem;
  the left-adjoint instance is taken directly from the recorded adjunction.

Edge cases were checked before writing: Z empty gives S empty, and the empty open
is an available terminal neighborhood in the reverse-inclusion diagram. Z = T gives
empty punctures and S empty. The empty space, zero sheaf, and p = 0 are included.
No nonempty-space hypothesis, positive-degree restriction, extra separation property,
constructibility assumption, or Noetherian condition was added. The source assumes
constructibility in its general subset version; a closed subset with quasi-compact
open complement in a spectral space has that property, as explained by the node.

Searches: `msearch.py` LeanFinder queried the statement in words, yielding only
skyscraper/condensed colimit results; none is this theorem. Loogle queried
`CategoryTheory.Sheaf.H, TopCat.Sheaf.pullback`, with zero hits. An initial mistyped
Loogle query reported an unknown identifier and was replaced by that valid query.
Mathlib grep for `(punctured|neighbou?rhood).*(cohomology|functorH)` and its reverse
returned zero hits. LeanSearch reported unavailable (Internal Server Error), which
is recorded as unavailable, not as a negative search. Separate Mathlib searches for
both new notions are reproduced verbatim in the new nodes' `mathlib_searches`.
`rg` of `WeilConjectures` and `lean/Sheaf` for punctured cohomology, generalization
cohomology, neighborhood diagrams, and the proposed declaration names found no
existing construction. A blueprint-id grep in upstream found no match. DAG grep and
`tools/blueprint_refs.py search punctured` found the present continuity theorem and
unrelated punctured-scheme results, not its diagram definition.
`blueprint_refs.py search 'cohomology pullback'` found scheme/module cohomology
statements; broader DAG reading located the site-cohomology family and its existence
and uniqueness nodes, which are reused rather than restated. Existing scheme etale
or structure-module pullback maps have different sites/coefficient categories.

No STATEMENT-DISPUTED flag or source fault was found. All new theorem bodies are
`sorry`. The two supporting theorems in the diagram module are named proof
obligations of its construction, with sources and full natural-language proofs.
There is no sorry-valued data and no alternative cohomology definition.

## New nodes

`def-weil-pbc-topological-object-cohomology-pullback`, module
`Sheaf.Topology.CanonicalCohomologyPullback`, supplies the actual canonical family of
pullback maps for continuous maps, specializing the existing site-cohomology interface.
It chooses the family characterized by naturality, boundary compatibility and unit
normalization; the cited uniqueness theorem determines its data. This is the standard
construction of Tags 01F8/01FB. It adds no new existence or uniqueness theorem.
The two instance declarations are direct constructions from existing Mathlib theorems.
Searches found the inverse-image functors and the general site's existence/uniqueness
statements but no named topological family of maps. Full query outputs are in the node;
local project and DAG searches are documented above. In particular, it does not copy
`SiteCohomologyFamily`, its normalization predicate, or the inverse-image functor.

`def-weil-pbc-punctured-neighborhood-cohomology-diagram`, module
`Sheaf.Topology.PuncturedNeighborhoodCohomologyDiagram`, gives the neighborhood index,
the punctured generalization subset and its inclusion, the monotone puncture assignment,
the cohomology diagram and its canonical restriction cocone. This is the concrete diagram
in Tag 0A3D (2). Searches found neither a node defining it nor a Mathlib/project diagram;
the skyscraper cocones are different objects. Its definition contains only actual
constructions. The named theorems `puncturedGeneralizations_le_preimage` and
`puncturedNeighborhoodCohomologyLeg_naturality` postpone only the proofs needed to
type the restriction and cocone; their statements determine proof objects uniquely.
The original item's `stmt_deps` gains this new definition node, which in turn cites
the canonical-pullback definition. All other original-node fields are unchanged.


## Second reading by NY

I independently read the item, all three delivered modules, both new definition
nodes, the recorded dependency signatures, and Stacks cohomology.tex at
lemma-cohomology-of-neighbourhoods-of-closed (0A3D), lemma-colimit (0A37)
with its preceding setup, and lemma-functoriality/remark-explain-arrow
(01F8/01FB). No mathematical or Lean statement mismatch was found. The Lean
and node statements are retained; this second reading adds the independent
review and search record only.

Object, hypothesis and conclusion checklist, made from the node:

- Ambient spectral space T: `{T : Type u} [TopologicalSpace T]
  [SpectralSpace T]`. Read Mathlib's class: T0, compact, quasi-sober,
  quasi-separated and prespectral give precisely the node's compactness,
  sobriety and compact-open basis. Verdict: exact.
- Closed Z and quasi-compact open complement U: `(Z : Set T)
  (hZ : IsClosed Z) (hU : IsCompact Zᶜ)`. The complement open is
  `⟨Zᶜ, hZ.isOpen_compl⟩`, with no additional hypothesis. Source 0A3D
  assumes quasi-compact E and, in part (2), constructibility. Closed Z
  is compact in compact T; its compact open complement makes Z
  constructible. Thus this is exactly the node's stated specialization.
- Arbitrary abelian sheaf A: `CategoryTheory.Sheaf
  (Opens.grothendieckTopology T) AddCommGrpCat.{u}`. This uses the
  ordinary open-cover site; no constructibility or finiteness on A.
  Verdict: exact.
- W consists of points specializing into Z, and S is W minus Z:
  `puncturedGeneralizations Z` is literally
  `{t | (closure ({t} : Set T) ∩ Z).Nonempty ∧ t ∉ Z}`.
  Its subtype topology and `puncturedGeneralizationsInclusion` are
  the stated subspace and actual inclusion. W is inlined into S;
  no change of specialization direction. Verdict: exact.
- A restricted to a subspace means inverse image: the target uses
  `sheafPullbackConstruction.sheafPullback (Opens.map inclusion)`.
  Read its definition and adjunction in Mathlib Sites.Pullback: it
  is the left Kan extension followed by sheafification, as the
  inverse-image dependency's mathlib_match specifies. Verdict: exact.
- Degree p ranges over every nonnegative integer: `(p : ℕ)` follows
  the A binder and includes zero. Verdict: exact.
- Neighborhoods N are compact open and contain Z:
  `compactOpenNeighborhoods Z` is the subtype of `Opens T` with
  `Z ⊆ N ∧ IsCompact (N : Set T)`. Its opposite category gives
  reverse inclusion. `IsFiltered ...ᵒᵖ` states both nonemptiness
  and directedness; parallel arrows are unique in this poset.
  Verdict: exact, including the final sentence of the node.
- Diagram groups are H^p(N minus Z,A restricted there):
  `puncturedNeighborhoodOpen` is intersection with the complement,
  and `puncturedNeighborhoodCohomologyDiagram` composes its opposite
  functor with `A.cohomologyPresheaf p`. Read Mathlib's H' and the
  presheaf definition: these are Ext from the free abelian sheaf
  on each open, precisely the recorded object-cohomology encoding.
  Inclusions give ordinary restriction transitions. Verdict: exact.
- Target is H^p(S,A restricted to S): the cocone vertex is H' of
  the constructed inverse image at the top open of S. Verdict: exact.
- Comparison is induced by canonical restrictions: each leg first
  applies `objectCohomologyPullback` at N minus Z and then restricts
  from its inverse-image open to the top open using
  `puncturedGeneralizations_le_preimage`. Its naturality theorem
  supplies the compatibility required by `Cocone`. The conclusion
  `IsIso (colimit.desc D c)` therefore specifies this canonical map,
  rather than merely asserting existence of an abstract isomorphism.
  Verdict: exact.

The new canonical-pullback node accurately specializes the existing
SiteCohomologyFamily/IsPullback interface. I read its definition, the
existence theorem and the uniqueness theorem: the unit normalization,
coefficient naturality and connecting-map condition uniquely determine
the family chosen by `Classical.choose`. The choice is not hollow data.
The two instances use the actual adjunction and finite-product
preservation, and add no hypothesis. The new diagram node introduces
exactly its explicit index, subset, diagram and cocone; its proof
obligations postpone proof objects only. Both new nodes have the required
chapter, unit, ancestor/via, searches, creation record, empty proof fields
and lean_audit states. Both are reached by the item's statement dependencies.
No dependency module is delivered. I also read the full
`spectralSpace_directedLimit` signature: the neighborhood construction
supplies its nonempty directed index, spectral inclusions and initial
limit topology. The other continuity proof dependency has no Lean record
and consequently supplies no proof import at this stage.

Edge cases: Z empty permits the empty neighborhood, terminal in the
opposite index; S is empty and that stage has zero cohomology. Z = T
has only the full neighborhood and empty puncture. Empty T, the zero
sheaf, and p = 0 are all admitted. There is no field, ring or
characteristic parameter. All variables/universes are explicitly bound
with autoImplicit false. The neighborhood subtype lies in Type u, so
the colimit is small in the group universe. Any separately sized space
and coefficient sheaf can be placed in their common larger universe;
there is no independent too-small test-object universe. No nonempty
space, Noetherian, separated or positive-degree assumption was added.

Independent duplicate searches: LeanFinder query "Cohomology continuity
on inverse limits of spectral spaces and compact open neighborhoods"
returned eight results about profinite locally constant functions and
condensed spaces, none this statement. Loogle query
`"cohomologyPresheaf"` returned exactly Mathlib's cohomologyPresheaf and
cohomologyPresheafFunctor, which the delivered diagram reuses.
LeanSearch query "Canonical inverse image homomorphism on abelian sheaf
cohomology for a continuous map of topological spaces" returned Internal
Server Error, recorded as unavailable. I searched Mathlib, upstream
WeilConjectures and project Sheaf sources for neighborhood/generization/
generalization cohomology and inverse-image/pullback cohomology, as well
as the proposed names. I opened the nearby
`exists_topological_induced_edge_and_map`: it concerns terminal cohomology
of direct images and an existential transformation, not the normalized
family over every open needed here. Existing strict-local and etale
neighborhood results concern different sites. DAG and blueprint searches
for punctured and cohomology pullback likewise provide no duplicate of
either new construction. The general site-cohomology family is reused,
not duplicated.

All theorem bodies in the delivery are sorry; definitions construct
actual data. Declaration docstrings carry sources and blueprint ids;
the main theorem docstring follows all five proof steps of the node.
The node lean.statement signatures match the module signatures verbatim.
No statement correction or citer reassessment was necessary.
