## Worker report

The module `Sheaf.Paper.StratifiedOrientedCover` states
`AlgebraicGeometry.StratifiedOrientedCover.stratified_product_coherent_conservative`.
This is the sole postponed theorem, with its six-step natural-language proof in the docstring.
All auxiliary declarations have real data and unpack constructions already specified by this
node; there are no new independent notions, dependency repairs, or statement corrections.
Only the item's `lean` field changes.

Hypothesis and clause correspondence:

- Schemes `X,S` are `{X S : Scheme.{u}}`, with arbitrary explicitly bound `u`; the set universe
  is `max (u + 1) v` with arbitrary `v`, exactly as in the recorded `VanishingTopos.{u, v}`.
- Noetherian `S` is exactly `[IsLocallyNoetherian S] [CompactSpace S]`.
- Finite presentation of `f : X ⟶ S` is `[LocallyOfFinitePresentation f] [QuasiCompact f]
  [QuasiSeparated f]`, as required by the conventions node (Stacks 01TP).
- The finite scheme stratifications are `A : X.FiniteLocallyClosedStratification` and
  `B : S.FiniteLocallyClosedStratification`. Their fields give finite indices `Fin A.n`,
  `Fin B.n`, locally closed strata, covering, pairwise disjointness, domain schemes,
  immersions, their `IsImmersion` proofs and the equality of their ranges with the strata.
  Constructibility is separately retained as `_hA` and `_hB`, each asserting
  `Topology.IsConstructible` for every stratum.
- `Index A B` is `ULift (Fin A.n × Fin B.n)` in the common site universe. This is exactly
  the finite set of pairs, including the empty set. No nonemptiness is assumed.
- `ComponentSite` is the dependency's actual `OrientedProduct.Triples` on the site inverse
  images of `A.immersion a ≫ f` and `B.immersion b`. `componentTopology` is precisely
  `OrientedProduct.topology` with its three generating covering types and the transported
  étale pretopologies. `ComponentTopos` is the category of sheaves of sets on that site.
- `Component` retains `first`, `second`, the direct-image structural `orientation`, and
  `OrientedProduct.IsUniversal` for these projections and that very orientation. Thus its
  structural arrow has direction `j_β p₂ ⇒ (f i_α) p₁` in the convention of the dependency.
- `componentOrientation` transports this arrow to the cone over `f` using the recorded
  `etaleComposition` isomorphism, a functor associator, and the identity right unitor.
  It does not replace the structural arrow by an arbitrary natural transformation.
- `ComponentLift` is the recorded `OrientedNearbyCycles.Lift`: its legs are
  `d.first.comp (etaleMorphism i_α)` and `d.second.comp (etaleMorphism j_β)`, and its arrow is
  exactly `componentOrientation d`. Its `first`, `second` and `compatible` fields identify
  the induced `u_αβ` with this cone, including the orientation equation.
- In `Data`, `component` and `lift` give these data for every pair. The `topology` is on the
  actual sigma category of the component triple sites. The field `coproduct` is the full
  `FiniteCoproductTopos.Witness`, with identity component presentations. Its `topology` field
  fixes componentwise coverings, its `equivalence` is restriction to components, and its
  other fields retain the component inclusions, their adjoints, limits, colimits,
  epimorphisms, the coproduct universal property, independence of presentations,
  componentwise coherence, and the empty-index case.
- `Data.morphism` is `u` with target the dependency's `VanishingTopos f`.
  `component_iso` says `u j_αβ ≅ u_αβ` on direct images.
  `inverse_formula` identifies `u.inverse` under the restriction equivalence with the
  tuple `Functor.pi' (fun k ↦ (lift k).morphism.inverse)`, exactly the node's inverse formula.
  The full coproduct witness supplies uniqueness of this induced morphism.
- `Nonempty (Data f A B)` asserts that the specified constructions exist; hence no
  uninhabited construction hypothesis can make the conclusion vacuous. The second conjunct
  applies to **every** compatible choice `d`, matching the statement's arbitrary universal
  choices. Existential `hE,hF` assert that its source and target are coherent topoi.
  `CoherentToposRepair.IsCoherentGeometricMorphism hE hF d.morphism` is preservation of
  coherent objects; `IsConservativeGeometricMorphism hE hF d.morphism` is reflection of
  isomorphisms of sheaves of sets. No coefficient category or module conservativity replaces
  the stated set-sheaf assertion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, available through the scheme imports.
- `def-weil-pbc-scheme-conventions` has no declaration; its finite-presentation convention is
  rendered by the three Mathlib classes above.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Topology.FiniteLocallyClosedStratification` and
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`.
- `def-weil-constructible-subset` is a Mathlib leaf:
  `Mathlib.Topology.Constructible`, `Topology.IsConstructible`; no `lean` repair is needed.
- `Sheaf.Paper.OrientedNearbyCycles`: `EtaleSite`, `etaleTopology`, `etaleBaseChange`,
  `etaleMorphism`, `VanishingTopos`, `Lift`, `etaleComposition`, and `identity` in namespace
  `AlgebraicGeometry.OrientedNearbyCycles`. The node's primary `nearbyCycles` declaration
  concerns derived coefficients; this item only uses its actual underlying vanishing topos.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`: `CategoryTheory.GeometricMorphism`, `comp`.
- `Sheaf.CategoryTheory.Sites.OrientedProductLargeSites` publicly retains
  `OrientedProduct.Triples`, `topology`, and `IsUniversal` from `OrientedProductUniversal`.
  Here the existing `AsSmall` étale-site transport gives small categories in `u+1`, so
  the original small-category constructors apply without identifying scheme object and
  morphism universes or repairing the recorded large-site interface.
- `Sheaf.CategoryTheory.Sites.CoherentToposRepair`: `IsCoherentTopos`,
  `IsCoherentGeometricMorphism`, `IsConservativeGeometricMorphism`.
- `Sheaf.CategoryTheory.Sites.FiniteCoproductToposCoherent`:
  `CategoryTheory.FiniteCoproductTopos.Witness`, including its entire recorded construction.

The stated proof-dependency modules are imported without `public`: EtaleToposPointsGeometric,
FinitarySiteCoherentGenerators, FinitarySiteEnoughPoints, QcqsOrientedTriplePresentation, and
`WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm`. The last module was absent in
both older local source trees; its full current source was read with `scompile.py --source`.
The remaining permanence inputs are Mathlib leaves available through the scheme imports.
There are no omitted cyclic proof imports.

Edge cases checked before writing: zero strata are allowed for the empty scheme; no stratum
is required to be nonempty or reduced. `Index` has no `Nonempty` instance hypothesis, and the
coproduct witness includes the degenerate empty topos. If only `X` is empty, the target
vanishing topos is degenerate and the point-reflection argument still applies. Nilpotent
stratum structures are allowed: geometric field-valued points kill their defining ideal.
The identity map and one-stratum stratifications are included. There is no field, torsion,
characteristic, separatedness, or reducedness hypothesis. Sites and set values live in
`max (u+1) v`, their sheaf categories one universe higher; the finite index is lifted without
changing its set.

Existing-declaration searches (2026-10-17 UTC):

- `msearch.py leanfinder`, query “Finite constructible stratifications induce a coherent
  conservative geometric morphism from the coproduct of oriented products”: eight hits,
  including `CompHausLike.sigmaComparison` and `AlgebraicGeometry.instFinitaryExtensiveScheme`;
  none states the oriented-topos claim.
- `msearch.py loogle`, query `ReflectsIsomorphisms, Sheaf`: zero hits, diagnostic unknown
  identifier `ReflectsIsomorphisms`. This query supplied no candidate.
- `msearch.py grep`, query `stratified.*conservative|coherent.*oriented`, subdirectory
  `CategoryTheory/Sites`: zero hits.
- `msearch.py leansearch`, query “Finite stratifications give a coherent conservative morphism
  of oriented étale product topoi”: eight hits, including `Scheme.smallEtaleTopology`,
  `Scheme.smallEtalePretopology`, and `CategoryTheory.coherentTopology`; no matching theorem.
- `rg` on the project and upstream Lean trees for stratified/conservative and
  coherent/conservative found the distinct proper-base-change theorem and proof mentions in
  `CoherentSetCriterion`, not this statement. The item-id search of upstream found no match.
  Exact namespace and theorem-name searches of upstream, the project and
  `dag/lean_names_upstream.json` found no collision.

Source verification: the cited author PDF is accessible online at the node's URL. Its §8.1,
printed p. 17 (PDF page 17), explicitly uses the finite disjoint sum of stratum subtopoi and
the corresponding canonical coherent conservative morphism. The node's older “WANTED” note
is therefore historical, not an obstacle to reading this source. No statement fault or
STATEMENT-DISPUTED flag remains.

Validation: prescribed `scompile.py` only, under the default per-file limit. Initial checks
caught and repaired an ambiguous `Equivalence.refl` and a single long line. The final dry run
and delivery repeat compilation and server preflight.

## Second reading by Q17

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix

The delivered module fixed the set universe of the recorded vanishing topos to `u + 1`
(`VanishingTopos.{u, u + 1}`, `etaleTopology.{u, u + 1}`, `Witness.{u + 1, u + 2, u + 2}`),
although `def-trf-oriented-nearby-cycles` and the citer `lem-trf-coherent-set-criterion`
(`coherent_iff_finite_constructible_strata`, stated for `VanishingTopos.{u, v}`, whose proof
step 3 applies this item) work in an arbitrary containing universe `max (u + 1) v`. The fix
binds `universe u v` and replaces every `u + 1` set/site universe by `max (u + 1) v`
(index lift, étale sites, component topoi, `IsUniversal`, `Lift`, the coproduct witness,
the target `VanishingTopos.{u, v} f` and `IsCoherentTopos`). `Index.{u, v}` is written
explicitly so that each auxiliary declaration has exactly the universes `u, v`. Nothing else
changed; the old statement is the instance `v := u + 1`. Compiled clean with `nt_compile.py`.

