## Worker report

The module states the complete node in three named theorems, all with `sorry`:
`TopCat.Sheaf.subspace_ring_restriction_unit_coherence`,
`TopCat.Sheaf.subspace_sets_restriction_unit_coherence`, and
`TopCat.Sheaf.subspace_ring_homeomorphism_unit_coherence`.
The seven helper definitions contain actual maps only: subtype inclusions,
adjunction units, presheaf restrictions and the homeomorphism on a subset and its image.
They belong to the canonical-map interface of this same node; no new independent notion
or DAG node is introduced. No statement correction or disputed clause.

Hypotheses and clauses, checked against the whole node:

- `Z : TopCat.{u}` is the arbitrary topological space, `E : Set Z` is an arbitrary
  subset with its induced topology, and `G : Z.Sheaf CommRingCat.{u}` is precisely
  a sheaf of commutative rings. No spectral, open, closed or nonempty hypothesis.
- `subspaceInclusion E` is e, `(pullback _ e).obj G` is G_E, and
  `subspaceSectionMap _ E G V h` is r_V. It is the recorded adjunction unit at V
  followed by the ordinary restriction from e⁻¹(V) to ⊤. For h : E ⊆ V this is
  the canonical identification e⁻¹(V) = E, rather than an arbitrary section map.
- Ordinary restriction to V is Mathlib's existing
  `V.isOpenEmbedding.sheafPullback`, whose presheaf evaluates at the ambient image
  of an open B of V. Its canonical comparison with inverse image is the existing
  `V.isOpenEmbedding.sheafPullbackIso`. The first conjunct of both restriction
  theorems says the unit followed by that comparison equals the actual restriction
  `G.obj.map (V.isOpenEmbedding.isOpenMap.adjunction.counit.app B).op`, on EVERY
  ambient open B. The counit here is inclusion V ∩ B ⊆ B.
- V containing E is `(V : Opens Z) (h : E ⊆ V)` and p_V is `subspaceToOpen E V h`.
  The second conjunct produces the ring-sheaf isomorphism c between p_V⁻¹(G|V)
  and e⁻¹G. Its first equation, quantified over every `B : Opens (TopCat.of V)`,
  is exactly c after the p_V unit equals the e unit on the ambient image of B.
  `subspaceOpenUnit` uses the ordinary presheaf restriction identifying
  e⁻¹(image B) with p_V⁻¹(B). Equality of category morphisms gives equality on
  every section s, with ring homomorphism structure retained.
- The `∀ c'` conjunct asserts uniqueness from this sectionwise equation alone;
  the subsequent global formula is not a hypothesis of uniqueness. That formula
  uses `openRestrictionGlobal`, the identity restriction identifying image(⊤_V)
  with V, followed by the p_V unit and c at ⊤; its value is r_V.
- Nested neighbourhoods are `W V : Opens Z`, `hWV : W ≤ V`, `hEW : E ⊆ W`.
  The last conjunct says ordinary restriction V to W followed by r_W is r_V.
  The transition furnished by the inverse-image unit is ordinary restriction by
  the first conjunct, applied on V to the open W in V. The second conjunct gives
  its subsequent composition comparison to E. Thus both the transition clause
  and its displayed equation are included, without introducing a second map.
- The same three clauses are stated separately for `G : Z.Sheaf (Type u)`.
  The canonical set-composition isomorphism is the one in the recorded
  `exists_sets_inverseImage_comp`; its defining unit equation, together with
  the ordinary open-restriction unit formula, is the equation asserted here.
  The uniqueness clause identifies the choices. We import that exact module.
- Homeomorphism hypotheses are `g : Z ≃ₜ Z'`, the two CommRingCat sheaves G,G',
  and `θ : G' ≅ (pushforward _ (TopCat.isoOfHomeo g).hom).obj G`.
  The image subset is literally `g '' E`; e' is its subtype inclusion, and g_E
  is `subspaceHomeomorphism g E`, implemented by Mathlib `Homeomorph.image`.
- The third theorem produces θE with exactly the source and pushforward target
  specified in the node. Its first equation is the stated unit square on EVERY
  `B' : Opens Z'`. The two inverse-image opens are definitionally identical
  under g_E, so no arbitrary transport is supplied. The `∀ ψ` clause asserts
  uniqueness from that square alone.
- Its final equation, for every V containing E, is the displayed global square:
  r' at g(V), then θE at ⊤, equals θ at g(V), then r_V. The helper
  `homeomorphismOpenSectionMap` only restricts from g⁻¹(g(V)) to V, equal opens
  because g is a homeomorphism. `Set.image_mono h` supplies E' ⊆ g(V).

Dependency declarations read and used:

- def-weil-pbc-topological-inverse-image: Mathlib.Topology.Sheaves.Functors,
  `TopCat.Sheaf.pullback`, `pushforward`, `pullbackPushforwardAdjunction`;
  the unit in every map is this actual adjunction's unit. Read its full source,
  including `pullbackIso`, and the presheaf direct-image/composition declarations.
- lem-weil-pbc-sets-inverse-image-composition:
  Sheaf.Topology.SetsInverseImageComposition, `TopCat.Sheaf.exists_sets_inverseImage_comp`;
  read its full signature, docstring and proof. Its uniqueness applies to each G.
- Proof imports: Mathlib.CategoryTheory.Adjunction.Basic (`Adjunction.comp`),
  Mathlib.CategoryTheory.Adjunction.Mates (`unit_conjugateEquiv_symm`),
  Mathlib.CategoryTheory.Sites.Sheafification (`presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`), Mathlib.CategoryTheory.Limits.HasLimits (`colimit`).
  These give the already-recorded proof-dependency interfaces; no dependency repair.

Sources read: literature/stacks-project/sheaves.tex, lemma-pullback-presheaves
(Tag 008F), lemma-pullback-composition (008I), and
section-presheaves-structures-functorial (008P). Their neighbourhood colimits,
adjunctions and algebraic-structure extension give the node's explicit formulas.

Edge cases: E = ∅ (with arbitrary V), V = ∅ (then necessarily E = ∅), W = ∅,
E = Z, V = W, identity homeomorphism, empty ambient space, and arbitrary non-open
and non-closed subsets. Every construction is point-free or uses a subtype lambda
with no chosen point. Units and ordinary restrictions exist at ∅, whose sheaf
value is the terminal ring or singleton set. There is no Nonempty assumption,
nonzero-ring convention or extra condition on the image subset. The single
universe u accommodates any chosen space and coefficient size by universe lifting;
the interfaces use the same size convention as the recorded dependency.

Searches for an existing statement (2026-10-23):

- msearch.py leanfinder, “Inverse image sheaves on nested subspaces unit agrees
  with open restriction and homeomorphism transport”: eight hits, including
  Scheme.restrictFunctorΓ_inv_app and SheafedSpace.IsOpenImmersion.ofRestrict_invApp;
  these are scheme/ringed-open-immersion formulas, not this arbitrary-subset result.
- msearch.py loogle, “Topology.IsOpenEmbedding.sheafPullbackIso,
  TopCat.Sheaf.pullbackPushforwardAdjunction”: zero hits.
- msearch.py grep, “sheafPullbackIso|unit_leftAdjointUniq|pullbackHomIsoPushforwardInv”
  in Topology/Sheaves: three hits. Read Functors.lean and Presheaf.lean; use the
  existing open comparison, but none states this combined result.
- rg of lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  subspace/restriction units, the item id and sheafPullbackIso: no full match.
  The existing ClosedEmbeddingRestrictionTransport concerns set sheaves with
  different ambient universes and a closed-image application, not this ring statement.
  AlgebraicGeometry.RingedSubspace.subspaceInclusion is restricted to a locally
  ringed space; it does not supply the generic topological-subset interface.
- rg of Mathlib, both project roots and the upstream name index for every helper
  and theorem name found no collision in the TopCat.Sheaf namespace.

Validation: prescribed scompile.py only; no local Lean invocation or global build.
The final module is compiled in both sandbox and library module modes; each theorem
has only `sorry` as its whole proof. No theorem was proved in this delivery.

## Second reading by Q158

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
