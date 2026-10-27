## Worker report

The module `Sheaf.AlgebraicGeometry.LocallyIndEtaleBaseChangeCharts` states
`AlgebraicGeometry.locally_indEtale_base_change_charts`, with its sole proof `sorry`.
The node is unchanged except for `lean`. There are no new nodes, dependency repairs,
or statement corrections. The source places read were schemes.tex,
lemma-open-fibre-product (01JR), lemma-fibre-product-affine-schemes (01I4),
lemma-fibre-product-affines (01JQ), lemma-basis-affine-opens (01IT), and proetale.tex,
lemma-base-change-ind-etale (097J); their labels were checked in tags/tags.

An affine open presentation `V = Spec B ⊂ T` is encoded by an open immersion
`iV : Spec B ⟶ T`; its open subset is `iV.opensRange`. This retains arbitrary fixed
presentations, rather than replacing the chosen rings with rings of global sections.
The analogous convention applies to U and W. Open immersions identify their source
with the corresponding open subscheme, so this is the node's chart datum.

Hypothesis and clause correspondence:

- The morphism of schemes is `{T S S' : Scheme.{u}} (u : T ⟶ S)`. The universe u
  is arbitrary; all chart rings lie in the same universe as their spectra.
- The pointwise local affine chart hypothesis is `hu : ∀ x : T, ∃ A B f iV iU, …`.
  The two `IsOpenImmersion` conjuncts express affine opens, `x ∈ Set.range iV`
  expresses the neighbourhood condition, and `Spec.map f ≫ iU = iV ≫ u` says
  that u restricted to V is the map induced by the specified ring map f. In
  particular it expresses u(V) ⊂ U. Conversely any such chart inclusion factors
  uniquely through U, and full faithfulness of Spec gives exactly this f.
  `RingHom.IndEtaleAcrossUniverses f.hom` is the recorded ind-etale predicate.
- The arbitrary base change is `(g : S' ⟶ S)`, with no hypotheses on g or on
  the ambient schemes. The new scheme is `pullback u g`; p and q are
  `pullback.fst u g` and `pullback.snd u g`.
- The first conclusion quantifies over every point x', every A, B, C and their
  commutative ring and A-algebra structures, and every open immersion iV, iU, iW.
  Its two commutative-square hypotheses say that the chart maps are induced by
  `algebraMap A B` and `algebraMap A C`. The second square is exactly the condition
  W ⊂ g⁻¹(U) together with its induced ring map. These are chart data, not
  additional geometric assumptions. Every ring homomorphism gives the indicated
  algebra structure, so no chosen presentation is excluded.
- The two membership premises are p(x') ∈ V and q(x') ∈ W; the ind-etale premise
  selects the pairs V,U stipulated in the node. The resulting membership conjunct
  is x' ∈ V', where V' is literally the infimum of the two inverse-image opens.
- The `∃! e` supplies and canonically characterizes the isomorphism from
  `V'.toScheme` to the pullback of the two affine chart maps over `Spec A`.
  The second isomorphism in the node's chain is the actual existing construction
  `pullbackSpecIso A B C`; the composite is `e ≪≫ pullbackSpecIso A B C`.
- The two equations in the unique-existence predicate identify the composite
  isomorphism followed by Spec of `Algebra.TensorProduct.includeLeftRingHom`,
  respectively `Algebra.TensorProduct.includeRight.toRingHom`, and then iV or iW,
  with `V'.ι ≫ p`, respectively `V'.ι ≫ q`. These ring maps are exactly
  b ↦ b ⊗ 1 and c ↦ 1 ⊗ c. Because iV and iW are monomorphisms, the equations
  characterize both projections into the affine chart pullback and hence e
  uniquely. They therefore encode canonicity relative to the fixed presentations.
- The remaining conjunct in the chart conclusion asserts ind-etaleness of exactly
  `includeRight.toRingHom : C →+* B ⊗[A] C`, the ring map for q.
- The final conclusion repeats the full local chart condition for q: at every x'
  there are rings C,D, a ring map f, open immersions from Spec D into the pullback
  and Spec C into S', membership in the source chart, the commuting square with q,
  and ind-etaleness of f. It is the same condition as hu with the schemes changed.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map` (def-pc-scheme and def-weil-affine-spectrum).
  Also read `Spec.homEquiv` in GammaSpecAdjunction for the equivalence between
  the chosen structure maps and the chart-factorization formulation.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`
  and `Scheme.Hom.opensRange` (def-weil-open-immersion).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd` (def-pc-fibre-product); scheme pullback existence
  and `pullbackSpecIso`, including both projection signatures, were read in
  `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Sheaf.RingTheory.IndEtaleUniverseTransport`: `RingHom.IndEtaleAcrossUniverses`
  (def-weil-pbc-ind-etale-algebra), the canonical ULift transport of the existing
  filtered-colimit predicate. Its definition, and upstream `Algebra.IndEtale`,
  were read; no second ind-etale notion is introduced.
- The already stated proof dependency `RingHom.indEtale_principalZariski_stability`
  is imported from `Sheaf.RingTheory.IndEtaleStability`. The other proof dependencies
  are the recorded Mathlib matches: `Scheme.isBasis_affineOpens` (AffineScheme),
  `pullbackSpecIso` (Pullbacks), `Scheme.pullback_map_isOpenImmersion` (Pullbacks),
  and `Scheme.Pullback.range_map` (PullbackCarrier). Their full signatures and
  adjacent source explanations were read. The latter two modules needed only for
  the proof are plain imports; definitions in the statement are public imports.

Edge cases checked: T' empty gives vacuous pointwise conclusions. The zero ring
and a zero tensor product are allowed: there is no Nontrivial assumption; any
impossible point-membership premise simply has no witness. The identity base
change is included, as is an arbitrary nonaffine or nonseparated S'. All affine
assumptions concern only the three chart sources. Tensor order is B ⊗[A] C, and
it is the C-map, not the B-map, that is asserted ind-etale after base change.
The full local hypothesis is not made into a stronger global affine condition.
No false-statement or ambiguity fault was found.

Searches actually run:

- msearch.py leanfinder: `Locally ind etale scheme morphisms have tensor product
  affine charts after arbitrary base change`. Eight hits, including IsEtale
  base-change stability, Algebra.Etale.baseChange, and formal-etale tensor
  stability; none states the local ind-etale chart theorem or its projections.
- msearch.py loogle: `AlgebraicGeometry.pullbackSpecIso, RingHom.IndEtale`.
  Zero hits; the service reports unknown identifier RingHom.IndEtale (the
  predicate is project-specific). This is not treated as evidence it is absent
  from the project.
- msearch.py grep: `IndEtale|ind.etale|locallyIndEtale`, in Mathlib/AlgebraicGeometry:
  zero hits.
- rg over lean/WeilConjectures and lean/Sheaf for ind-etale/chart names located
  strict-henselization and root-splitting chart results, not this arbitrary
  scheme-base-change statement. A narrower search for `locallyIndEtale`,
  `locally_indEtale`, `indEtale.*chart`, `ind_etale.*chart` confirmed those are
  specialized results. The item's id has no hit in lean/WeilConjectures.
- The proposed theorem name was searched in dag/lean_names_upstream.json,
  Mathlib, WeilConjectures and Sheaf; no collision was found.

Validation: scompile.py compiled the final module as sandbox and library modules
in 2.0 and 2.2 seconds respectively, without errors or unexpected warnings.
`set_option autoImplicit false` binds all variables explicitly. The file contains
one theorem with proof `sorry`, no new definitions or local notation, and all
lines are at most 100 characters.

## Second reading by Q39

Author's separate second pass, not an independent review (the maintainer supplies
that review). Re-read the node against the final signature: hu is the original
pointwise hypothesis, the first conclusion ranges over arbitrary chosen compatible
charts, V' is the exact intersection, e retains the intermediate fibre product,
`pullbackSpecIso` supplies the tensor isomorphism, both projection equations have
the correct directions, includeRight is the ind-etale map, and the last conclusion
is the entire local condition for q. No clause or ambient finiteness condition was
added or omitted. The first compiler pass required opening tensor-product notation;
the next required explicit Scheme annotations on point binders for the pullback,
because otherwise elaboration tried the category of types. These are elaboration
repairs and do not restrict the statement. No node changes were needed.
