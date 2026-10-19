## Worker report

The module `Sheaf.CategoryTheory.DerivedRestrictionBifibrantNerveEquivalence` states
`CategoryTheory.derived_restriction_bifibrant_nerve_equivalence`, with `sorry` as its
only theorem proof. The two real-data helpers construct the specified enriched
restriction and its actual coherent nerve map. No node statement is corrected,
no dependency interface is replaced, and no new independent notion is introduced.

Source read: [Higher Algebra](https://www.math.ias.edu/~lurie/papers/HA.pdf),
section 1.3.4, Theorem 20 and Lemma 21 (printed pp. 117–118), together with
Remark 27 of that section (printed p. 120). The node's agent-extracted enriched comparison
is expanded in all eight steps of the declaration docstring. Its `source.document`
still names HTT, but its source place, proof_origin and actual supporting references
explicitly identify HA; this delivery follows those references without changing
any source metadata.

Hypotheses, matched individually to the node:

- `M N : Type u`, their `Category.{v}` instances, and `ModelCategory` instances
  are the two ordinary categories and their model structures. Mathlib's model
  structure includes lifting and retract/two-out-of-three axioms.
- `HasLimits` and `HasColimits` for each category express completeness and
  cocompleteness required by the model-category convention.
- `_hM` and `_hN : CombinatorialModelCategory.{u,v,w}` express precisely local
  presentability and set-generated model weak factorization systems. This
  existing structure also includes both functorial factorizations. Its set-size
  universe `w` is independent of the morphism universe.
- Both `SimplicialCategory` instances, `_TM`, `_TN : SimplicialTensorCotensor`,
  and `_hSM`, `_hSN : SatisfiesSM7` express enrichment, tensors, cotensors and
  the actual corner-map simplicial model axiom, including the triviality clause.
- `L` and `R` are the given enriched functors. `adj` is their underlying ordinary
  adjunction, using the recorded `simplicialUnderlyingFunctor`. `_enrichedAdj`
  makes its canonical mapping-object map, induced by R and the actual unit, an
  isomorphism. This is the simplicial adjunction convention already used by
  `SimplicialQuillenEquivalence.enriched_adjunction` in the projective dependency.
- `_hL` and `_hLt` say the left adjoint preserves cofibrations and trivial
  cofibrations. Trivial means the conjunction with `WeakEquivalence`.
- `_hEquiv` quantifies over every cofibrant X, fibrant Y and ordinary map
  `L.obj X ⟶ Y`, and gives exactly the iff between weak equivalence of that map
  and weak equivalence of `adj.homEquiv X Y f`, its actual adjunct.
- `Q` is an arbitrary enriched endofunctor. `q` is its ordinary natural map to
  the identity, and `_qEnriched` is naturality on entire enriched mapping objects:
  postcompose `Q.map X Y` with `q_Y` equals precompose with `q_X`. Thus it is
  the enriched natural transformation, not merely pointwise ordinary naturality.
- `_hQ` says separately for every X that QX is cofibrant, q_X is a fibration,
  and q_X is a weak equivalence. This is exactly the specified trivial fibration.
- Universes `u` and `v` are separate bounds for objects and mapping simplices;
  both categories fit these fixed common bounds. `t` enlarges nerves/localizations
  to `max u v t`; `s` independently enlarges the Joyal test universe. No equality
  of object and morphism universes, smallness of the categories, or preservation
  of cofibrant objects by R is required.

Conclusions, matched clause by clause:

- `∃ h : ∀ Y : Bif N, IsCofibrant (Q.obj (R.obj Y.obj)) ∧ IsFibrant ...`
  proves the restriction exists. It is an output, not an assumed preservation
  property. `bifibrantRestriction R Q h` uses exactly these objects and
  `R.map X Y ≫ Q.map (R.obj X) (R.obj Y)` on full mapping objects; its functor
  laws are the existing laws of the composite.
- `DerivedRestriction.nerveMap` postcomposes each actual thickening functor
  with that restricted enriched functor and applies `uliftFunctor`. It is
  not an arbitrary functor or a chosen equivalent map. Its construction retains
  every coherent simplex.
- `IsFunctorEquivalence` gives an inverse with coherent natural inverse
  equivalences for that very nerve map. The next conjunct is exactly the Joyal
  convention: for every quasicategory Z in `max u v t s`, the induced functor
  `h Fun(N_hc(M^cf),Z) ⥤ h Fun(N_hc(N^cf),Z)` is an equivalence. The extra
  universe lift follows the formula in `exists_joyal_model_structure`.
- The final universally quantified conclusion is the phrase "under the
  localization equivalences" made explicit. C,D are arbitrary quasicategorical
  localizations, with actual `qM`, `qN` and full `IsLocalization` universal
  properties. These are not additional assumptions on M or N: the earlier
  localization dependency supplies such presentations. T and tN are any
  ordinary functorial fibrant replacement in N. No enriched fibrant replacement
  is assumed or needed.
- `Nonempty (ReplacementAdjunction adj ... q ... tN qM qN)` explicitly states
  existence of the normalized derived adjunction. For every such A,
  `IsEquivalenceEdge ... A.coherent.unitEdge` and the analogous counit clause
  assert equivalence of its actual coherent unit and counit. The normalizations
  in the imported structure tie these edges to the ordinary adjunction and
  the specified replacements.
- For every inclusion-normalized localization equivalence eM,eN, the maps jM,jN
  satisfy the existing `IsOrdinaryNerveMap` predicate on all strings and the
  two coherent comparison equations with inclusion followed by qM,qN. The
  conclusion `AreNaturallyEquivalent (nerveMap ... ≫ eM) (eN ≫ A.right)` identifies
  the specified QR map with the derived right adjoint. This predicate is an
  equivalence edge in the full internal functor simplicial set; hence it includes
  natural mapping-space maps and composition homotopies, rather than only an
  equivalence of induced ordinary homotopy-category functors. The strict enriched
  map and canonical nerve construction fix the map whose coherent action is compared.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SimplicialModelNerveLocalization`:
  `CategoryTheory.SimplicialModelLocalization.Bif`, `SatisfiesSM7`,
  `IsOrdinaryNerveMap`, `inclusionNerve`, and the theorem
  `CategoryTheory.simplicial_model_nerve_localization`; its comparison and mapping
  presentation definitions were read in full.
- `Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`:
  `HomotopicalAlgebra.ModelInfinity.ReplacementAdjunction`, `CoherentAdjunction`,
  and `quillenAdjunctionInfinityLocalization`. The unit/counit normalization
  fields and full signature were read, including the required universe lifting.
- `Sheaf.CategoryTheory.SimplicialProjectiveModelCalculus`:
  `CategoryTheory.simplicialUnderlyingFunctor` and the enriched adjunction
  convention; the imported canonical `HomotopicalAlgebra.CombinatorialModelCategory`
  is defined in `ModelColimitLocalizationComparison` and was read there.
- `Sheaf.AlgebraicTopology.JoyalModelStructure`:
  `SSet.exists_joyal_model_structure`, especially its lifted homotopy-category
  testing convention.
- Proof imports: `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus` and
  `Sheaf.CategoryTheory.CoherentNerveComparison`. The other three stated proof
  dependencies are already public statement imports. There is no omitted proof import.
- Mathlib: `EnrichedFunctor`, its `comp`, `forget`, and functor laws;
  `SimplicialNerve` with the subset-path thickening; `SSet.hoFunctor` and
  `MonoidalClosed.pre`. The enriched naturality condition is expressed using
  the existing enriched whiskering maps, without a private replacement notion.

Edge cases checked: identity Quillen adjunction; identity Q when all objects are
cofibrant; nonidentity and arbitrary enriched Q; RY fibrant but not cofibrant
(the conclusion uses QRY, never RY); nonpointed model categories (no zero object
is used); all nerve dimensions including dimension zero and degenerate simplices;
arbitrary enlargement of the test quasicategory universe. Complete/cocomplete
model categories have initial and terminal objects, so no spurious empty-model
case is assumed. No nonempty hypothesis is placed on a bifibrant subcategory or
mapping space. Empty mapping simplicial sets remain covered by the constructions.

Searches made, before writing:

- `msearch.py ... leanfinder`: "A simplicial Quillen equivalence induces an
  equivalence of bifibrant coherent nerves after enriched cofibrant replacement".
  Eight hits on ordinary nerve/truncation adjunctions; no match.
- `msearch.py ... loogle`: "SimplicialNerve, EnrichedFunctor". No hits; the
  service reported unknown identifier SimplicialNerve.
- `msearch.py ... leansearch`: "simplicial Quillen equivalence derived right
  adjoint equivalence of bifibrant coherent nerves". Eight hits on Kan–Quillen
  fibrations, cosimplicial equivalences and ordinary nerve adjunctions; no match.
- `msearch.py ... grep`: "QuillenEquivalence|enriched.*replacement" in
  AlgebraicTopology. No hits.
- `rg` of WeilConjectures and lean/Sheaf for QuillenEquivalence, enriched
  replacement and the item name: found change-of-index/projective Quillen
  equivalence data and other replacement comparisons, not this theorem.
  Opened the projective, coherent-nerve infrastructure and enriched-evaluation
  interfaces, and the bifibrant common-replacement construction. The coherent
  nerve functor there is restricted to small bundled SCat; our owning-node
  helper is its same postcomposition formula for potentially large categories.
- `rg` of Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  for the proposed full declaration/namespace names: no conflicting declaration.
  The broader DerivedRestriction search returns unrelated sheaf restriction APIs.

Validation: the required `scompile.py Q86 ...` compiles both sandbox and module
with no errors or warnings (1.7 s and 1.9 s). The first compile exposed a namespace
closure and syntactic universe-lift mismatch; both were repaired, followed by
line-width cleanup. No local/global Lake build or direct repository mutation used.

## Second reading by Q86

This is the worker's second pass with the DAG statement and final module open;
the maintainer performs the independent review specified in the dispatch brief.
No second agent was started. Compared the binders individually as listed above:
model/combinatorial/simplicial hypotheses, the actual adjunction and Quillen iff,
and arbitrary enriched Q with enriched natural q and trivial-fibration components
all agree. Compared each output: h gives bifibrancy, the helper gives exactly QR,
the coherent nerve map uses that helper, the explicit categorical test has the
correct contravariant direction, and the final edge compares this same map with
the normalized derived right adjoint. The actual derived unit and counit are used.
During this pass I made existence of the normalized derived adjunction explicit
with `Nonempty`, so the unit/counit assertions are accompanied by existence, and
made the combinatorial set-size universe independent. I checked that no conclusion
is substituted as an input hypothesis: localization presentations, fibrant
replacements and their comparisons occur only in universally quantified conclusions.
There is no statement correction or unresolved statement dispute.

## Repair self-check

The returned delivery was rechecked against the immutable head and the current
`newtargets-dag` tip. The repair packet contains exactly the retained module,
the item's Lean record, and this report; no dependency or new-node file is
introduced. The module's three declarations are still owned by the item's
single `lean.file`, and the node's recorded statement is byte-for-byte the
theorem signature in that module. The malformed reviewer-fix path reported for
the prior head is therefore repaired by regenerating the delivery from this
packet; all source, dependency, and edge-case checks above were rerun.

## Maintainer review fix (NT-cc reviewer, 2026-10-17)

The helper `DerivedRestriction.nerveMap` re-implemented the landed coherent-nerve map
`CategoryTheory.hammockCoherentNerveMap` (lem-coef-hammock-infinity-localization) by the same
postcomposition formula. Its body is now the universe enlargement of that existing map
(one definition per notion); the module publicly imports
`Sheaf.CategoryTheory.HammockInfinityLocalization`. The item theorem's signature is unchanged.
The source citation above, garbled in the delivered report, was restored.
