## Worker report

The module `Sheaf.CategoryTheory.FreeFactorHammockComparison` states
`CategoryTheory.free_factor_hammock_comparison`, with the single proof `by sorry`.
All helper definitions contain real data. No other DAG theorem is restated or proved.
The node's mathematical statement is unchanged. Its statement dependencies gain the
already landed `def-coef-simplicial-hammock-pair` to reuse the existing reduced-hammock
and diagonal definitions instead of creating copies. There are no new nodes or
dependency-module repairs.

Source checked: Dwyer--Kan, *Calculating simplicial localizations*,
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-2.pdf,
Definition 2.1 (printed p.19), Comparison Lemma 2.3 and Remark 2.5 (printed p.20),
Proposition 3.4 (printed p.21), and the node's expanded Section 5.8 proof plan.
The source's comparison is mappingwise and does not require functors to preserve
chosen generators. The current blueprint ancestry is the node's recorded proof
paragraph of `prop-coef-integral-exceptional-adjoint`; this is not a unit statement.

Hypothesis and clause correspondence:

- Small common object set: `FreeFactorHammockInput.C : Cat.{u, u}` has an arbitrary
  object type in `Type u`. Both generator sets are morphism properties on this same
  category, so there is exactly one common object set. The universe `u` is explicit;
  objects and hom sets may always be placed together in a sufficiently large universe.
- Chosen free ordinary categories `D,V`: the fields `D,V : MorphismProperty C` select
  their generating arrows inside the coproduct `P = C`. They select GENERATORS, not
  all arrows of a factor. `FreeFactorHammockGraph` has these as a disjoint tagged sum
  of edges. `freeFactorHammockWordFunctor` is Mathlib's `Paths.lift`, evaluating words
  by composition with identity for the empty word.
- Unique finite composable words and no identity generators:
  `FreeFactorHammockInput.unique_words` is bijectivity of this evaluation on every
  Hom set. Injectivity rules out identity generators (the empty and one-letter words
  would coincide) and overlapping factors' nonidentity generators (the two tags would
  coincide). Surjectivity says that every arrow is such a word. There is no extra
  existence or nonemptiness hypothesis.
- Coproduct `P = D *_O V`: the same bijective union-word presentation is an equivalent
  encoding of this hypothesis, not an extra relation or a weaker universal property.
  From the node's coproduct, the two canonical inclusions carry the chosen generators
  to precisely these two subsets of `P`, and every word is unique. Conversely,
  `D.multiplicativeClosure` and `V.multiplicativeClosure` are the two free wide
  subcategories; a functor from each fixing objects extends uniquely by evaluating
  the union words. Thus arbitrary free categories with their chosen presentations
  are covered, not only a special preselected category. No theorem about this
  equivalence is postponed or assumed: the unique-word data is the input encoding.
- Canonical wide subcategory `V` in `P`: `I.V.multiplicativeClosure`, Mathlib's
  closure under identities and finite composition, is exactly the second free factor.
  This is a construction, not an arbitrary subcategory or extra assumption.
- Reduced hammocks, vertical markings, identity endpoints, uniform alternating
  columns, no identity column, and the length-zero diagram:
  `FreeFactorHammockComparison.hammock : HammockLocalization
  I.V.multiplicativeClosure` reuses the existing exact reduced-grid interface.
  Its `simplices` are equivalent to `ReducedHammock`; `HammockChain.marked`,
  `hammockEndpoint`, `HammockStep.backward`, and `HammockReduction` render the
  conditions individually. `row_operators`, `identities`, and `composition` of this
  same interface pin operators and enriched operations to row deletion/repetition
  and concatenation followed by reduction. No replacement grid definition is made.
- Diagonal for simplicial pairs: the public import
  `Sheaf.CategoryTheory.SimplicialHammockPair` gives the recorded
  `SimplicialHammockPair.simplices` equivalence to
  `ReducedHammock (U.degree (op ⦋n⦌)) x y n`; its `row_operators` applies both
  simplicial operators before reduction. This convention is reused, not reasserted
  as a second theorem. The comparison in this item is for an ordinary free-factor pair.
- Ordinary inversion: `I.V.multiplicativeClosure.Localization` and its functor `Q`
  are Mathlib's construction with the same object set (wrapped) and formal inverses
  modulo the identity, composition and two inverse relations. No localization axiom
  or arbitrary groupoid is substituted.
- Discrete mapping sets: `FreeFactorHammockComparison.comparison` has target
  `(Functor.const SimplexCategoryᵒᵖ).obj (Q.obj x ⟶ Q.obj y)`.
- Row-product functor: `comparison` consists of actual simplicial maps. The
  `row_formula` field quantifies over every degree, simplex and row. The displayed
  `Paths.lift` takes forward arrows to `Q.map`, backward arrows to
  `Localization.Construction.wInv`, and evaluates the grid path by composition.
  This anonymous use of the existing path functor avoids declaring another copy of
  the downstream `dkHammockRowProduct` helper. The formula includes every row,
  not just row zero or vertices.
- Identity on objects and functor laws: the mapping-family is indexed by the same
  `x,y : I.C` with target objects `Q.obj x,Q.obj y`; this is the identity on the
  underlying object set. `identities` and `composition` are exactly the identity
  and composition conditions for that simplicial functor, in every degree.
- Mappingwise weak homotopy equivalences: `weak_equivalence` uses the recorded
  `SSet.Enhanced.IsWeakHomotopyEquivalence` on every comparison map, namely
  bijection on realized path components and all positive based homotopy groups.
- Naturality: `FreeFactorHammockComparisonStatement` provides comparisons
  simultaneously for all inputs. Its `naturality` quantifies over every functor
  `T : I.C ⥤ J.C` preserving the marked multiplicative closures. There is no
  condition on `T` on either generator subset. `FreeFactorHammockNaturality`
  supplies the actual enriched hammock map, its exact grid-image formula
  `IsHammockMap`, the ordinary localization functor with its triangle under `Q`,
  and the commuting `comparison_square` on every simplex. `HEq` transports only
  endpoint equalities from these functors. The triangle characterizes the unique
  induced ordinary functor by Mathlib's strict localization universal property.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CoherentNerveComparison`:
  `CategoryTheory.coherent_nerve_comparison`, its full signature
  `Nonempty CoherentNerveComparisonStatement.{u}`, and the locally mappingwise
  weak-equivalence condition `CategoryTheory.DwyerKanEquivalence`.
  The theorem uses the same enriched-category and realized weak-equivalence notions.
- `Sheaf.CategoryTheory.SimplicialHammockPair`:
  `CategoryTheory.WideSimplicialSubcategory`, `SimplicialHammockDegree`,
  `SimplicialHammockPair` and their full fields, read locally and checked through
  `scompile.py --source Sheaf.CategoryTheory.SimplicialHammockPair`.
  This already landed definition node is added to `stmt_deps`.
- Through that public module, `Sheaf.CategoryTheory.HammockInfinityLocalization`:
  `HammockChain`, `HammockStep`, `HammockReduction`, `HammockReduces`,
  `ReducedHammock`, `HammockLocalization`, `HammockObjects`, `hammockMapPath`
  and `IsHammockMap`, including their full grid/row/identity/composition signatures.
  We use its definitions only, not its downstream universal-localization theorem.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, with its realization-based definition,
  used by the coherent-nerve dependency.
- Mathlib `CategoryTheory.Paths`, `Paths.lift` (including its empty-word and
  composition behavior), `MorphismProperty.multiplicativeClosure` and its
  `IsMultiplicative` instance; `MorphismProperty.Localization`, `Q`, and
  `Localization.Construction.wInv`, read in `PathCategory/Basic.lean`,
  `MorphismProperty/Composition.lean`, and `Localization/Construction.lean`.

Proof-only imports retain all currently stated proof inputs:
`Localization.ZigzagHomotopyCalculus`, `FilteredColimitWeakHomotopyEquivalence`,
`NerveNaturalHomotopyEquivalence`, and `ProperWordColimitInvariance` (all under
`Sheaf`). The coherent-nerve proof input is already a public statement import.
The six other proof dependencies currently have no Lean record, so they cannot
be imported yet and are only named in the complete natural-language proof docstring:
`lem-coef-fixed-object-simplicial-free-calculus`,
`lem-coef-free-factor-hammock-pushout`,
`lem-coef-free-factor-hammock-universal-cover-reduction`,
`lem-coef-hammock-components-localization`,
`lem-coef-hammock-graph-colimit-presentation`, and
`lem-coef-hammock-inverted-arrow-actions`. No missing proof input is an added
hypothesis, and none is restated in this delivery.

Edge cases checked before writing:

- Empty object set: all unique-word and mapping conditions are empty products;
  no `Nonempty`, selected object, or connectedness is required.
- Empty generating subsets: paths still include the empty word. Either factor can
  consist only of identities, including the case when both do.
- Loops and infinite sets of generators: arbitrary morphism subsets and finite paths
  cover both; no acyclicity, finiteness or tree hypothesis is imposed on the input.
- Endomorphisms and identity hammocks: empty paths, identity arrows, and every
  `n = 0` simplex/row are included; `Fin (n+1)` always has the required row zero.
- Objects in different graph components: neither mapping set is required inhabited;
  the statement allows their comparison to be empty-to-empty.
- A functor may collapse generators to identities, take them to composite words, or
  mix the unmarked factor with marked arrows, provided it preserves the entire
  marked subcategory. The naturality binders include all these cases.
- The union-word bijection excludes, rather than silently treats as free, a category
  with a nontrivial relation or a generator equal to an identity.

Searches performed before writing:

- `msearch.py ... leanfinder`: "For free ordinary categories D and V, the hammock
  localization of their free product at V is weakly equivalent on mapping simplicial
  sets to ordinary inversion". Eight results, ordinary localization equivalences,
  nerve product comparisons, and homotopy-category localization constructions;
  no hammock/free-factor theorem.
- `msearch.py ... leansearch`: "hammock localization of a coproduct of free categories
  agrees with ordinary localization". Eight results, notably
  `MorphismProperty.Localization`, `Localization'`, localization of product functors,
  and cofibrant homotopy-category localization; no free-factor hammock comparison.
- `msearch.py ... loogle`: `"FreeCategory", "Localization"`; zero hits.
- `msearch.py ... grep`: `hammock|Hammock|free.*factor.*localiz`; zero Mathlib hits.
- `rg` in Mathlib, `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`,
  `lean/Sheaf/CategoryTheory`, and `dag/lean_names_upstream.json`: no declarations
  matching the proposed names, no upstream hammock construction, and no existing
  theorem with this content. `grep -rn` of the item id in upstream has no match.
  The project does have the reduced-hammock/diagonal modules reused here and the
  downstream `DkCofibrantLocalizationComparison`; the latter states a different
  augmented free-resolution comparison and uses this item in its proof. It cannot
  be imported as a prerequisite of this item.
- The free-category library search found Mathlib `Paths`, `Paths.of`, and `Paths.lift`;
  these implement the word construction. No second free-category definition is made.

Compilation: prescribed `scompile.py Q86 lem-coef-free-factor-hammock-comparison`
compiled this single file successfully, both sandbox and module-path modes, in
1.8 and 2.8 seconds. The first check exposed source/graph quiver instance ambiguity;
explicit `@Quiver.Hom C inferInstance` and `Paths.lift (V := ...) (C := C)` repaired
it. The successful check emitted no errors or warnings. No live file was modified,
no global build was run, and nothing was delivered. The required dry run is invoked as the last worker step; its tool output supplies
the preflight result. The independent second reading remains for the next worker.

## Second reading by Q86

Independent second reading, 2026-10-17. I read the node and its complete proof,
the delivered module, both statement-dependency records and their declarations,
and the reduced-grid definitions they import. I also obtained the current
`Sheaf.CategoryTheory.SimplicialHammockPair` source through `scompile.py --source`
and checked it against the local source. No repair note exists for this item.

Source read independently: Dwyer--Kan, *Calculating simplicial localizations*,
[the recorded PDF](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-2.pdf),
Section 1.2 (printed p.18), Definition 2.1 (p.19), Comparison Lemma 2.3 and
Remark 2.5 (p.20), Propositions 3.1--3.4 (pp.20--21), and Section 5.8
(pp.24--25). This is not a Stacks result. Section 1.2 uses small categories and
defines weak equivalences mappingwise; no connectedness, finiteness, or
generator-preservation hypothesis is imposed in Comparison Lemma 2.3.
Connectedness and finitely many generators occur only in reductions of its proof.

My object/hypothesis/conclusion checklist, matched against the Lean:

1. Small object set `O` and ordinary category `P`: `FreeFactorHammockInput.C :
   Cat.{u, u}` supplies both; there is no nonemptiness assumption. **Pass.**
2. Two chosen sets of generating arrows on this same object set:
   `FreeFactorHammockInput.D` and `.V` are morphism properties on `C`;
   `freeFactorHammockGraphQuiver` takes their tagged disjoint union. They denote
   generators, not the full factor subcategories. **Pass.**
3. Each factor is free, generators are nonidentity, and all words are unique:
   `unique_words` requires the evaluation functor to be bijective on every Hom.
   The evaluation is Mathlib `Paths.lift`, so the empty word is exactly the identity.
   Injectivity excludes an identity generator, two equal differently tagged
   generators, and all relations among words. **Pass.**
4. `P = D *_O V`, with its specified factor inclusions: the union-word encoding
   includes precisely this datum. Starting from the node's two free categories,
   their coproduct has this unique word presentation in the two generator sets.
   Conversely the `D`-only and `V`-only words give the free wide factors in `C`;
   any pair of object-fixing functors out of them extends uniquely by evaluating
   union words. Thus bijective evaluation is equivalent to the stated input,
   not an additional hypothesis about a particular presentation. **Pass.**
5. The marked wide category is the canonical `V` factor:
   `I.V.multiplicativeClosure`, whose constructors are generators, identities,
   and finite compositions. There is no arbitrary marked category added as data.
   **Pass.**
6. Width `k` grids have `k+1` rows, downward marked vertical arrows, constant
   endpoints, uniformly oriented columns and marked leftward arrows:
   `hammock : HammockLocalization I.V.multiplicativeClosure`, its `simplices`
   equivalence, `HammockChain.diagram/marked`, `hammockEndpoint`, and the two
   `HammockStep` constructors impose exactly these conditions. **Pass.**
7. Alternation and absence of identity columns, with empty hammocks included:
   `ReducedHammock` excludes every contextual `HammockReduction`; its elementary
   operations are precisely erasing an identity column and composing adjacent
   columns in the same direction. `Quiver.Path.nil` represents the identity
   hammock. These are the existing definitions, not private replacements. **Pass.**
8. Row deletion/repetition followed by reduction, and concatenation followed by
   reduction: `HammockLocalization.row_operators`, `.identities`, and
   `.composition` pin the enrichment to those operations. **Pass.**
9. For simplicial pairs, diagonal degree `n` means width `n` grids in degree `n`,
   applying both operators together: the imported `SimplicialHammockPair.simplices`
   uses `ReducedHammock (U.degree (op ⦋n⦌)) x y n`, and `.row_operators` combines
   `simplicialHammockDegreeOperator` with `hammockRows`. This is the already
   recorded definition node added to `stmt_deps`. **Pass.**
10. Ordinary inversion, with unchanged objects and only localization relations:
    Mathlib `I.V.multiplicativeClosure.Localization`, `.Q`, and
    `Localization.Construction.wInv` use the formal-inverse path quotient. I read
    `relations.id`, `.comp`, `.Winv₁`, `.Winv₂`, and `objEquiv`; the object wrapper
    changes no objects mathematically. **Pass.**
11. Discrete target mapping simplicial sets: the target of `.comparison` is
    `(Functor.const SimplexCategoryᵒᵖ).obj (Q.obj x ⟶ Q.obj y)`. **Pass.**
12. Comparison is the composite of any row, with backwards arrows inverted:
    `.row_formula` quantifies over every `n`, every simplex, and every
    `i : Fin (n + 1)`. Its `Paths.lift` sends forwards to `Q.map` and backwards
    to `wInv`; it includes the empty path. It specifies the canonical map in all
    degrees, rather than merely some weak equivalence. **Pass.**
13. A simplicial functor, identity on objects: `.comparison` is a family of
    simplicial maps indexed by `x,y : I.C`, with target objects `Q.obj x,Q.obj y`;
    `.identities` and `.composition` state the enriched functor laws in each
    degree. **Pass.**
14. Weak homotopy equivalence on every mapping simplicial set:
    `.weak_equivalence : ∀ x y, SSet.Enhanced.IsWeakHomotopyEquivalence
    (comparison x y)`. I read the latter definition: bijectivity on realized
    path components and all positive based homotopy groups. It is exactly the
    convention imported by the coherent-nerve dependency. **Pass.**
15. Naturality for all functors of pairs preserving the whole marked factor:
    `FreeFactorHammockComparisonStatement.naturality` quantifies over arbitrary
    `T : I.C ⥤ J.C` and only `hT` preserving multiplicative closures.
    `FreeFactorHammockNaturality.grid_formula` is the existing `IsHammockMap`
    condition applying `T` to every grid entry and reducing;
    `.localization_triangle` characterizes the induced ordinary functor under `Q`.
    Mathlib `Localization.Construction.uniq` guarantees this characterization is
    unique. `.comparison_square` commutes on every simplex; `HEq` transports
    only endpoints. No generator-preservation premise appears. **Pass.**
16. Comparisons simultaneously natural for all inputs: `Nonempty
    FreeFactorHammockComparisonStatement.{u}` supplies `.comparison` for every
    input before quantifying over its marked functors. This realizes the claimed
    natural family; naturality is not a hypothesis. **Pass.**

Edge cases: empty `O` makes all object-pair obligations vacuous; either or both
generator sets may be empty, leaving the corresponding factor discrete. The
length-zero path and `n = 0` have the stipulated identities and one row. A
single vertex with loops is allowed, as are infinitely many generators.
Distinct graph components may have empty Hom sets in both constructions; no
inhabitance was assumed. A functor can collapse a generator to an identity or
send it to a composite, and may send a `D` generator into the marked factor:
only preservation of the marked closure is required. There is no coefficient
ring, characteristic, scheme, or additive zero object in this statement.
The explicit universe `u` ranges over arbitrary small categories in the fixed
universe of the source and dependency; both objects and arrows are small there,
with no independent universe equation imposed on external input. All variables
and universes are bound (`autoImplicit false`).

Independent duplicate searches, run through the prescribed `msearch.py`:

- LeanFinder: `hammock mapping space localization free product free categories
  discrete hom sets` returned eight ordinary localization, free-groupoid and
  free-bicategory declarations; none states the hammock comparison.
- Loogle: `"Paths", "Localization"` returned only
  `CategoryTheory.Localization.Construction.ιPaths`, an object inclusion in the
  localization path category, not a comparison theorem.
- LeanSearch: `A free category generated by disjoint arrow sets has hammock
  localization equivalent to formally inverting one set of generators` returned
  eight results, including `MorphismProperty.Localization`, `Cat.free_obj`, and
  free-groupoid localization. These supply ordinary constructions only.
- Grep service: `hammock|free.factor.*inversion|hammock.*discrete` returned zero
  Mathlib hits. Independent `rg` of Mathlib, the named upstream source tree,
  project `lean/Sheaf`, and `dag/lean_names_upstream.json` for hammock,
  free-factor localization, and the proposed declaration names found no upstream
  theorem or name clash. The project hits include the reused reduced-hammock
  definitions and the downstream `DkCofibrantLocalizationComparison` theorem.
  I opened the latter's signature and proof plan: it compares a free-resolution
  localization with hammocks and explicitly uses this item in proof step 6,
  so it is not an existing match for this ordinary free-factor comparison.

I also read Mathlib's `Paths.lift`, its empty-word evaluation, the
`multiplicativeClosure` constructors and multiplicativity instance, and the
localization quotient and strict universal property. The helper graph here is
just the tagged generating quiver for this input; the free category and ordinary
localization are reused Mathlib constructions. No new DAG definition node or
dependency-module repair is needed. The existing coherent-nerve and
simplicial-hammock interfaces give the notions their node records promise.

H5/H6/H8/H9: all new definitions contain real data, there is exactly one postponed
theorem and no proved theorem, every declaration has the source and blueprint
docstring, and the theorem's docstring includes all seven proof steps and their
dependencies. The four proof-only imports and coherent-nerve public import cover
all five presently stated proof dependencies; the remaining six are correctly
listed above. There is no `statement_change`, since no mathematical correction
is needed. The node's `lean.statement` is verbatim the theorem signature.

Mismatches found: none. I retained the Lean module and node without alteration;
the second reading adds only this independent review and fresh search evidence.
I rechecked the worker's count of six unstated proof dependencies and confirmed
it is correct (five of the eleven proof dependencies already have Lean records).

Validation: prescribed `scompile.py Q86 lem-coef-free-factor-hammock-comparison
lean/Sheaf/CategoryTheory/FreeFactorHammockComparison.lean` passed in sandbox and
library-module modes, respectively 2.1 s and 1.9 s, with no errors or warnings.
There are no sibling modules to compile. Delivery preflight and push follow this
reading through the prescribed wrapper only.
