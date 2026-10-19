## Worker report

Item: `lem-coef-kan-quillen-right-proper`, Q03 stage 2, 2026-10-16.
Module: `Sheaf.AlgebraicTopology.KanQuillenRightProper`.
Main declaration: `SSet.KanQuillen.right_proper_kan_quillen`.
There is one postponed theorem, with the node's eight-step proof in its docstring;
its proof is exactly `by sorry`. The two helper definitions have real data.
No other DAG statement is stated or changed. No statement correction is made.

I read the current reviewed Q26 eight-step split, its statement dependencies and
its sources. The sandbox was empty at the start of this attempt. The prior
worker's superseded-split report is not used as a reason to discard this item.
The current node's mathematical statement, proof and proof dependencies remain
unchanged. Its statement dependencies gain the already landed
`def-coef-coherent-localization-interface`, whose definition is needed to give
the precise meaning of the final clause. This is the allowed addition of an
existing node with a Lean record, not a new theorem dependency on finite Reedy
localization and not a new definition node.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The category is exactly `SSet.{u}`, with `u` explicitly declared and arbitrary.
  Mathlib's `SSet` is `SimplexCategoryᵒᵖ ⥤ Type u`, and its `stdSimplex` is lifted
  Yoneda. The standard simplex is therefore the stated representable.
- Boundaries and horns are the existing `SSet.boundary` and `SSet.horn` used in
  `modelCategoryQuillen.I` and `.J`. The boundary consists of nonsurjective
  simplices. The horn omits a vertex other than its designated index.
  `I` includes all `n : ℕ`, including zero. `J` uses `n + 1` and every
  `i : Fin (n + 2)`, so includes every positive dimension and both outer horns.
- The weak-equivalence clause is the dependency's exact
  `SSet.Enhanced.IsWeakHomotopyEquivalence`. The helper
  `weakEquivalenceStructure` only packages that predicate in
  `CategoryWithWeakEquivalences`. Its data are an explicit lambda, not a choice.
  Unfolding the dependency gives bijectivity on `ZerothHomotopy` of realization
  and on `HomotopyGroup (Fin r)` for every `r ≥ 1` and every point of the source
  realization. These are the canonical postcomposition maps and hence give the
  specified group isomorphisms. The dependency uses `SSet.toTop` realization.
- The model assertion is `∃ m : ModelCategory SSet, ...`, with ALL THREE of
  `m.categoryWithFibrations`, `m.categoryWithCofibrations` and
  `m.categoryWithWeakEquivalences` equated to the specified structures. This
  prevents an unrelated model structure from witnessing the assertion.
  Mathlib's model axioms supply two-out-of-three, retract closure, lifting and
  both factorization axioms. The intrinsic limits and colimits of `SSet` need
  no additional assumption.
- Functoriality is asserted for BOTH factorization systems by
  `HasFunctorialFactorization (trivialCofibrations SSet) (fibrations SSet)` and
  `HasFunctorialFactorization (cofibrations SSet) (trivialFibrations SSet)`.
  These quantify over actual functorial data on the whole arrow category.
- Cofibrations are `monomorphisms SSet`, and fibrations are `.J.rlp`.
  In this presheaf category monos are precisely degreewise injections. These
  structures are Mathlib's scoped `SSet.modelCategoryQuillen` instances.
- Fibrant objects: `∀ X, IsFibrant X ↔ KanComplex X`. This is also Mathlib's
  existing definition of `KanComplex`, with the same horn-fibration structure.
- Trivial fibrations: `trivialFibrations SSet = modelCategoryQuillen.I.rlp`.
  This equality is for arbitrary source and target, with dimension zero present.
- Every mono is cellular: `monomorphisms SSet ≤ transfiniteCompositions
  (coproducts I).pushouts`. Mathlib's transfinite composites use well-ordered
  continuous chains; `.pushouts` and `coproducts.{u}` give exactly the two
  operations in the node. The indexing universe is that of the simplices.
- Trivial cofibrations: equality with
  `(transfiniteCompositions (coproducts J).pushouts).retracts`.
  Thus the equality asserts both directions of the retract characterization.
- Right properness quantifies over `E B B'`, `p : E ⟶ B` and `w : B' ⟶ B`.
  The ONLY hypotheses are `Fibration p` and weak equivalence of `w`.
  The conclusion is weak equivalence of `pullback.fst p w`, the pullback of
  `w` along `p`. There is no Kan or nonemptiness hypothesis on any of these
  three objects.
- The homotopy-pullback clause uses an actual coherent localization `q` of all
  simplicial sets at the stated weak equivalences. `C : SSet.{u+1}` contains
  the independent object/hom universes `u+1` and `u` of `SSet.{u}`; no equality
  of distinct universes is imposed. `IsLocalization` has the full coherent
  functor-category universal property, not just a homotopy-category property.
- For `A B Z` the three assumptions are exactly `KanComplex A`,
  `KanComplex B`, `KanComplex Z`, followed by `f : A ⟶ Z` and `g : B ⟶ Z`.
  Every `A'`, `w : A ⟶ A'`, `p : A' ⟶ Z`, and equation `w ≫ p = f` is
  quantified, assuming only weak equivalence of `w` and `Fibration p`.
  In particular `w` is not required to be a cofibration or a selected
  functorial replacement. `A'` and `pullback p g` are asserted Kan.
- `replacementMap` is the explicit natural transformation with components
  `w`, `𝟙 Z`, `𝟙 B`; its commutation is the supplied factorization equation.
  No arbitrary comparison map is assumed. `transformation q` and `diagram q`
  are the already constructed nerve/evaluation maps of the recorded module.
- The result has a specified cone edge `s` with
  `IsLimitEdge (diagram q (cospan f g)) (object q (pullback p g)) s`.
  This uses the dependency's actual coherent comma cone category and
  `Enhanced.IsLimiting`; it retains the apex as the localization of the
  ordinary pullback. The `Composes` clause is a compositional two-simplex
  identifying postcomposition with the actual replacement transformation
  with `transformation q (pullback.cone p g).π`. Thus it is the strict
  pullback cone transported back to the original cospan, rather than an
  arbitrary cone on a potentially unrelated object.
- Independence is `Enhanced.IsContractible (Enhanced.limitingConeSpace ...)`.
  This is the core of the full subcategory of limiting cones with varying
  apex, so it retains comparisons together with their higher compatibility
  simplices. Terminality gives the canonical comparisons under maps of
  cospans, and contractibility gives their coherent uniqueness. These are
  stronger data than a bare isomorphism of apices in a homotopy category,
  and are exactly the cone interpretation explained in the node's proof.
  Either leg is covered by the universal quantification in `f` and `g`:
  instantiate with `g,f` for a replacement of the other leg, and use the
  canonical symmetry of the cospan and its pullback. The hypotheses and
  replacement conditions are symmetric, so this excludes no replacement.

Dependency declarations read and used:

- `def-weil-pbc-simplicial-set` is Mathlib, with the actual declarations
  `SSet` in `SimplicialSet.Basic`, `SSet.degenerate/nonDegenerate` in
  `.Degenerate`, `SSet.Subcomplex` in `.Subcomplex` and `SSet.Finite` in
  `.Finite`. Their complete recorded definitions and docstrings were read.
  The statement only needs the category itself and existing simplex objects.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: the weak-equivalence and
  homotopy-group-map definitions, `coneCategory`, `IsLimiting`,
  `IsContractible`, `limitingConeSpace`, and their underlying comma/core
  constructions. I read the explicit signatures and bodies, not just names.
- `def-coef-coherent-localization-interface` records the existing definitions
  `HomotopicalAlgebra.FiniteReedy.largeNerve`, `IsLocalization`, `object` and
  `Composes` in `Sheaf.CategoryTheory.FiniteReedyLocalization`. The same
  module's `comparison`, `diagram`, `transformation` and `IsLimitEdge` are
  concrete helper definitions for these same nerves and coherent cones.
  Its theorem `finite_reedy_localization` is NOT invoked. These definitions
  precede that theorem and depend only on nerves, evaluation and the cone
  definitions. This gives no circular theorem or DAG dependency on the
  downstream finite-Reedy statement whose proof may use the present theorem.
- Mathlib's `ModelCategory`, `HasFunctorialFactorization`, `.I`, `.J`,
  `.rlp`, `KanComplex`, `transfiniteCompositions`, `coproducts`, `pushouts`,
  `retracts`, `cospanHomMk`, and `pullback.cone` were read at their sources.
  They are used directly rather than redefined.
- The already stated proof dependency
  `Sheaf.Paper.TrivialKanHomotopyEquivalence` is imported privately, as is
  Mathlib's `SmallObject.IsCardinalForSmallObjectArgument` (the recorded
  small-object leaf). Mathlib's boundary-cell dependency is imported via
  the simplicial-set modules. The other proof dependencies have no Lean
  record yet and are therefore not imported. The cone-calculus node also
  has no recorded Lean declaration at this writing. None is required as
  statement data, and none is restated in this delivery.

Edge cases checked before writing: boundary zero is the empty subcomplex of
`Δ[0]`, so boundary lifting includes vertex surjectivity; horns start at one,
so empty Kan complexes are allowed. Empty-to-point is a Kan fibration but not
a trivial one, distinguishing the two generating classes. Empty-to-empty
passes boundary lifting. The identity mono is covered by the cell classes
(including empty coproducts). Disconnected bases and empty fibres are retained
in right properness; no positive-group-only surrogate is used. Identity
replacements and arbitrary weak-equivalence replacements both satisfy the
same quantified clause. The replacement objects are concluded Kan rather
than assumed Kan. Universes include `u = 0` and arbitrary `u`; localization
uses the necessary containing universe.

Searches actually made using `msearch.py`:

- LeanFinder, “Simplicial sets admit the right proper Kan Quillen model
  structure whose weak equivalences are geometric realization weak homotopy
  equivalences”: found `.I`, `.J`, the fibration/cofibration structures and
  their equalities, but no complete model structure or right-proper theorem.
- LeanFinder, “Simplicial sets admit a right proper functorial Kan Quillen
  model category structure”: the same existing simplicial ingredients.
- Loogle, `SSet.modelCategoryQuillen, HomotopicalAlgebra.ModelCategory`:
  unknown namespace identifier, so no usable result for that query.
- Loogle, `HomotopicalAlgebra.ModelCategory`: found the generic model class
  and its projections/axioms; not the simplicial-set theorem.
- LeanSearch, “The Kan Quillen model structure on simplicial sets is right
  proper”: returned horn-fibration and cofibration ingredients and unrelated
  proper-pairing results; no exact match.
- Mathlib grep, `modelCategoryQuillen|RightProper|right.proper` in
  `AlgebraicTopology`: found the existing scoped structures and anodyne
  results. Reading `CategoryWithFibrations` confirms its explicit TODO for
  the model structure.
- `rg` for `KanQuillen|kan_quillen|right.proper|RightProper` in the upstream
  `WeilConjectures` and project `lean/Sheaf` trees found no theorem matching
  this item. The relevant project hits were proof-docstring mentions in
  `CosimplicialFrameMapping`; no existing statement. The prescribed item-id
  search in the upstream tree returned no hit.
- The current coherent-localization node was found by searching the DAG's
  existing localization/interface records and its full source definition
  was opened; its declaration is reused.

Source verification: opened the current blueprint ancestor's coefficient
adjunction proof paragraph 2, the supplied Cisinski PDF and Hovey PDF. Read
the cited model-characterization results and Cisinski's localization pullback
criterion (7.5.18/7.5.20) for the meaning of limiting coherent squares. The
module's mathematical proof follows the current node's eight steps. No node
fault or STATEMENT-DISPUTED finding remains.

Validation: `scompile.py Q03 lem-coef-kan-quillen-right-proper` compiled the
sandbox file and its library-path copy separately, both within the specified
60-second limit. The initial reducibility warning on the class-data package
was repaired with `@[instance_reducible]`; the subsequent run was clean.
The final private proof imports are included in the mandatory delivery dry
run. No global build, direct Git command or live-source edit was performed.

## Second reading by Q03

Independent reader, 2026-10-17. I opened the sandbox node and module, the three
statement-dependency records, their actual definitions, and the current base
node. The sandbox differs from the base only in `lean` and the addition of the
landed coherent-localization definition to `stmt_deps`. There is no
`statement_change`, no new node, no dependency module, and no repair handoff.

Source reading: I read Stacks `simplicial.tex`, section 0174, Definition 0175,
Definition 08NL and Lemma 08NS, including their surrounding conventions. The
main result is not a Stacks theorem. I independently opened the cited Cisinski
and Hovey PDFs, then read Cisinski 3.1.8, 3.1.28, 3.1.29, 3.8.4 with its proof,
7.5.18 and 7.5.20, and Hovey Definition 3.2.1, Proposition 3.2.2,
Proposition 3.2.6 and Theorem 3.6.5. These have no finiteness, nonemptiness,
connectedness or fibrancy-of-the-base assumption on the model structure or
right properness. Cisinski 7.5.20 has the fibrant bases needed for the final
Kan-cospan clause. Hovey's topological arguments use compactly generated
spaces; the statement's weak equivalences use the existing realization
predicate, not an additional preservation-of-products assertion in `TopCat`.
I also read paragraph 2 of the blueprint ancestor's coefficient-adjunction
proof, which explains this foundational input's role.

Here is my object/hypothesis/conclusion list, matched against the Lean:

1. All simplicial sets and their maps: `SSet.{u}`, with the explicitly bound
   arbitrary universe `u`. Mathlib `Basic` defines contravariant functors on
   `SimplexCategory` with values in `Type u`; morphisms are natural
   transformations. Verdict: exact, with no extra mathematical hypothesis.
2. Representable simplices, boundaries and positive-dimensional horns:
   Mathlib `stdSimplex` is `uliftYoneda`; `boundary` consists of nonsurjective
   simplices and `horn n i` of simplices omitting a vertex other than `i`.
   The actual `modelCategoryQuillen.I` ranges over every natural number;
   `J` ranges over `n+1` and all `Fin (n+2)`. Verdict: both outer horns and
   the zero-dimensional boundary are present.
3. Weak equivalences detected by realization on components and every based
   homotopy group: `Enhanced.IsWeakHomotopyEquivalence`. I opened
   `componentsMap` (path-component quotient) and `homotopyGroupMap` (actual
   postcomposition on based cubical homotopy classes). Its bijections on
   `HomotopyGroup (Fin r)` for every `1 ≤ r` and every source basepoint are
   precisely isomorphisms on these groups. Verdict: exact; the helper
   `weakEquivalenceStructure` only packages the same predicate as class data.
4. A model structure on these classes: `∃ m : ModelCategory SSet, ...` fixes
   all three structure fields, including the weak-equivalence package.
   I read `ModelCategory`'s lifting, retract, two-out-of-three and factorization
   fields. Existing limits and colimits of simplicial sets supply the
   completeness convention without extra assumptions. Verdict: exact.
5. Functoriality: both `HasFunctorialFactorization` conjuncts. The actual class
   asserts nonempty functorial factorization data on the entire arrow category,
   rather than separate choices for each arrow. Verdict: exact for both systems.
6. Cofibrations and fibrations: equalities with `monomorphisms SSet` and
   `modelCategoryQuillen.J.rlp`, using Mathlib's scoped structures. Monos in
   this presheaf category are degreewise injections. Verdict: exact.
7. Fibrant objects: `∀ X, IsFibrant X ↔ KanComplex X`. I read Mathlib's
   `KanComplex`, which is fibrancy for precisely the horn-defined structure.
   Verdict: exact, including the empty Kan complex.
8. Trivial fibrations: `trivialFibrations SSet = modelCategoryQuillen.I.rlp`.
   Verdict: the equivalence applies to arbitrary arrows and includes `n=0`.
9. Every mono is boundary-cellular: the inclusion of `monomorphisms` in
   `transfiniteCompositions (coproducts I).pushouts`. I opened the continuous
   well-ordered composition, coproduct and pushout definitions. Verdict: exact;
   this does not merely assert a retract characterization for monos.
10. Trivial cofibrations: equality with the retracts of the corresponding
    horn-cell class. Verdict: both directions and all three cellular operations
    are retained, with indexing universe `u` sufficient for `u`-small simplices.
11. Right properness: for all `E B B'`, `p : E ⟶ B`, `w : B' ⟶ B`, the only
    assumptions are `Fibration p` and the realization weak equivalence of `w`.
    The conclusion concerns `pullback.fst p w`, which is the base change of
    `w`. Verdict: exact; no assumption that the bases or total space are Kan.
12. Meaning of homotopy pullback: an actual localization
    `q : largeNerve SSet ⟶ C` with `IsLocalization (weakEquivalences SSet) q`.
    I read the enlarged nerve, actual precomposition map, edge-inverting full
    functor subcategory and coherent functor-equivalence condition. Verdict:
    the whole coherent universal property is used, not ordinary localization.
13. Objects and hypotheses of the cospan: `A B Z : SSet`, their three
    `KanComplex` assumptions, and `f : A ⟶ Z`, `g : B ⟶ Z`. Verdict: exactly
    the node's Kan cospans; `q` is fixed before these universal quantifiers.
14. Any replacement of a leg: every `A'`, `w : A ⟶ A'`, `p : A' ⟶ Z` with
    `fac : w ≫ p = f`, assuming only weak equivalence of `w` and fibration
    of `p`. Verdict: no cofibration, chosen-factorization or extra Kan
    assumption is imposed on the replacement. Its being Kan and the pullback's
    being Kan are conclusions. Swapping the two legs covers the other leg.
15. The ordinary pullback actually represents the homotopy pullback:
    `IsLimitEdge (diagram q (cospan f g)) (object q (pullback p g)) s`.
    I opened `IsLimitEdge`, the coherent comma `coneCategory`, `IsTerminal`
    and `IsLimiting`; the witness fixes both the actual apex and the cone
    edge. `Composes s (transformation q (replacementMap ...))
    (transformation q (pullback.cone p g).π)` specifies its compatibility
    with the actual strict pullback cone. I checked the order of all three
    faces in `Composes` and the components `w, 𝟙 Z, 𝟙 B` of `replacementMap`.
    Verdict: the canonical cone, not just an arbitrary equivalent apex.
16. Independence up to natural equivalence:
    `Enhanced.IsContractible (Enhanced.limitingConeSpace ...)`, with the
    limiting-cone conclusion for every replacement. I opened that space: the
    core of the full subcategory of terminal cones, with varying apex.
    Verdict: it retains comparisons of cones and their higher compatibilities;
    their universal property gives natural comparisons under maps of cospans.

Dependency checks: the `SSet` dependency is the recorded Mathlib notion;
`EnhancedDiagramsCones` supplies the stated realization and comma-cone
definitions; the landed coherent-localization interface supplies
`FiniteReedy.IsLocalization`, with `diagram`, `transformation`, `object`,
`IsLimitEdge` and `Composes` read directly in its module. These are concrete
definitions preceding `finite_reedy_localization`; that downstream theorem
is not invoked. I found no missing notion, private substitute or unusable
dependency interface. I also opened the privately imported
`SSet.exists_section_homotopy_equivalence`; its boundary-lifting hypothesis
and section/cylinder-homotopy conclusion match proof step 3. The Mathlib
small-object and boundary-skeleton dependencies are imported. The remaining
proof nodes currently have no Lean record, so need no import in this delivery.

Edge cases: `∂Δ[0]` is empty, so its lifting condition tests surjectivity on
vertices. Horns start in dimension one, permitting the empty Kan complex.
The empty-to-point map is a Kan fibration but fails boundary-zero lifting;
empty-to-empty and identity replacements are retained. Empty cell families
and identity monos are allowed. Right properness includes empty fibres,
disconnected bases and non-Kan bases. Empty Kan cospans are not excluded.
There is no ring, characteristic or positive-integer hypothesis here. The
universes of the category of simplicial sets are object `u+1`, morphism `u`;
`C : SSet.{u+1}` contains both in `largeNerve`. The sole theorem universe is
`u`, including `u=0`; no extra independent universe or equality was inferred.

Independent searches, using words different from the author's queries:

- LeanFinder via `msearch.py`: "simplicial sets model structure weak homotopy
  equivalences pullback stable along fibrations". Found the scoped horn and
  mono structures and generic base-change results for trivial fibrations;
  the latter assume the pulled-back map is also a fibration, so are not the
  unrestricted right-properness theorem or this full statement.
- LeanSearch via `msearch.py`: "monomorphisms are cofibrations in the functorial
  right proper model category of simplicial sets". Found the mono/cofibration
  equivalence and generic model-category projections, not this node.
- Loogle via `msearch.py`: `"KanComplex", "pullback"` returned no hits.
- Separate `rg` searches in Mathlib's algebraic-topology tree, upstream
  `WeilConjectures`, and project `lean/Sheaf` for `modelCategoryQuillen`,
  `RightProper`, `rightProper`, `right_proper`, `KanQuillen`, `kan_quillen`,
  then `WeakHomotopy`, `weak.homotopy`, `weakEquivalenceStructure`, and
  `replacementMap`. No complete match or duplicate class package/map.
  `CosimplicialFrameMapping` uses the same weak-equivalence predicate and
  states its separate mapping-complex/replacement input; its
  `frameSpaceWeakEquivalences` is a morphism property, not a second
  `CategoryWithWeakEquivalences` structure. The upstream item-id search
  returned no hit. No node or existing theorem should replace this module.

Mismatch found and repaired: `attribute [local instance]
weakEquivalenceStructure` violated the explicit prohibition on file-local
instances. I changed only that attribute to `[scoped instance]`, in namespace
`SSet.KanQuillen`. Consumers can activate the same real package with
`open scoped SSet.KanQuillen`. This preserves the theorem's mathematical
statement and its verbatim signature; no node correction is needed.

Validation: `scompile.py` compiled the delivered module cleanly as both a
sandbox file and its library-path file, each under 2.2 seconds. An additional
scratch consumer, compiled separately by the same wrapper, imported the
module, opened the two scopes, synthesized the weak-equivalence structure
as `SSet.KanQuillen.weakEquivalenceStructure`, and printed the theorem from
outside its namespace. It has only universe `u` and no hidden instance
hypotheses. A direct text comparison confirms `lean.statement` is verbatim
the signature in the file. Every line is at most 100 characters. The only
postponed theorem remains `right_proper_kan_quillen := by sorry`; both helper
definitions have real data. Source/blueprint docstrings and all eight proof
steps are present. No mathematical mismatch or disputed statement remains.
