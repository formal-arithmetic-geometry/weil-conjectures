## Worker report

The module `Sheaf.CategoryTheory.DoldKanHypercoverQuillen` states
`CategoryTheory.DoldKanHypercover.doldKanHypercoverQuillen`, with its entire proof
`sorry`. The output `Statement` packages the adjunction, its two Quillen assertions,
the canonical realization's homotopy comparisons, preservation of local equivalences,
and the interval arrow comparison. Every helper definition has real data. No theorem
other than the requested theorem is postponed or proved.

The source was opened at https://arxiv.org/pdf/1511.02828 and read at §3.3,
Fact 3.14, Proposition 3.15 (printed pp. 11–12), Lemma 5.12 and the interval
paragraph of Lemma 5.13 (printed pp. 20–21). The source's homological indexing
is reindexed as cohomological degree `-n`. No change to the natural statement
or proof plan is needed.

Hypotheses and clauses are rendered as follows:

| Natural statement | Lean rendering |
| --- | --- |
| A small category and an arbitrary covering-sieve topology | `(C : Type u) [SmallCategory C] (J : GrothendieckTopology C)`; no finite-limit or subcanonical instance occurs. |
| Size convention | One explicit working universe `u` for the small category, coefficients, set and module values, and small indexing families. Categories of presheaves/complexes live in `u+1`. This is the common small universe of the node, with the larger category universe automatic. No derived-category universe is equated to it. |
| A commutative coefficient ring | `(Λ : Type u) [CommRing Λ]`; the zero ring is allowed. |
| Associated module sheaves | `[HasWeakSheafify J (ModuleCat.{u} Λ)]`, the existence/choice interface supplied by `dgPresheafModelLocalizations`, rather than a geometric restriction. Set-valued sheafification is the existing small-site instance. |
| Presheaves and unbounded cochains | Existing `DgPresheaf C Λ`, exactly `CochainComplex (Cᵒᵖ ⥤ ModuleCat Λ) ℤ`. |
| Augmented semirepresentable hypercovers over a fixed representable | Existing `DerivedHypersheaf.AugmentedOver`, `augmentedOverToAugmented` and `IsHypercover`. The latter requires semirepresentability and sheaf-epimorphic proper-face matching maps, formed in the presheaf slice; its degree-zero matching object is terminal in that slice, i.e. the target representable before slicing. |
| Refinements over the same target | The existing `AugmentedOver C T` is literally an `Over` category; its morphisms are commuting augmentation triangles. No refinement or density hypothesis is imposed. |
| A small hypercover set H, not necessarily dense | `I : Type u`, targets `T : I → C`, actual augmentations `H : ∀ i, AugmentedOver C (T i)`, and `∀ i, IsHypercover J (...)`. An indexed family is the usual encoding of a small set of arrows; repetitions do not change localization. |
| The alternating augmentation e_U | Existing `DerivedHypersheaf.hypercoverAugmentation`, obtained by free modules, `AlternatingFaceMapComplex.ε` and extension along `embeddingDownNat`. It retains the original augmentation map. |
| B contains all integer shifts | `shiftedAugmentations Λ T H : I × ℤ → Arrow (DgPresheaf C Λ)`, using `CochainComplex.shiftFunctor` on that actual augmentation. |
| NΛ | `freeNormalization`: flip the two presheaf variables, apply the recorded `freePresheaf` degreewise, use `Abelian.DoldKan.N`, and extend by zero with `embeddingDownNat`. Mathlib's `NormalizedMooreComplex.objX` intersects precisely `ker d₁,…,ker dₙ`; `objD` is induced by `d₀`. |
| R(K) | `realization`: the canonical `complexOfFunctorsToFunctorToComplex` followed objectwise by existing `DoldKanHomology.simplicialRealization`. Its `connectiveTruncation` uses `truncLE'Functor`, with degree zero the cycles `ker d⁰`, not the original degree-zero module. |
| NΛ is left adjoint to R | `Statement.adjunction : freeNormalization C Λ ⊣ realization C Λ`. |
| Projective Quillen assertion | `Statement.projective`, quantified over every `DgProjectiveModelData` and every simplicial-presheaf model with the recorded objectwise weak equivalence and Kan fibration classes. Model axioms then determine the projective cofibrations. `DgLeftQuillen` is preservation of cofibrations and trivial cofibrations; together with `adjunction` this is exactly a Quillen adjunction. |
| Localized Quillen assertion | `Statement.localized`, for all the preceding small hypercover families, all `DgBousfieldModelData` at their shifted augmentations and every H-localized model with the original cofibrations and the recorded `BousfieldLocalization.localEquivalences`. The original usual enrichment and a genuine functorial projective cofibrant replacement are quantified over exactly as in `simplicial_presheaf_localization_comparison`. They specify derived mapping spaces; they are not extra hypotheses on C, Λ, or H. |
| Objectwise Kan | `Statement.homotopy.kan` applied to `K.asFunctor.obj (op V)`. This is definitionally the evaluated `realization`. |
| π₀ is the set underlying H⁰ | `homotopy.piZero` and `piZero_natural`; path components of the canonical geometric realization are used. |
| π_m at zero is H^(-m), m≥1 | `homotopy.piPositive`, indexed as `m+1`, is a multiplicative group equivalence to `Multiplicative` of the additive cohomology module in degree `-(m+1)`; specialize its vertex to the existing `zeroVertex`. This includes m=1 in the natural statement. |
| Translations at all vertices and naturality on slices | `translation_formula` is actual addition of the degenerate vertex in every simplicial degree; `translation_zero` fixes its basepoint, and `translation_groups` specifies its action on the above group comparison. `piZero_natural` and `piPositive_natural` hold for all complex maps, hence for every presheaf restriction and every arrow of every slice. The formula forces translation to commute with those same restrictions. |
| Cohomology-sheaf equivalences become local weak equivalences | `Statement.localEquivalence` uses existing `DgSheafCohomologyEquivalence J f` and `LocalSimplicialPresheaf.IsLocalWeakEquivalence J (realization.map f)`. The latter tests sheafified π₀ and local surjectivity/injectivity of positive homotopy groups at every object and vertex, exactly the associated-sheaf isomorphism tests on every induced slice topology. |
| Standard simplex, boundary and horns | Existing `SSet`, `stdSimplex`, `boundary`, `horn` and Kan classes, imported through the recorded simplicial-set/projective-model/local-map interfaces. |
| L_T[0] and the algebraic interval | `freeRepresentable` is the recorded free representable placed in cochain degree zero. `intervalInclusion` is the actual right inclusion in the mapping cone of `biprod.lift (-𝟙) 𝟙`. Thus its source is precisely `L_T[0] ⊞ L_T[0]`, its target has one `L_T` in degree -1 and two in degree 0, with differential `(-id,id)`, and all other terms zero. |
| Identification includes the boundary arrow and both endpoint maps | `IntervalComparison.comparison` is an isomorphism in the arrow category, not just an object isomorphism. `vertex` identifies the zero-simplex tensor with the free representable in degree zero. `initial` and `final` make the two actual normalized boundary-face maps equal the corresponding biproduct inclusions. `endpoint` uses omitted face 1 for vertex 0 and omitted face 0 for vertex 1. The same adjunction therefore identifies the lifting squares, preserving their endpoint maps. |

The global package `HomotopyComparison` records only the Kan, homotopy and
translation comparisons in the requested assertion, using the actual already
recorded Dold–Kan realization. It does not select a new realization or import
the additional dg-enrichment conclusion of `DoldKanHomology.Statement` into
the requested conclusion.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.DgPresheafModelLocalizations`:
  `HomotopicalAlgebra.DgPresheaf`, `DgSheafCohomologyEquivalence`,
  `DgProjectiveModelData`, `DgBousfieldModelData`, `DgLeftQuillen`,
  and the full signature/docstring of `dgPresheafModelLocalizations`.
- `Sheaf.CategoryTheory.SimplicialPresheafLocalizationComparison`:
  `SSet.ProjectivePresheaf.simplicial_presheaf_localization_comparison`,
  in particular its usual-enrichment, replacement, and localized-class conventions.
- `Sheaf.AlgebraicTopology.SimplicialPresheafProjectiveModel`:
  `representable`, `tensor`, `IsUsualEnrichment` and the full projective-model signature.
- `Sheaf.CategoryTheory.DerivedHypersheafPresentation`:
  `freePresheaf`, `IsHypercover`, `hypercoverAugmentation`.
- `Sheaf.CategoryTheory.BoundedRepresentableHypercover`:
  `AugmentedOver`, `augmentedOverToAugmented` (no summand bound is imposed).
- `Sheaf.CategoryTheory.LocalSimplicialPresheafMaps`:
  `IsLocalWeakEquivalence`, with its `Pi` and `piMap` tests.
- `Sheaf.Paper.DoldKanHomology`: `ModuleComplex`, `connectiveTruncation`,
  `simplicialModule`, `simplicialRealization`, `vertexPoint`, `zeroVertex`,
  `vertexPoint_natural`, and the signature/docstring of `doldKanHomology`.
- Mathlib's `CategoryTheory.presheafToSheaf`, `DerivedCategory`, `SSet`,
  `Abelian.DoldKan.N`, `normalizedMooreComplex`, `embeddingDownNat.extendFunctor`,
  `HomologicalComplex.complexOfFunctorsToFunctorToComplex`, `Functor.flipping`,
  and `CochainComplex.mappingCone.inr` supply the underlying canonical constructions.
- Proof-only imports include `Sheaf.CategoryTheory.BousfieldQuillenDescent`
  (`bousfield_quillen_descent`), Mathlib's normalized/alternating homotopy equivalence,
  `sheafifyComposeIso`/its unit identity, and the slice sheafification compatibility.
  `lem-cbc-simplicial-module-model` has no recorded declaration at the read revision,
  so there is no module for that proof-only dependency to import. Its use remains
  explicit in the proof docstring. No statement dependency is missing.

The four added `stmt_deps` are existing landed nodes for the hypercover
presentation, fixed-target slice, local simplicial-map predicate and Dold–Kan
realization. They record the declarations actually used in the signature and
constructions. A read-only dependency traversal checked that none reaches this
item, so these additions create no cycle. No new node or dependency repair is needed.

Edge cases checked before and after writing: the empty site makes all sectionwise
conditions vacuous and creates no representable interval case; the empty family
`I` is allowed and localizes at the empty family; arbitrary nondense H is allowed;
the zero coefficient ring gives zero free complexes and contractible realizations;
π₀ is separate from positive groups, with m+1 covering every positive degree;
positive cochain degrees are discarded only by the specified smart truncation;
no boundedness on K, cofibrancy on U, subcanonicity or site fibre products is imposed.
The cone convention was checked: its cross differential is the chosen map,
so `(-id,id)` has exactly the sign in the node. The two omitted-face indices
were checked against `boundary.ι_ι`.

Searches (2026-10-17):

- `msearch.py ... leanfinder "Free normalized Dold Kan functor from simplicial presheaves to unbounded module complexes is left Quillen for hypercover localization"`:
  eight hits, including `CategoryTheory.Abelian.DoldKan.N` and `.Γ`; no assembled Quillen theorem.
- `msearch.py ... loogle "AlgebraicTopology.DoldKan.N, AlgebraicTopology.DoldKan.Γ"`:
  no hits, first expected identifier unknown. Reading the semantic hits resolved the correct namespace.
- `msearch.py ... grep "DoldKan|NormalizedMooreComplex|localWeakEquivalence" AlgebraicTopology`:
  normalized Moore complexes and normalization comparison APIs; no hypercover-local adjunction.
- `msearch.py ... leansearch "Dold Kan normalized free simplicial modules Quillen adjunction presheaves localization"`:
  eight hits, ordinary free/forget and Dold–Kan APIs, no assembled theorem.
- `msearch.py ... leansearch "hypercover augmented semirepresentable simplicial presheaf matching covering sieve"`:
  eight ordinary zero/one-hypercover hits; no replacement of the existing project-specific all-degree definition.
- `rg -n "DoldKan|doldKan|NormalizedMoore|connectiveTruncation|localWeakEquiv"` in upstream
  `WeilConjectures`, and the required `grep -rn` for this item id: no matching theorem.
- Searches of `lean/Sheaf` found `DoldKanHomology`, the recorded hypercover-presentation
  and local-simplicial-map interfaces; all are reused, with no copied definition.
- `tools/blueprint_refs.py search hypercover` and DAG searches confirmed the existing
  hypercover-related nodes. `dag/lean_names_upstream.json` and upstream/source searches
  have no name collision with the new namespace or declarations.

Compilation: `scompile.py NA lem-cbc-dold-kan-hypercover-quillen <module>` succeeds
for both sandbox and final module-path compilation, with no errors or warnings.
The only `sorry` is the requested theorem. No STATEMENT-DISPUTED issue was found.

## Second reading by NA

A separate pass in this worker reopened the node and the full generated module.
The dispatcher's explicit instruction forbids starting a second agent; this section
records that separate reading, not a claimed independent-agent review. The
maintainer's independent delivery review remains the independent check.

The pass checked every row above against the signature and definitions. It found
and fixed an initially incorrect positional invocation of `Functor.flipping` and
residual universe names in the homotopy comparison; final compilation is clean.
It verified that smart truncation uses cycles in degree zero, that normalization
uses kernels of the positive-index faces, and that all integer shifts are retained.
The H-localization tests refer to original projective derived mapping spaces,
with a genuine Q and its natural trivial fibration; no projective cofibrancy or
density was added for H. The local-equivalence predicate includes every vertex
and restriction on every slice. The interval comparison is an arrow isomorphism
with separate initial/final equations, so it does not lose the endpoint maps.
No natural statement was changed, no hollow definition was introduced, and no
remaining mismatch was found in this pass.
