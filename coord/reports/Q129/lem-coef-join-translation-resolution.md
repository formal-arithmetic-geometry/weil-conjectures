## Worker report

Group Q129, stage 2, 2026-10-17. Item: `lem-coef-join-translation-resolution`.
Module: `Sheaf.AlgebraicTopology.JoinTranslationResolution`.
Main declaration: `SSet.Enhanced.join_translation_resolution`.

The module constructs the exact ordered-block translation, its two restriction maps,
and the natural transformations retaining their dependence on the simplicial set.
Only the main theorem is postponed, with `sorry`. Its docstring carries all ten DAG
proof steps and their prerequisite names. The six helper definitions contain real
functors and natural transformations; their proof fields check only the structural
functor/naturality laws, using existing Mathlib equations. No mathematical theorem
is proved here. The node copy changes only `lean`; there is no statement correction,
new node, dependency-module repair, or statement dispute.

The prior unfinished sandbox also had a fresh definition `SSet.disc` and a node for
it. Those files have been removed: `Functor.const SimplexCategoryᵒᵖ` already supplies
exactly this notion, and an additional definition would violate one definition per
notion. The prior nested handwritten functor failed to elaborate; composing
Mathlib's opposite-product equivalence, ordinal-sum functor, whiskering and currying
now gives the same degree/operator formulas and compiles without a heartbeat increase.
The maps have also been packaged as natural transformations in `X`, rather than
leaving that part of the final sentence only in prose.

### Clause and hypothesis correspondence

| Node clause | Lean rendering |
| --- | --- |
| Every small simplicial set `X` | `(X : SSet.{u})`, with `universe u` explicitly bound; no fibrancy, nonemptiness, finiteness, or other hypothesis on `X`. |
| Each integer `n ≥ 0` | `n : SimplexCategoryᵒᵖ`; its underlying object is the finite nonempty ordinal `[n.unop.len]`. Every natural-number degree occurs as `op ⦋n⦌`. |
| `(t_n X)_m = X_(n+m+1)` | `joinTranslations.obj X`, constructed by precomposition along `joinOrdinals.op` and then `Functor.curry`; its `(n,m)` object is definitionally `X.obj (op (AugmentedSimplexCategory.tensorObjOf n.unop m.unop))`. Mathlib's `tensorObjOf` is `[n.len + m.len + 1]`. |
| First block precedes second | `joinOrdinals.map` is Mathlib's `tensorHomOf`: in `Fin.addCases` the first summand uses `f.1` and the second uses `f.2`, translated above the first block. The underlying definition and the `inl'_eval`/`inr'_eval` formulas were read in `Augmented/Monoidal.lean`. |
| Inner simplex operator `id_[n] star beta` | Currying fixes `n`; the inner map is `X.map (joinOrdinals.map (𝟙 n.unop, beta.unop)).op`, definitionally. |
| Outer simplex operator `alpha star id_[m]`; simplicial diagram in `n` | The outer map of `joinTranslations.obj X` has inner component `X.map (joinOrdinals.map (alpha.unop, 𝟙 m.unop)).op`. The functor records all identity and composition laws. |
| `disc(X_n)` has constant sets and identity operators | `(Functor.const SimplexCategoryᵒᵖ).obj (X.obj n)`. This is Mathlib's existing constant functor, with no independent discrete-set construction. |
| `p_n` is restriction to the first block | `joinTranslationProjection X n`, whose `m` component is precisely `X.map (AugmentedSimplexCategory.inl' n.unop m.unop).op`. Its target is the constant simplicial set above. |
| `e_n` is restriction to the last block | `(joinTranslationAugmentation X).app n`; its `m` component is precisely `X.map (AugmentedSimplexCategory.inr' n.unop m.unop).op`. |
| Augmentation compatible with the outer simplicial diagram | `joinTranslationAugmentation X` is itself a natural transformation `joinTranslations.obj X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X`, not a bare family. |
| For every `n`, `p_n` is a weak homotopy equivalence | First conjunct of `join_translation_resolution`, universally quantified over `SimplexCategoryᵒᵖ`, uses the dependency's `SSet.Enhanced.IsWeakHomotopyEquivalence`. |
| Coherent diagram of the represented spaces | `FiniteReedy.diagram q (joinTranslations.obj X)` is the actual nerve/evaluation comparison followed by `q`. |
| Specified coherent cocone induced by `e` | `FiniteReedy.transformation q (joinTranslationAugmentation X)` is the image of the actual strict last-block transformation. |
| The apex is the space represented by `X` | `FiniteReedy.object q X`, the actual localization vertex of `X`, not an unspecified equivalent apex. |
| This cocone exhibits that apex as the colimit in spaces | `FiniteReedy.IsColimitEdge ... (object q X) (transformation q ...)`. Its definition requires a colimiting vertex of the dependency's actual coherent comma cocone category, with both the apex and its transformation equal to these specified data. |
| Naturality in `X` and all indicated simplex operators | `joinTranslations` is a functor of `X`. `joinTranslationProjections` is a natural transformation from it to the degreewise constant diagram functor; its inner `app X` is natural in `n`. `joinTranslationAugmentations` is a natural transformation of `X`, with components `joinTranslationAugmentation X`. Together with the inner simplicial naturality of both maps, these retain every stated naturality square. |
| No Kan condition on `X` | There is no `[KanComplex X]` binder, and no Kan witness for a translation or for its discrete target is assumed. |

The phrase “space represented by a Kan replacement” is expressed without choosing
replacement data: the second conjunct ranges over presentations
`q : largeNerve SSet ⟶ C` with `IsLocalization` at the SAME realization weak
equivalences. This is a presentation-independent way to state the colimit in spaces,
using the public interface already used by the recorded Kan–Quillen dependency.
`IsLocalization` includes that `C` is a quasicategory and the full coherent functor
universal property. The model theorem guarantees such a presentation exists; thus
this is not a vacuous test on an unconstructed structure. Its functorial fibrant
replacement identifies `q X` with the space of any Kan replacement, naturally on
objects, maps, diagrams, and the specified transformation. The additional `C, q`
binders select a model of the category of spaces; they impose no condition on `X`.
`C : SSet.{u+1}` accommodates the category of all `u`-small simplicial sets, whose
objects lie in `Type (u+1)` and morphisms in `Type u`. The countable simplex category
is small and is lifted by the existing `largeNerve` interface, without excluding `u=0`.

### Recorded dependencies and interfaces read

* `def-weil-pbc-simplicial-set` is a Mathlib leaf. Read `SSet` in
  `Mathlib.AlgebraicTopology.SimplicialSet.Basic`, `SSet.degenerate` and
  `SSet.nonDegenerate` in `...Degenerate`, `SSet.Subcomplex` in `...Subcomplex`, and
  `SSet.Finite` in `...Finite`. The module uses the actual `SSet` functor category.
* `def-cbc-enhanced-diagrams-cones`: read the full module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`, including
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, `coconeCategory`, `IsInitial` and
  `IsColimiting`, with their full signatures and docstrings. Weak equivalence uses
  realized path components and every positive based homotopy group. The colimit
  predicate below uses these exact comma and initial-object definitions.
* `lem-coef-kan-quillen-right-proper`: read all of
  `Sheaf.AlgebraicTopology.KanQuillenRightProper`, especially
  `SSet.KanQuillen.weakEquivalenceStructure` and `right_proper_kan_quillen`.
  It fixes weak equivalences to the preceding realization definition and supplies
  the model, functorial factorizations, and an actual coherent localization.
* The public `Sheaf.CategoryTheory.FiniteReedyLocalization` interface imported by
  that dependency was read at `largeNerve`, `comparison`, `IsLocalization`,
  `transformation`, `diagram`, `object` and `IsColimitEdge`. Only its definition
  interface is used in the signature, not its finite-index theorem. The translation
  index here is the full simplex category, with no finite-index restriction.
* Mathlib's `AugmentedSimplexCategory.tensorObjOf`, `tensorHomOf`, `inl'`, `inr'`,
  `tensor_id`, `tensorHom_comp_tensorHom`, `inl_comp_tensorHom` and
  `inr_comp_tensorHom` come from `Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal`.
  They are used rather than a second definition of finite ordered-block maps.
  `CategoryTheory.prodOpEquiv`, `Functor.whiskeringLeft`, `Functor.whiskeringRight`,
  `Functor.curry` and `Functor.const` retain the functor structure without private notation.

All currently recorded proof-dependency modules are imported without `public` when
not already statement imports: `RealizationFiniteLimits`, `BisimplicialDiagonalEquivalence`,
`ReedyModelStructure`, `ModelInfinityDerivedAdjunction`, `CoherentNerveComparison`,
`KanMappingHomotopyInvariance`, `HammockInfinityLocalization`,
`EnhancedFunctorConeCalculus`, and `SmallDiagramModelRectification` in their recorded
`Sheaf` topics. The Mathlib proof leaves import `ExtraDegeneracy`, `SimplicialSet.Degenerate`
and `SimplicialSet.AnodyneExtensions.PushoutProduct`. The one proof prerequisite
`lem-coef-kan-enriched-hammock-comparison` has no recorded `lean` or `mathlib_match`
in the read-only DAG; there is no module to import yet. It is not needed to type
this statement. No import cycle was found by traversal of the current source import
closure. No dependency notion has been copied or restated.

### Sources and edge cases

Opened [Higher Algebra](https://www.math.harvard.edu/~lurie/papers/HA.pdf), Notation
the project server and Lemmas the project server–13, printed pp. 112–113. The first result concerns the
first restriction, and the next concerns the augmentation colimit. This delivery
retains the DAG's explicit formulas and its proof route. It does not replace the
coherent universal property by an ordinary colimit or by a statement about apex objects.

* `X = ∅`: every degree and every translation is empty; the first restriction is
  the empty identity, so its component bijection and all based tests are valid.
  The augmentation is the diagram of empty spaces' specified cocone with empty apex.
* `X = Δ⁰` or a constant discrete simplicial set: all translations are the same
  constant set and both restrictions are identities. The full simplex index has
  contractible nerve; its constant-space colimit has the stated apex, even for
  a disconnected set. No connectedness assertion about `X` is made.
* `n=0`, `m=0`: the translation starts at `X₁`, and the two restrictions select
  the first and last vertex, respectively. The formulas do not use truncated
  subtraction or assume that either index is positive.
* `X=Δ¹` is a non-Kan test. `t_0 X` has components classified by the first
  vertex (the fiber starting at 0 contains the edge 0→1), so projection to
  the two-point `X₀` is consistent. Its last restriction supplies the interval
  coherent resolution. No horn-filling assumption is smuggled into either map.
* Arbitrary ordinal maps include surjections/degeneracies and every face, not just
  injective maps. The functor and natural-transformation laws enforce all of them.

### Searches and duplicate check

The msearch queries and raw results below include the earlier attempt's searches
and this worker's repeat searches. The repeat LeanFinder query returned only
skeleton/coskeleton, standard-simplex extra degeneracies, and classifying-space
cover results. LeanSearch returned ordinary augmentation, realization, and Yoneda
primitives. None is this ordered-block resolution with both conclusions.
`ExtraDegeneracy.section_`, `section_comp_hom`, and `homotopy` at lines 126–174 were
read: they require already supplied extra-degeneracy data. They are proof tools,
not a statement of the item. `ExtraDegeneracy.homotopyEquiv` at lines 411–420
contracts a preadditive alternating face complex, a different object.

Direct `rg` on `WeilConjectures/` and `lean/Sheaf/` for
`joinTranslation|join_translation|decalage|décalage|translation.*resolution`
found only the prose use in `EnrichedMarkedRealization.lean`, not a declaration.
`grep -rn 'lem-coef-join-translation-resolution' WeilConjectures/` returned no hit.
The seven delivered declaration names were also checked in
`dag/lean_names_upstream.json`, Mathlib's algebraic topology tree, the upstream
project, and `lean/Sheaf`: no declaration collision. The existing constant functor
was used, so no new discrete-simplicial-set node is delivered.

```jsonl
{"t": "2026-10-17T00:05:11Z", "tool": "leanfinder", "query": "Ordinal sum decalage simplicial set homotopy colimit resolution", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["SSet.Augmented.StandardSimplex.extraDegeneracy", "SSet.ι₀_comp", "SSet.S1", "SSet.ι₁_comp", "AlgebraicTopology.DoldKan.Γ₀.Obj.map", "SSet.prodStdSimplex.orderHomOfSimplex_coe", "AlgebraicTopology.DoldKan.Γ₀.Obj.map_on_summand₀'", "SSet.horn.isColimit"], "digest": "dde735d16e6336ec"}
{"t": "2026-10-17T00:05:11Z", "tool": "loogle", "query": "SSet, CategoryTheory.Functor.const", "sub": "", "ok": true, "n_hits": 10, "note": "", "top": ["SSet.relativeCellComplexOfMono_incl_app", "SSet.relativeCellComplexOfMono_isColimit", "SSet.StrictSegal.isPointwiseRightKanExtensionAt.fac_aux₃", "SSet.StrictSegal.isPointwiseRightKanExtensionAt.fac_aux₁", "SSet.StrictSegal.isPointwiseRightKanExtensionAt.fac_aux₂", "CategoryTheory.SimplicialThickening.id_app", "SSet.iSup_range_eq_top_of_isColimit", "SSet.range_eq_iSup_of_isColimit"], "digest": "17fd33e0b2120dd9"}
{"t": "2026-10-17T00:05:11Z", "tool": "grep", "query": "decalage|décalage|translation|constant", "sub": "AlgebraicTopology/SimplicialSet", "ok": true, "n_hits": 9, "note": "", "top": ["Mathlib/AlgebraicTopology/SimplicialSet/KanComplex/MulStruct.lean", "Mathlib/AlgebraicTopology/SimplicialSet/KanComplex/MulStruct.lean", "Mathlib/AlgebraicTopology/SimplicialSet/KanComplex/MulStruct.lean", "Mathlib/AlgebraicTopology/SimplicialSet/KanComplex/MulStruct.lean", "Mathlib/AlgebraicTopology/SimplicialSet/KanComplex/MulStruct.lean", "Mathlib/AlgebraicTopology/SimplicialSet/Basic.lean", "Mathlib/AlgebraicTopology/SimplicialSet/CompStruct.lean", "Mathlib/AlgebraicTopology/SimplicialSet/CompStructTruncated.lean"], "digest": "6bbd0d6dc66bbce6"}
{"t": "2026-10-17T00:14:39Z", "tool": "leansearch", "query": "A simplicial set ordinal sum translation is weakly equivalent to its discrete n simplices and has homotopy colimit the original simplicial set", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["SSet.toTop", "SSet", "SSet.yonedaEquiv", "SSet.Finite.instIsFinitelyPresentableObjSimplexCategoryStdSimplex", "SSet.horn.isColimit", "SimplexCategory.toTop", "SSet.Truncated.hasColimits", "SimplexCategory.skeletal"], "digest": "1fd865082cb8758d"}
{"t": "2026-10-17T00:21:08Z", "tool": "leanfinder", "query": "For a simplicial set X the join translation t_n X with m simplices X_(n+m+1) is weakly equivalent to discrete X_n and its simplicial homotopy colimit is X", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["SSet.hasColimits", "SSet.modelCategoryQuillen.J", "SSet.modelCategoryQuillen.I", "SSet.sk", "SSet.horn.isColimit", "SSet.ι₀", "SSet.ι₁", "CategoryTheory.hoFunctor.isIso_prodComparison_stdSimplex"], "digest": "a42fbd621187fe6e"}
{"t": "2026-10-17T00:51:54Z", "tool": "grep", "query": "decalage|décalage|joinTranslation|join_translation", "sub": "AlgebraicTopology", "ok": true, "n_hits": 0, "note": "", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-17T00:51:54Z", "tool": "leanfinder", "query": "For each simplicial set X the ordinal sum translation t_n X has m simplices X n+m+1, is weakly equivalent to discrete X_n and augments to a coherent colimit resolution", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["SSet.cosk", "SSet.Augmented.StandardSimplex.extraDegeneracy", "CategoryTheory.SimplicialObject.cosk", "SSet.Augmented", "CategoryTheory.SimplicialObject.sk", "SSet.Augmented.stdSimplex", "classifyingSpaceUniversalCover.extraDegeneracyCompForgetAugmented", "SSet.Augmented.StandardSimplex.nonempty_extraDegeneracy_stdSimplex"], "digest": "4614d6cc1248f6f0"}
{"t": "2026-10-17T00:51:54Z", "tool": "loogle", "query": "SSet, SimplexCategory, AugmentedSimplexCategory.tensorHomOf", "sub": "", "ok": true, "n_hits": 0, "note": "", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-17T00:52:31Z", "tool": "leansearch", "query": "The simplicial ordinal sum translation of a simplicial set is weakly equivalent to its discrete set of n simplices and its augmentation is a homotopy colimit", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["CategoryTheory.SimplicialObject.augment", "SSet.toTop", "SSet", "SSet.Augmented.stdSimplex_obj_left", "SSet.Augmented.stdSimplex", "SSet.yonedaEquiv", "SSet.Truncated", "SSet.S"], "digest": "545ff9fe4ce4b350"}
```

### Validation

`scompile.py Q129 lem-coef-join-translation-resolution
lean/Sheaf/AlgebraicTopology/JoinTranslationResolution.lean` passed both sandbox
and library-mode checks with no errors or warnings, under the required 60-second
file limit and without increasing heartbeats. The node's recorded signature is
copied verbatim from the file. `autoImplicit` is explicitly disabled and the one
universe is declared. The dry run is the final check; delivery is reserved for the
independent second reader.

## Second reading by Q129

I opened the stage-1 node copy, the Lean module, every statement dependency, the
recorded localization interfaces, and HA pp. 112--113 (Notation the project server and
Lemmas the project server--the project server). The node's objects and clauses match as follows.

* The arbitrary small simplicial set is `(X : SSet.{u})`; there is no Kan,
  finiteness, nonemptiness, or fibrancy hypothesis. The integer degree `n` is
  `SimplexCategoryᵒᵖ`, whose skeletal objects are exactly the finite ordinals.
* The translation `t_n X` is `(joinTranslations.obj X).obj n`; its degree-`m`
  value is definitionally `X.obj (op (tensorObjOf n.unop m.unop))`, hence
  `X_(n+m+1)`. `joinOrdinals.map` is Mathlib's ordinal-sum `tensorHomOf`, with
  the first summand before the translated second summand. Currying gives both
  the inner `id_[n] star beta` operators and the outer `alpha star id_[m]`
  diagram operators, including all identities and compositions.
* The first-block restriction is `joinTranslationProjection X n`, with target
  `(Functor.const SimplexCategoryᵒᵖ).obj (X.obj n)`, exactly the constant
  simplicial set on `X_n`; its components are `X.map (inl' n.unop m.unop).op`.
  The last-block restriction is `joinTranslationAugmentation X`, with components
  `X.map (inr' n.unop m.unop).op`. `joinTranslationProjections` and
  `joinTranslationAugmentations` are natural transformations in `X` and in the
  outer simplex variable, so the displayed maps retain the node's naturality.
* The first conclusion is rendered by
  `∀ n, IsWeakHomotopyEquivalence (joinTranslationProjection X n)`, using the
  exact weak-equivalence predicate of `def-cbc-enhanced-diagrams-cones`.
* The coherent cocone conclusion is rendered for every localization presentation
  `q : largeNerve SSet.{u} ⟶ C` satisfying the recorded weak-equivalence
  `IsLocalization`: its diagram is `diagram q (joinTranslations.obj X)`, its
  apex is the specified `object q X`, and its edge is the specified
  `transformation q (joinTranslationAugmentation X)`, with
  `IsColimitEdge` requiring the actual cocone vertex and colimiting predicate.
  This is the presentation-independent formalization of the node's space
  represented by a Kan replacement; no arbitrary apex or cocone is introduced.
* There is no Kan condition on `X`; the statement quantifies over all `SSet`.

I checked the edge cases explicitly: the empty simplicial set gives empty
translations and the empty specified cocone; a point and constant discrete sets
give identity translations/restrictions; `n = 0` and inner degree `m = 0` use
`tensorObjOf` without subtraction; a non-Kan test such as `Δ¹` is included; and
all degeneracy and face maps are covered by the functorial ordinal-sum maps.
The universe `u` is explicit, while the localization presentation is in
`SSet.{u+1}`, so no small-index or universe case is excluded.

For duplicate checking I repeated LeanFinder, Loogle, LeanSearch, and direct
`rg` searches in Mathlib, `WeilConjectures/`, and `lean/Sheaf/` for
`joinTranslation`, `join_translation`, `decalage`, `translation`, and the
ordinal-sum construction. They found only standard simplex/coskeleton,
extra-degeneracy, realization, and unrelated join declarations. I read the
returned `ExtraDegeneracy` declarations; they are contraction tools with supplied
extra-degeneracy data, not this translation resolution. Mathlib's
`AugmentedSimplexCategory.tensorObjOf`, `tensorHomOf`, `inl'`, `inr'`, and
their composition lemmas are the single existing ordinal-sum construction used
here.

No mismatch was found, so no Lean or node repair was needed. The sandbox module
was recompiled with `scompile.py` after this reading and passed both sandbox and
library-mode checks cleanly; the node copy's `lean.statement` is verbatim the
theorem signature.
