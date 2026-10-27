## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceDerivedDirectImageCoproducts` states
`AlgebraicGeometry.AlgebraicSpace.derivedDirectImage_quasiCoherent_coproducts`.
Its sole theorem has proof `sorry`; it introduces no definitions, maps, or instances.
The source read was `literature/stacks-project/spaces-perfect.tex`,
`lemma-quasi-coherence-direct-image` (08FA), part (1),
`lemma-quasi-coherence-pushforward-direct-sums` (08FB), and
`lemma-quasi-coherence-direct-sums` (08F3). The declaration docstring carries
all seven accepted DAG proof steps and their node citations.

Hypothesis and clause correspondence:

- Fixed sizes: explicit `universe u w`, `Scheme.{u}`, and the two
  `HasDerivedCategory.{w}` binders use the existing small-model interface.
  The small affine ringed site has both object and morphism universe `u`,
  its rings and module sections remain in `u`, and `w` is the arbitrary
  localization morphism universe. This follows the recorded size convention
  and the landed `def-sfb-space-derived-module-calculus`.
- Base scheme and algebraic spaces: `{S : Scheme.{u}} {X Y : AlgebraicSpace S}`;
  `f : X ⟶ Y` is a natural transformation over that same base.
- Relative quasi-compactness: `hqc : IsQuasiCompactPresheafMap f.hom.hom`.
  Its definition tests every affine scheme over Y and asks for a quasi-compact
  scheme with an etale surjective map to the pullback. This is exactly the
  scheme-test definition of quasi-compactness of the pulled-back space.
- Relative quasi-separatedness: `hqs : IsQuasiCompactPresheafMap
  (diagonalPresheafMap f.hom.hom)`. No absolute qc or qs hypothesis occurs.
- Structure sheaves, modules and their unbounded derived categories:
  `X.SmallModules`, `Y.SmallModules`, `X.DerivedModules`, `Y.DerivedModules`
  are the existing regular-functions small ringed models, identified with
  the original etale module categories by `smallModuleEquivalence`.
- The canonical K-injective derived direct image is `derivedDirectImage f`.
  Its body is `(smallModuleDirectImage f).rightDerivedFunctor`, with
  `smallModuleDirectImage` the conjugate of the specified compatible-chart
  `moduleDirectImage f`. The existing named instance
  `smallModules_hasKInjectiveResolutions` supplies K-injective computation.
- Preservation of quasi-coherent cohomology is the first conjunct:
  `∀ K : X.DerivedModules, X.derivedQCohProperty K →
  Y.derivedQCohProperty ((derivedDirectImage f).obj K)`.
  The recorded predicate quantifies over every integer cohomological degree
  and tests Mathlib `SheafOfModules.IsQuasicoherent` after the inverse module
  equivalence. It is D_QCoh inside D(all modules), not D(QCoh).
- Every small family: `(I : Type u) (E : I → X.DerivedQCoh)`.
  The family has no boundedness, finiteness, or nonemptiness assumption.
  The index universe is the chosen small module/site universe. It is
  independent of the localization morphism universe `w`.
- The canonical map and its invertibility are exactly the second conjunct:
  `IsIso (sigmaComparison (derivedDirectImage f) (fun i ↦ (E i).obj))`.
  In Mathlib/CategoryTheory/Limits/Shapes/Products.lean:668 the map is
  `Sigma.desc (fun i ↦ F.map (Sigma.ι E i))`; the coprojection equation is
  `ι_comp_sigmaComparison` at line 673. Thus it is the specified map, rather
  than existence of an unspecified isomorphism. Both coproducts are taken
  in the ambient derived categories, because the input to `sigmaComparison`
  is `(E i).obj`, not an object summed in the full subcategory.
- Ambient sums exist without an added hypothesis: the public existing
  `DerivedCategory.hasColimitsOfShape_discrete` instance supplies them from
  module sums and K-injective resolutions. In the same module,
  `DerivedCategory.isColimitCofanMkQObj` identifies the image of a termwise
  coproduct with its derived coproduct. No new termwise-sum construction is
  needed or introduced. These facts apply to the empty family as well.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `EtaleSite`, `structurePresheaf`, `structureSheaf`, `Modules`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent abbreviation of Mathlib `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, and its localization `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicGeometry.AlgebraicSpace.QCoh` and the slice sheafification instances,
  using `SheafOfModules.IsQuasicoherent` from Mathlib unchanged.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `ModuleDirectImageModel`, `moduleDirectImageModel`, `moduleDirectImage`;
  the actual compatible-chart limit and all its projections are retained.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`:
  `SmallModules`, `smallModuleRestriction`, `smallModuleEquivalence`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`:
  `DerivedModules`, `derivedQCohProperty`, `DerivedQCoh`,
  `smallModuleDirectImage`, `smallModules_hasKInjectiveResolutions`,
  `derivedDirectImage`.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`:
  `IsQuasiCompactPresheafMap` (owner `def-sfb-space-quasi-compact-presheaf-map`),
  `diagonalPresheafMap` (owner `def-sfb-presheaf-map-separated-diagonal`).
- `Mathlib.CategoryTheory.Limits.Shapes.Products`: `sigmaComparison`.
- `WeilConjectures.CategoryTheory.DerivedCategory.Coproducts`:
  `hasColimitsOfShape_discrete`, `isColimitCofanMkQObj`.

The item's `stmt_deps` gains the three already-landed owning definition nodes
`def-sfb-space-derived-module-calculus`,
`def-sfb-space-quasi-compact-presheaf-map`, and
`def-sfb-presheaf-map-separated-diagonal`; their declarations are used directly.
The last two have `existing: true` records in
`Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`; its etale-locality theorem
is not a statement dependency.
No new node or dependency module is required. The natural-language statement
and proof are unchanged. Every recorded, currently stated proof-dependency
module is imported. The four proof-only prerequisites without a Lean record
are not imported: `lem-sfb-space-qcoh-kernels-colimits`,
`lem-sfb-space-qcoh-extension-closed`,
`lem-sfb-space-derived-pushforward-upper-bound`, and
`lem-sfb-space-higher-module-image-filtered-colimits`.

Edge cases checked against the source and interfaces:

- The empty index type is admitted; ambient sums are zero and a derived
  additive direct image preserves zero. No arbitrary coproduct instance
  has been assumed just to type that comparison.
- The singleton family gives the canonical identity comparison up to
  coproduct unit isomorphisms, with the map fixed by its coprojection.
- Zero objects, empty spaces and the empty base scheme are admitted.
- Identity maps and non-qc/non-qs individual spaces are admitted whenever
  the morphism has the stated relative properties. No target compactness
  was imported from the separate upper-bound assertion of Tag 08FA.
- Unbounded families, including those without a uniform lower bound,
  are admitted. The seven-step proof uses a degreewise common truncation
  cutoff only internally, not as an additional hypothesis.
- Neither the coefficient characteristic nor a field is constrained.

Searches actually run (2026-10-24):

- `msearch.py ... leanfinder`: "Unbounded derived pushforward for quasi compact
  quasi separated algebraic spaces preserves quasi coherent cohomology and
  coproducts" returned eight underived scheme/module pushforward adjunctions
  and generic site pushforwards, no matching space-level theorem.
- `msearch.py ... loogle`: "CategoryTheory.Limits.coproductComparison,
  DerivedCategory, PreservesColimitsOfShape" returned an unknown-identifier
  diagnostic. A second query "sigmaComparison" was likewise unqualified
  and unresolved. The corrected query "CategoryTheory.Limits.sigmaComparison"
  returned eleven hits including the exact canonical generic map and its
  coprojection equation; its local source was read and is used.
- `msearch.py ... grep`: "derivedDirectImage|coproductComparison" in Mathlib
  AlgebraicGeometry returned zero matches.
- `rg -n "derivedDirectImage|lem-sfb-space-derived-pushforward-coproducts"`
  in `lean/WeilConjectures` found the existing SCHEME theorem
  `AlgebraicGeometry.derivedDirectImagePreservesDirectSums` and related
  scheme-only results. Its full statement and docstring were read; it does
  not state the algebraic-space theorem, so is not an existing match.
- `rg` in `lean/Sheaf/AlgebraicGeometry` for canonical coproduct comparisons
  and derived QCoh sums found no matching theorem, while the search for
  `derivedDirectImage` located the exact existing derived calculus.
  The item's id occurs in proof docstrings of
  `DerivedEtaleZariskiEquivalence` and `SpaceFlatProperPseudoCoherentDirectImage`,
  not as an already-stated theorem.
- Exact-name search for `derivedDirectImage_quasiCoherent_coproducts` in
  Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` returned no collision.

No statement dispute, source correction, hollow definition or added geometric
hypothesis was found. Server `scompile.py` checked the sandbox and library module
successfully (7.7 seconds and 2.5 seconds), with no errors or unexpected warnings.

## Repair of return on 645cce5d877c

H2: replaced the added theorem dependency
`lem-trf-space-qc-separated-etale-local` by the two live definition owners
`def-sfb-space-quasi-compact-presheaf-map` and
`def-sfb-presheaf-map-separated-diagonal`. Read both node statements and their
existing declaration records against the definitions in
`Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`: the first owns the affine-test
atlas predicate used by `hqc` and `hqs`, and the second owns the canonical
relative presheaf diagonal used by `hqs`. The theorem concluding etale locality
is not used by the signature. The dependency list above is corrected accordingly.

The retained sandbox was compared with current main: before repair only `lean`
and `stmt_deps` differed in the node. Rebased the node on current main, retaining
the delivered Lean record and adding the three actual definition owners. The
Lean source is byte-identical to returned head 645cce5d877c; its statement,
imports and all seven proof steps required no change. The maintainer's return
independently accepted the mathematical clauses and edge cases.

## Second reading by Q125

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
