## Worker report

The module `Sheaf.CategoryTheory.DerivedColimitBar` states
`CategoryTheory.categoryColimitBarSystem_exists`, with `sorry` as its only theorem proof.
It asserts the existence of the complete system of bar models and their canonical maps.
The records `CategoryColimitPoint`, `CategoryColimitBarModel`, and
`CategoryColimitBarSystem` expand that assertion into explicit data and laws. They are
helpers for this node's own notion. There is no choice of data from the postponed
existence theorem, no opaque placeholder definition, and no new independent DAG notion.
All helper declarations are listed in `lean.declarations` and have source docstrings.
The node changes only in `lean`; there is no statement correction or dependency repair.

Sources read: Stacks `sites-cohomology.tex`, lines 9944–9960 (08PD), 10016–10042
(08PF), 10044–10113 (08PG), 10117–10165 (08PH), and the 07AC existence proof
at lines 9320 onward. The full fourteen-step DAG proof is retained in the main
theorem's docstring, including the acyclic-resolution comparisons and prism signs.
The natural-transformation extension is the node's supplied prism argument, rather
than an assertion that Stacks explicitly states that extension.

Clause-by-clause correspondence:

- A small category in the chosen universe is `E : Type u` with `[SmallCategory E]`.
  Other indexing categories have the same universe convention, and coefficient rings
  are `R S T : Type u` with `CommRing`. One may take the common ambient universe as
  large as necessary. Modules are `ModuleCat.{u} R`; the standard localization is in
  universe `u + 1`. The two named instance definitions use
  `HasDerivedCategory.standard`, with real data and no proof placeholders.
- The identity-cover topology is literally `⊥ : GrothendieckTopology E`.
  `sheafBotEquivalence` gives all presheaves as sheaves. The point is the small
  category `Discrete PUnit.{u + 1}`, which has one object and one arrow.
- The constant coefficient ring is the actual definition `categoryBarConstantRing`:
  transport the constant `RingCat.of R` functor through `sheafBotEquivalence.inverse`.
  `CategoryColimitPoint.modules` is the equivalence from the dependency's
  `ringedSiteModules` to `Eᵒᵖ ⥤ ModuleCat R`. Its evaluation isomorphisms are linear,
  natural in the module, and its `restriction` field identifies the actual restriction
  maps. This is not a replacement module category with a different scalar action.
- The geometric morphism is `CategoryColimitPoint.morphism : RingedToposMorphism ...`.
  Its `inverse` isomorphism identifies inverse image with point evaluation followed
  by the constant-presheaf functor and the bottom-topology sheaf equivalences.
  Its `ringMap` equality says that the structural map, under this identification,
  is the identity of the constant ring. The dependency record supplies the geometric
  adjunction, preservation of finite limits, and the induced module direct image.
- Ordinary lower shriek is Mathlib's actual `colim`, not an arbitrary left adjoint.
  `colimConstAdj` fixes its adjunction to `Functor.const Eᵒᵖ`. Exactness of this
  constant functor is also enforced by the instances required by `mapDerivedCategory`.
  The additivity witness for `colim` is a field in the existence conclusion, not an
  extra hypothesis on the category.
- The unbounded total derived functor is `CategoryColimitBarModel.derived` between
  Mathlib `DerivedCategory` objects; its `comparison` and `universal` are precisely
  `Functor.IsLeftDerivedFunctor` for the ordinary colimit applied to complexes.
  `pointwise` asserts Mathlib pointwise derivability at every complex.
  `stacksPointwise` additionally asserts the exact essentially-constant denominator
  pro-diagram condition on the homotopy category: this is the defining expression
  in the recorded `IsTriangulatedLeftDerivedValue`, unfolded so it need not introduce
  an extra saturated-system hypothesis. Its value is the displayed derived value.
- `shift` and `triangulated` assert triangulatedness. `adjunction` is the adjunction
  to the exact constant functor on derived categories. `transpose` fixes the
  adjunction with the termwise ordinary adjunction and the universal comparison,
  including the `mapDerivedCategoryFactors` transport.
- `bar` is the functor `K_E`. `coordinates F n` identifies its degree `-n` with the
  coproduct over `c : ComposableArrows E n` of `F.obj (op c.right)`. The vertices
  of `c` are `U_n,...,U_0`, so its right endpoint is exactly `U_0`.
  `positive` makes every positive-degree term a zero object.
- `categoryBarDelete c j` precomposes the chain with the simplex coface deleting
  vertex `j`; functoriality composes the adjacent arrows. Thus `j` deletes `U_(n-j)`.
  `categoryBarFaceCoefficient` applies `F` to the arrow from the last retained
  vertex to the old last vertex. For all but the last coface this is the identity;
  for the last coface it is precisely restriction along `U_1 → U_0`.
  `differential` is the sum of these faces with `(-1 : ℤ)^j.val` on each generator.
  The type `CochainComplex` includes the required square-zero law.
- `coefficientMap` specifies functoriality on each generator. `exact` states that
  every objectwise short exact sequence gives a short exact sequence of complexes;
  in the abelian category of complexes this is degreewise short exactness.
- `model` is the natural isomorphism from the degree-zero input's derived colimit
  to `Q(K_E F)`. It is normalized by `model_eq`: invert the derived image of the
  quasi-isomorphic resolution augmentation, then apply the universal comparison
  on the acyclic resolution, then its colimit identification. `quasiIso` and
  `acyclic` ensure those maps are invertible. This precludes treating a bare
  unnormalized isomorphism as the canonical derived model.
- `CategoryColimitBarSystem.map` quantifies over all indexing functors `u`, all
  ring homomorphisms `φ : R →+* S`, and precisely a natural transformation
  `t : F ⟶ u.op ⋙ G ⋙ ModuleCat.restrictScalars φ`. This is exactly a semilinear
  natural coefficient map, with `u⁻¹` as precomposition. Its target is the scalar
  restriction of the target bar complex, with no flatness assumption.
- `formula` states the specified map on every chain and coefficient element:
  `(c,x)` goes to `(c ⋙ u, t.app (op c.right) x)`.
  `lift_aug` makes the chosen same-ring resolution lift commute with augmentations;
  `canonical` identifies its ordinary colimit with this exact bar map using the
  actual `colimit.pre` reindexing map. Along with `model_eq` and the normalized
  derived adjunction, this specifies the canonical derived map of 08PD, not merely
  some map with the right homology groups. `scalarIso`, `scalarFormula`, and
  `scalarCanonical` identify the general semilinear map with this same-ring map
  followed by the generatorwise scalar-restriction identification.
- `identity` asserts the identity at every degree and element. `composition`
  asserts the law for composable functors and ring maps, after the canonical
  underlying scalar identifications. Its `a` is the composite coefficient map,
  specified at every object and element; the universal quantifier over `a` does
  not replace the coefficient map with an unconstrained morphism. Such `a` exists
  by composing the two given semilinear natural maps and the standard scalar
  restriction associator.
- `modelBoundary` identifies the connecting morphism under the canonical model
  with the image under the triangulated derived functor of the original connecting
  morphism. It uses Mathlib's `DerivedCategory.triangleOfSESδ`, with its cone sign.
  `scalarExact` includes all scalar-restricted target sequences, and `connecting`
  asserts boundary naturality for the maps of those short exact sequences.
  Its two square hypotheses are exactly the definition of a morphism of the
  displayed sequences. Coefficient squares imply these chain squares by `formula`
  and the coproduct coordinates, so no original map of sequences is excluded.
- `homotopy` quantifies over arbitrary parallel `v,w`, arbitrary `η : v ⟶ w`,
  and the original semilinear coefficient map `t` into the `w` pullback.
  `NatTrans.op η` reverses the coefficient direction; whiskering with `G` gives
  `G(η)` and precomposing with `t` gives precisely `G(η)t`.
  Both `Nonempty (Homotopy ...)` and equality after `DerivedCategory.Q.map` are
  asserted. Taking `η` to be the hom of a natural isomorphism gives the last clause,
  including the indicated coefficient identifications.

Dependency declarations and source signatures read:

- `def-weil-size-convention`: the recorded metatheoretic convention, with no
  declaration to import; implemented by the explicit universe levels above.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, its entire presieve-site definition.
  This fixes the site convention; the particular topology is the Mathlib bottom topology.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, the public abbreviation of `SheafOfModules`.
  Also read Mathlib `SheafOfModules`, its module evaluations and morphism definitions.
- `Sheaf.CategoryTheory.RingedToposMorphism`:
  `CategoryTheory.RingedToposMorphism`, the entire structure including the geometric
  adjunction, finite-limit preservation, structural ring laws, and induced module image.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colim`, `colimit.pre`,
  `colimit.desc`, and `colimConstAdj`, with their universal-property signatures.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory`, `DerivedCategory.Q`, and `Qh`.
- `Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem`:
  `Functor.IsTriangulatedLeftDerivedValue`, `IsTriangulatedLeftDerivedDefinedAt`,
  and their underlying `IsEssentiallyConstantProDiagram` from
  `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro`.
- The two proof-only nodes `lem-trf-continuous-cocontinuous-derived-shriek` and
  `lem-trf-bounded-above-acyclic-derived-computation` have no recorded Lean module
  or Mathlib match on the read base. There is therefore no proof-only module to
  import for them. Their mathematical statements and their uses were read; the
  full proof plan cites them in the theorem docstring. They are not prerequisites
  for typing this statement, whose derived notions already come from the recorded
  statement dependencies and Mathlib.

Edge cases checked against the formulas:

- Empty indexing categories are allowed: there is no `Nonempty E` hypothesis.
  Every chain coproduct is then zero and the colimit/derived adjunction still exists.
- Zero modules and the zero ring are allowed; no nontriviality or flatness is assumed.
- For `n=0`, the differential from degree `-1` to `0` is the retained coefficient
  at `U_0` minus its restriction at `U_1`. Positive degrees are zero.
- For `n=1` in the differential field, the input has two arrows: the three
  cofaces give exactly `(U_1→U_0,x) - (U_2→U_0,x) + (U_2→U_1,x|U_1)`.
- Identity arrows and degenerate chains are retained. No normalized-chain quotient
  accidentally removes them. Infinite categories require only finite sums of faces
  on each generator, not finite categories or finite-rank coefficients.
- A natural transformation need not be invertible; its coefficient direction is
  checked at `n=0` by the two endpoint terms of the prism homotopy.
- All categories/rings can be put in a common ambient universe. No equality of
  distinct object and morphism universes of an independently presented large site
  is imposed; the node specifically concerns small indexing categories.

Searches executed with actual outputs inspected:

- `msearch.py ... leanfinder "derived colimit of a presheaf of modules computed by
  category bar complex alternating chains"`: eight hits, ordinary module-presheaf
  colimits, their cocones and generators. None gives the derived assertion.
- `msearch.py ... loogle "SimplicialObject, LeftDerived"`: zero hits;
  `SimplicialObject` was unknown to that search index. This search was not treated
  as evidence that the underlying simplicial constructions do not exist.
- `msearch.py ... grep "simplicialReplacement|barComplex|derivedColimit|leftDerived"
  CategoryTheory`: 25 hits, primarily the derived-functor APIs. Their source
  signatures were read; none is the category bar theorem.
- `msearch.py ... leansearch "bar complex of a category with presheaf module
  coefficients"`: eight hits, including `Rep.barComplex` (group representations,
  not arbitrary categories) and ordinary presheaf module constructions. No match.
- `rg` of Mathlib's CategoryTheory and AlgebraicTopology for
  `simplicialReplacement|SimplicialReplacement|bar construction|bar resolution|alternatingFaceMapComplex`:
  the alternating-face complex exists, but no arbitrary-category coefficient
  construction or claimed derived/functorial assertion. `ComposableArrows`, `nerve`,
  and the cofaces are reused to express the exact chain-index and face operations.
- `rg` of upstream `WeilConjectures` and shared `lean/Sheaf` for
  `barComplex|simplicialReplacement|derivedColimit|lem-trf-derived-colimit-bar`:
  no matching declaration (unrelated Qbar coefficient-twist names only).
- `rg` of `dag/lean_names_upstream.json` for bar and simplicial replacements:
  no match for this assertion. Final collision search for the proposed declaration
  and helper names in Mathlib, upstream, and shared Lean found no existing matches.

Validation uses only the prescribed `scompile.py` and `deliver2.py` wrappers.
No direct Git command, global build, or write to either read-only checkout was run.

## Second reading by Q108

This is the author's separate second pass, as the dispatcher explicitly prohibits
starting other agents. The maintainer supplies the independent delivery review.
I reread the complete node, all three records, the map formulas, and the source
examples, matching every clause as detailed above.

The first pass exposed an important typing distinction: taking `η.op` without a
namespace selected the opposite-category hom of the functor category, rather than
`NatTrans.op η` between opposite functors. The file now uses `NatTrans.op` explicitly.
The other correction was the single-complex/reindexing comparison in `lift_aug`:
`HomologicalComplex.singleMapHomologicalComplex` now appears explicitly, so the
augmentation square has exactly the source's objects at every degree.
The derived model normalization, scalar comparison, and connecting-morphism
identification are all explicit fields; no clause is left as prose alone.
No mathematical statement mismatch or disputed statement remains.
