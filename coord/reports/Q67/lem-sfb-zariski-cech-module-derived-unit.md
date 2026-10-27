## Worker report

The theorem `AlgebraicGeometry.ZariskiCechFaceTotal.zariski_cech_module_derived_unit`
states invertibility of the canonical derived augmentation unit for every ordinary
module in degree zero on an arbitrary Zariski open cover. The original statement,
proof, and proof dependencies are unchanged. One explicit definition node is added
to stmt_deps. There are no dependency repairs or statement corrections.

The source was read in spaces-simplicial.tex, the two lemmas preceding
lemma-augmentation-spectral-sequence-modules and that lemma (Tag 0D7F), and in
cohomology.tex, lemma-injective-trivial-cech and lemma-cech-cohomology (01EP/01EQ).
The source has a full simplicial index; the node explicitly asks for the injective
order-map adaptation. The declaration's proof docstring records all four steps of
the accepted DAG proof, including the total-model normalization to the actual unit.

Clause-by-clause correspondence:

- The scheme is `X : Scheme.{u}`. The set-indexed family of open immersions is
  `I : Type u`, `W : I → X.Opens`; every such open has its canonical open-subscheme
  immersion. The cover condition is exactly `hW : iSup W = ⊤`.
- The disjoint-union level of all (n+1)-tuples is presented by its usual basis:
  `Object.degree`, `Object.tuple : Fin (degree.len + 1) → I`, `Object.openSet`,
  and `Object.contained` asserting inclusion in every indexed open. It includes
  repeated indices, all finite degrees, and empty intersections.
- `Hom.drop.down : B.degree ⟶ A.degree` is Mathlib's injective monotone map;
  `Hom.tuple_eq` drops precisely those coordinates and `Hom.inclusion` includes
  the remaining open. The category instance composes these maps. No degeneracy
  arrows have been introduced.
- `verticalCoverage` contains exactly vertical presieves covering the underlying
  open. Identity of the face map implies equality of the tuple by `tuple_eq`.
  `topology` is their generated Grothendieck topology. This is the basis version
  of the total Zariski site, not the site of all opens of the base scheme.
  Sheaves on this basis are sheaves on each disjoint union together with the
  semilinear face transitions of the recorded general-total-category dependency.
- `site` is the dependency's actual `SemisimplicialRingedTotal.Site` with ring sheaf
  obtained from `X.sheaf` by continuous precomposition with `toOpens`. Its value is
  literally O_X(V), with original restriction maps. There is no arbitrary ring or
  module category. `Site.modules` is the recorded `ringedSiteModules` abbreviation.
- `restriction` is `SheafOfModules.pushforward` for `toOpens` and the identity ring
  map. Despite that API's name it has direction Mod(O_X) to Mod(O_total), with
  value G(V) on every tuple-labelled open. This is a^*, not augmentation a_*.
- `Augmentation` is a proposition containing only preparation proofs: continuity,
  additivity, exactness, existence of a right adjoint, and K-injective resolutions
  for the actual total module category. The theorem CONCLUDES `∃ A : Augmentation W`;
  none of those properties is an additional hypothesis. The existence of the
  right adjoint determines its data up to the natural isomorphism used downstream,
  exactly the universal-property exception in AGENTS.md, rather than choosing an
  arbitrary map or a functor from a mere existence claim.
- `Augmentation.pushforward` and `Augmentation.adjunction` are Mathlib's right
  adjoint and adjunction of this very restriction. They are fixed together by
  `Adjunction.ofIsLeftAdjoint`, so the unit is the canonical one.
- `derivedAdjunction` uses the existing
  `Adjunction.mapDerivedCategoryRightDerivedAdjunction`, with exact termwise
  restriction on the left and `rightDerivedFunctor` on the right. The latter is
  the ambient unbounded K-injective construction, not a bounded derived functor,
  a total-complex substitute, or an arbitrary adjunction.
- `∀ G : X.Modules` covers every module, and `A.IsUnitIso W G` unfolds to
  `IsIso ((derivedAdjunction W).unit.app
  ((DerivedCategory.singleFunctor X.Modules 0).obj G))`. This is the specified
  morphism G[0] to Ra_*(a^*G[0]) in the ordinary unbounded derived category.
- No quasicoherence, finite-index, quasi-compactness, quasi-separatedness,
  cartesian-system hypothesis, or bounded-derived-category restriction occurs.
  The existential A packages proofs of the canonical construction; it does not
  replace the conclusion by an abstract existence of an isomorphism.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` (including its
  local-affine field) and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  open families are represented by opens with their canonical immersions.
- `Mathlib.CategoryTheory.Sites.Spaces`: `Opens.grothendieckTopology`, whose
  covering sieves cover every point. Note that the actual declaration is in the
  root namespace `Opens`, not `TopologicalSpace.Opens`.
- `Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory`:
  `CategoryTheory.SemisimplicialRingedTotal.Site`, `Site.rings`, `Site.modules`,
  `Site.hasDerived`; read also `Presentation`, `AugmentationPresentation`, and
  `semisimplicial_ringed_total_category` with their normalized comparisons.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently `SheafOfModules`, and its existing abelian structure.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `HasDerivedCategory.standard`, and `DerivedCategory.Q`.
  The definition fixes the ordinary localization with morphism universe u+1,
  using `Site.hasDerived` rather than choosing another abelian structure.
- The size convention is a recorded metatheoretic convention, with no module or
  declaration. All variables and universe u are explicit; I is in the common
  universe containing the scheme and cover, as for the existing Cech API.
- The canonical exact-left derived adjunction is the published
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`,
  `CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction`; its
  signature and K-injective hypotheses were read.

The already stated proof dependencies are imported plainly:
`HomologicalComplex₂.quasiIso_of_column_augmentation`
(WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation),
`Scheme.Modules.injectiveModuleCechAugmentation_quasiIso`
(WeilConjectures.AlgebraicGeometry.InjectiveModuleCechAugmentation),
`Scheme.Modules.module_open_restriction_injectives`
(WeilConjectures.AlgebraicGeometry.ModuleOpenRestrictionInjectives),
`SheafOfModules.isGrothendieckAbelianOfUniverses`
(Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses), and
`IsGrothendieckAbelian.enoughInjectives`
(Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives).
Their full signatures and docstrings were read. The proof-only dependency
lem-sfb-face-component-injective-total-model has no recorded Lean declaration;
there is no import to add yet. Its accepted proof is retained and explicitly named
in this theorem's proof docstring. It is not needed to TYPE the statement.

Edge cases checked: for empty I the total basis is empty, and hW forces X empty,
so module sheaves are zero and the assertion is meaningful. A cover with one open
or with repeated opens retains every tuple and all injective faces, rather than
collapsing them. Empty intersections give the empty open with its empty covering.
Infinite I causes arbitrary products in the intended proof but no infinite total
diagonal: both resolution indices are nonnegative. The zero module is included.
No condition excludes the empty scheme or a characteristic. The construction is
valid for non-covering W as well, but the theorem still requires hW.

Searches (all from this task, with exact queries/results in searches.jsonl and in
new node mathlib_searches): LeanFinder query "The derived augmentation unit for a
sheaf of modules in degree zero is an isomorphism on the Cech face total Zariski
site of an arbitrary open covering" returned eight hits, including pullback of a
tensor unit and the zero-th derived functor, none the claimed total-site unit.
Loogle `SheafOfModules, IsIso` gave unknown IsIso; the corrected query
`"SheafOfModules", "cech"` returned zero hits. Mathlib grep
`cech.*unit|Cech.*Unit|zariski.*total` found 17 Stone-Cech topology hits, no match.
LeanSearch "Zariski Cech face total site module augmentation" returned eight hits
(augmentedCechConerve, AffineZariskiSite, Modules, sheafify, etc.), none the face
total-site augmentation. LeanFinder's tuple-basis query returned ordinary gluing
and OpensLeCover declarations, not this category/site. Direct rg of
lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
`Cech.*total.*site|cech.*total.*site|ZariskiCechFaceTotal` found no match; the exact
item-id search in WeilConjectures also found no match. Concept searches of
DAG nodes found the general ringed-total node and the item's consumers, not a
separate definition of this specialization. `blueprint_refs.py search
'Zariski Cech face total site'` returned zero blueprint nodes; `ancestor` returns
None, so the new node preserves the inherited null ancestor and the full route.

Validation: both delivered files compiled separately and together in dependency
order through scompile.py; no errors or warnings after fixing a line-width warning.
Definitions have real data. The sole postponed theorem is the item, with `sorry`
and its complete natural-language proof docstring. No STATEMENT-DISPUTED fault.

## New nodes

`def-sfb-zariski-cech-face-total-site` defines the explicit small Zariski face total
site on the tuple-labelled open basis, the restriction augmentation, proof-only
preparation, its right adjoint determined by universal property, and the canonical
unbounded derived unit predicate. It imports and uses the existing general ringed
site and module categories; it does not copy them. Source: Stacks 09WC, 09WF,
0D70 and 0D7F with the node's injective-order-map adaptation, and 01EP/01EQ for
its open-cover use. Searches above found no existing specialization. This is an
independent missing notion needed to state the item, added under §1(A). No claim
about existence of preparation proofs or invertibility is hidden in a definition:
the item's theorem asserts them. Every declaration is listed in lean.declarations.

## Second reading by Q67

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
