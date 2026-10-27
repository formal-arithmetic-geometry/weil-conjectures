## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceProperComposition` states
`AlgebraicGeometry.AlgebraicSpace.mapIsProper_comp`, with proof `sorry`, exactly the
composition assertion of Stacks Project, spaces-morphisms.tex, Tag 04XY,
`lemma-composition-proper`. The source definition and composition proof were read at
lines 7883–7940. No new definitions, dependency repairs or statement corrections.

Hypotheses and clauses:

- The ambient base is `Spec (CommRingCat.of (ULift.{u} ℤ))`. Lifting the integers
  supplies Spec ℤ in every scheme universe rather than restricting to universe zero.
- `X Y Z : AlgebraicSpace ...` uses the existing category of fppf sheaves with
  representable diagonal and a surjective representable étale scheme atlas.
  `universe u` is explicit; `autoImplicit false` forbids auto-bound variables.
- `f : X ⟶ Y` and `g : Y ⟶ Z` render the two composable morphisms. These are
  natural transformations in the full subcategory, with no representability premise.
- `hf : MapIsProper f` and `hg : MapIsProper g` render the two properness assumptions.
  Unfolding the shared predicate gives `MapIsSeparated`, `MapIsFiniteType` and
  `MapIsUniversallyClosed` for each morphism.
- `MapIsSeparated` tests the relative diagonal by `IsRepresentableWith` and the
  scheme class `IsClosedImmersion`; it does not require the original map representable.
- `MapIsFiniteType` is quasi-compactness together with `MapIsLocally
  (@LocallyOfFiniteType)`. The latter checks all compatible étale scheme charts.
  The shared quasi-compactness predicate uses affine scheme base changes and
  compactness of the resulting atlas point space. This is the usual algebraic-space
  quasi-compactness convention. In this properness assertion universal closedness
  also ensures quasi-compactness (spaces-morphisms.tex, lemma-universally-closed-
  quasi-compact); in particular the node's condition on inverse images of
  quasi-compact opens holds. No weaker notion of properness is substituted.
- `MapIsUniversallyClosed` requires `IsClosedMap` on point classes of the sheaf
  pullback projection for every algebraic-space base change. The points and topology
  are the existing field-valued classes and final topology for étale scheme maps.
- The conclusion `MapIsProper (f ≫ g)` renders that the composite is proper, with
  exactly the same three properties. Quasi-separatedness and finite presentation
  are background conventions in the node, not extra assumptions or conclusions;
  neither is imposed on `f` or `g`.
- There are no local Noetherian, locally quasi-finite, finite-presentation or
  representability hypotheses. The sole postponed theorem is `mapIsProper_comp`.

Dependency declarations used, signatures and docstrings read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map` (scheme and affine-spectrum nodes).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale` and `IsAlgebraicSpace` (def-trf-algebraic-space).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`. The chosen products in the properness predicate are
  actual sheaf pullbacks, with the algebraic-space closure supplied by this module.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `PointRepresentative.map`, `pointImage`, `pointTopologicalSpace`, using
  `Point`, `PointRepresentative` and `schemePointMap` from AlgebraicSpacePointClasses.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`; `Mathlib.AlgebraicGeometry.Morphisms.Proper`:
  scheme `IsProper` (its separated/universally-closed/local-finite-type convention).
  These are reused by the shared algebraic-space predicates, not redefined here.
- `def-weil-size-convention` is a metatheoretic convention with no declaration.
- Added the already landed node `def-sfb-space-morphism-properties` to `stmt_deps`:
  its module `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties` supplies
  `MapIsLocally`, `MapIsSeparated`, `MapIsFiniteType`, `MapIsUniversallyClosed`,
  and `MapIsProper`. `ProperCurveModuli.mapPoint` and `MapIsQuasiCompact` were also
  read in full. The shared module publicly exposes the statement dependencies.
- The two other proof nodes, `lem-sfb-space-separated-fp-composition` and
  `lem-sfb-stack-finite-type-calculus`, have no Lean records in the read checkout;
  they supply no import yet. The theorem docstring records their exact intended uses.

Edge cases checked before writing: empty source or intermediate/target space where
morphisms exist; identity morphisms; nonrepresentable proper morphisms; arbitrary
characteristic (Spec ℤ base); arbitrary universe u; proper morphisms that are not
locally of finite presentation or locally Noetherian. The signature excludes none
of these. No index or nonemptiness condition is present.

Searches actually run with msearch.py, Q78 / lem-sfb-space-proper-composition:

- LeanFinder: `The composition of two proper morphisms of algebraic spaces is
  proper` — eight hits, headed by scheme `IsProper.stableUnderComposition`,
  `IsProper.instCompScheme`, and `IsProper.comp_iff`; no algebraic-space theorem.
- Loogle: `"IsProper", "comp"` — twelve hits, principally topological
  `IsProperMap.comp`, not the algebraic-space assertion.
- LeanSearch: `The composition of proper morphisms of algebraic spaces is proper`
  — eight hits, all scheme `IsProper` statements or its definition.
- Mathlib grep via msearch.py: `proper.*comp|IsProper` in `AlgebraicGeometry` —
  twenty-five reported hits, all scheme results; the scheme properness file was
  then read directly, including its composition instance.
- Direct rg in `lean/WeilConjectures`, `lean/Sheaf/AlgebraicGeometry` and
  `dag/lean_names_upstream.json` for `proper_comp`, `mapIsProper_comp`,
  `proper_composition`, `MapIsProper`, and the node ID: no existing theorem of this
  statement; found and reused AlgebraicSpaceMorphismProperties. Other hits concern
  schemes, compact support or statements assuming properness of a composite.

The example CompactObject module is withdrawn in the current read checkout (only
`module` and a withdrawal comment); the module follows current brief-stage2 module
visibility and source-docstring conventions.

Validation: scompile.py compiled the sandbox module and its intended library module
with no errors or warnings (58.8 s and 39.4 s respectively). The dry run and final
delivery are run through deliver2.py as required. No mathematical dispute found.

## Second reading by Q78

I reread the node, the delivered signature and the definitions of `MapIsProper`,
`MapIsSeparated`, `MapIsFiniteType` and `MapIsUniversallyClosed`. The base, spaces,
two composable arrows, two properness premises and proper composite conclusion
match clause by clause as listed above. In particular `MapIsProper` universally
quantifies over algebraic-space base changes, not just representable maps; its
separatedness condition concerns only the diagonal. The universe lift does not
change the integer base ring. Finite presentation and quasi-separatedness introduce
no extra premises. No signature mismatch was found and no correction was made.
This is a worker self-check; the dispatcher's instructions prohibit starting another
agent, and the maintainer performs the independent reading of this delivery.
