## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceProperBaseChange` states
`AlgebraicGeometry.AlgebraicSpace.proper_baseChange`. Its only theorem has proof
`sorry`, as required in stage 2. It introduces no definition, axiom, helper theorem,
new node, dependency replacement, or statement correction.

Hypotheses and clauses, checked against the full current node and Stacks
`spaces-morphisms.tex`, definition-proper (03ZM), lemma-base-change-proper (04WP):

- The base scheme B is `{B : Scheme.{u}}`. The explicit universe `u` is the
  universe of the existing algebraic-space framework, including its test schemes
  and fields; no independent smaller universe or additional size equality is imposed.
- X, Y, Y' are `{X Y Y' : AlgebraicSpace B}`. This is the existing full
  subcategory of fppf sheaves with representable diagonal and a representable
  surjective etale scheme atlas. Morphisms are the existing full-subcategory
  morphisms, hence natural transformations of the underlying sheaves.
- The specified maps are `(f : X ⟶ Y)` and `(g : Y' ⟶ Y)`.
- The sheaf fibre product is `enlargedFibreProduct f g`, definitionally the
  actual `Limits.pullback f.hom g.hom`, bundled with the algebraic-space
  property supplied by `fibreProduct_isAlgebraicSpace`.
- Its projection to Y' is exactly
  `ObjectProperty.homMk (Limits.pullback.snd f.hom g.hom)`. The type annotation
  fixes its domain to `enlargedFibreProduct f g` and its target to Y'. It is the
  second projection in the stated factor order X ×_Y Y', with no arbitrary map,
  universal-property witness, or reversed-product convention.
- Properness is the existing `MapIsProper`. The hypothesis is `(hf : MapIsProper f)`;
  the conclusion applies the same predicate to that second projection.
- Separatedness is its first conjunct `MapIsSeparated`: the presheaf diagonal
  `pullback.diagonal` is `IsRepresentableWith` the scheme property
  `IsClosedImmersion p.left`. This is precisely the scheme-test condition of
  the node and agrees with `IsSeparatedPresheafMap` from the recorded dependency.
- Finite type is its second conjunct `MapIsFiniteType`, which consists of
  `MapIsQuasiCompact f.hom.hom` and `MapIsLocally (@LocallyOfFiniteType) f`.
  The latter quantifies over all compatible representable etale scheme charts
  U → X, V → Y and their scheme morphism U → V, using Mathlib's scheme
  `LocallyOfFiniteType`.
- Quasi-compactness tests every affine scheme mapping to the target, as required.
  `MapIsQuasiCompact` asks that the corresponding presheaf fibre product's
  atlas-topology point space be compact. This agrees with the node's existence
  of a quasi-compact surjective etale scheme atlas, without any extra hypothesis:
  Stacks `spaces-properties.tex`, definition-quasi-compact (03E3) and
  lemma-quasi-compact-space (03E4), read in full. The published theorem
  `AlgebraicSpace.points_compactSpace_iff` in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage` states exactly this
  equivalence. On an algebraic-space pullback, representability and Yoneda turn
  such an atlas into the (U,p,q,hp) data of `IsQuasiCompactPresheafMap` and
  conversely. Hence the existing predicate is the same notion, not a new
  assumption or a weakened test. No second properness definition is introduced.
- Universal closedness is its third conjunct `MapIsUniversallyClosed`: for
  every algebraic space Y'' and every g' : Y'' → Y it asks
  `IsClosedMap (mapPoint (Limits.pullback.snd f.hom g'.hom).hom)`.
  The induced maps use the recorded field-valued point classes, and their
  `pointTopologicalSpace` is precisely the final topology of all representable
  etale scheme-source maps from `def-a1-space-point-topology`.
- There is no Noetherian, finite-presentation or representability hypothesis on
  either f or g, and no nonemptiness assumption.

Declarations and dependency sources read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its category
  and `Scheme.Hom` (def-pc-scheme).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `IsAlgebraicSpace`, `IsRepresentableWith`, `IsEtale`, `IsSurjective`
  (def-trf-algebraic-space); definitions and docstrings inspected.
- `def-weil-size-convention` is a metatheoretic convention, with no module or
  declaration; explicit universe polymorphism implements it.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` and its full universal-property signature
  (lem-trf-space-fibre-products-etale-covers).
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `pointTopologicalSpace`, `PointRepresentative.map`, `pointImage`
  (def-a1-space-point-topology). Also read `Point`, `PointRepresentative`,
  and `schemePointMap` from the underlying point-classes module.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`:
  `IsQuasiCompactPresheafMap`, `diagonalPresheafMap`,
  `IsSeparatedPresheafMap`, `quasiCompact_separated_etaleLocal`
  (lem-trf-space-qc-separated-etale-local).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (def-weil-closed-immersion).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; quasi-compactness and finite type
  follow the recorded conjunction convention (def-weil-finite-type-morphism).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`:
  `AlgebraicGeometry.IsProper`, `IsSeparated`, `UniversallyClosed`
  (def-weil-proper-morphism), used through the existing space predicates.
- Added the already-landed `def-sfb-space-morphism-properties` to stmt_deps:
  its module `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties` supplies
  `MapIsLocally`, `MapIsSeparated`, `MapIsFiniteType`,
  `MapIsUniversallyClosed`, `MapIsProper`. Also read their underlying
  `mapPoint` and `MapIsQuasiCompact` in `ProperCurveModuli`.
- Added the already-landed `def-sfb-space-sheaf-fibre-product` to stmt_deps:
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite.enlargedFibreProduct`
  (declaration namespace `AlgebraicGeometry.AlgebraicSpace`) bundles the actual
  sheaf pullback. Its first projection was also read; this statement uses the
  actual second projection in the same way.

The added dependencies merely record existing definitions used by the unchanged
statement. Every recorded statement-dependency module is publicly imported.
The proof-dependency modules coincide with these except
`lem-sfb-stack-finite-type-calculus`, which currently has no Lean record or
Mathlib match; it is a proof-only input, so there is no module to import and no
missing notion needed to type this statement. Its role is retained explicitly
in the theorem's full four-step natural-language proof docstring. Its DAG record
and mathematical statement were read. No statement or proof dependency is removed.

Edge cases: empty X, empty Y', both empty, g = identity, arbitrary scheme targets
and arbitrary algebraic-space targets are included. Empty atlases correspond to
compact empty point spaces in the 03E4 equivalence. An identity base change gives
the original proper map up to the canonical sheaf isomorphism. Nonrepresentable
g and proper nonrepresentable f remain in scope. A non-Noetherian base and
proper maps not locally of finite presentation are not excluded. All binders
and the sole universe are explicit; `autoImplicit` is disabled.

Searches performed using the prescribed search wrapper and direct source search:

- LeanFinder: `Base change preserves proper morphisms of algebraic spaces`:
  eight hits, all scheme-level properness/base-change properties, including
  `AlgebraicGeometry.IsProper.isStableUnderBaseChange`; no exact space theorem.
- LeanSearch: `Proper morphisms of algebraic spaces are stable under arbitrary
  base change`: eight scheme/ring-property hits, no exact algebraic-space theorem.
- Loogle: `"IsProper", "pullback"`: zero hits.
- Mathlib grep: `AlgebraicSpace|IsProper` in AlgebraicGeometry: proper scheme
  morphism hits, no algebraic-space properness theorem.
- Direct rg in `lean/WeilConjectures` for the item id: no match. Further rg for
  `IsProper`, `UniversallyClosed`, `MapIsProper`, `proper_baseChange` and related
  space property names in `lean/WeilConjectures` and `lean/Sheaf` found the
  published generic predicates, bundled sheaf products and point-compactness
  equivalence, all reused rather than redefined.
- The existing `AlgebraicSpace.flat_proper_fp_locality` includes this assertion
  as one specialization of one conjunct, but its full signature also asserts
  flatness/f.p. base-change stability and fppf descent. It does not have exactly
  this node's standalone statement. This delivery states just the required
  assertion with its own DAG proof plan. It neither imports that broader
  theorem nor substitutes it for the accepted four-step proof.

Validation: the prescribed scompile.py compiled both sandbox and final module
forms cleanly (3.7 s and 1.6 s), with no errors or warnings. The theorem is the
sole postponed proof. No STATEMENT-DISPUTED flag or node fault remains.

## Second reading by Q36

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
