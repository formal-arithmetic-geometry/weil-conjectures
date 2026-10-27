## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceUniversallyClosedQuasiCompact` states
`AlgebraicGeometry.AlgebraicSpace.mapIsQuasiCompact_of_mapIsUniversallyClosed`.
Its only theorem proof is `sorry`, as required for stage 2. The docstring carries
all eight steps of the accepted split and their dependency identifiers.
No definition is introduced and no statement or dependency field is changed.

Source read: `literature/stacks-project/spaces-morphisms.tex`, lines 1467–1560,
Tag 04XW, lemma-universally-closed-quasi-compact and its full proof. The existing
split corrects the source's incidental Z/X, Y_V/X_V and q(t)/q(z) typos and works
with a closed subset directly. None affects the statement.

Hypothesis-by-hypothesis and clause-by-clause translation:

- The base scheme S is `{S : Scheme.{u}}`, using Mathlib's locally ringed space
  with local affine charts. `universe u` is explicit and arbitrary; all scheme
  tests use this same bound, not an independent possibly smaller universe.
- The algebraic spaces X and Y over S are `{X Y : AlgebraicSpace S}`. This is
  the existing full subcategory of fppf sheaves with representable diagonal
  and a representable surjective étale scheme atlas. Neither is restricted
  to be a scheme. Morphisms are the existing full-subcategory morphisms,
  so `(f : X ⟶ Y)` is precisely a natural transformation of their sheaves.
- The universally closed hypothesis is `(hf : MapIsUniversallyClosed f)`.
  Its existing definition quantifies over every `(Y' : AlgebraicSpace S)`
  and `(g : Y' ⟶ Y)` and requires
  `IsClosedMap (mapPoint (Limits.pullback.snd f.hom g.hom).hom)`.
  Thus this is the point map of the sheaf fibre product, closed for every
  algebraic-space base change, including nonrepresentable ones.
- The conclusion is `MapIsQuasiCompact f.hom.hom`. Its existing definition
  expands to `∀ (T : Over S) (a : yoneda.obj T ⟶ Y.obj.obj), IsAffine T.left →
  CompactSpace (Point (Limits.pullback f.hom.hom a))`.
  It therefore includes every affine scheme mapping to Y, not just an atlas.
  `IsAffine` is Mathlib's canonical-map-to-Spec-is-an-isomorphism predicate,
  with `Scheme.isoSpec` the spectrum isomorphism, equivalent to the node's
  description of affine schemes. `CompactSpace` means quasi-compactness
  without any Hausdorff condition; it is exactly the finite-subcover clause.
- `Point` uses the existing common-field-extension equivalence classes of
  field-valued representatives. Its `pointTopologicalSpace` is the final
  topology of all representable étale scheme-source maps, the atlas topology.
  Both hypothesis and conclusion use that same topology.
- No representability of f, separatedness, finite type, Noetherian, nonempty,
  finite-index, or separation axiom for point spaces is assumed. No extra
  conclusion or tautological conjunct is present.

Statement dependency declarations read and used (full source signatures and
docstrings were read, including the definitions that the predicates unfold to):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace`, `AlgebraicSpace.IsAlgebraicSpace`,
  `IsRepresentableWith`, `IsRepresentable`, `IsEtale`, and `IsSurjective`.
- `def-weil-size-convention`: the recorded metatheoretic convention has no
  declaration or import; the explicit universe u and the existing bounded
  algebraic-space framework implement it. `Point F` lives in Type (u+1).
- `lem-trf-space-fibre-products-etale-covers`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`,
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`,
  `etaleCover_pullback`, and `etale_fibreProduct_isScheme`. The definitions
  already use the same categorical sheaf pullback supplied by this module.
- `def-a1-space-point-topology`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`, declarations
  `AlgebraicGeometry.AlgebraicSpace.pointTopologicalSpace`, `pointImage`,
  `PointRepresentative.map`; the imported PointClasses module provides
  `Point`, `PointRepresentative`, and `schemePointMap`.
- `def-sfb-space-morphism-properties`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`,
  `AlgebraicGeometry.AlgebraicSpace.MapIsUniversallyClosed`. It publicly
  imports `Sheaf.AlgebraicGeometry.ProperCurveModuli`, whose existing
  `MapIsQuasiCompact` and `mapPoint` supply the conclusion and point map.
  This is the dependency node's specified interface, not a private copy.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, `Spec.map`; affine schemes are tested with the
  existing `IsAffine` and `Scheme.isoSpec` in `Mathlib.AlgebraicGeometry.AffineScheme`.

All stated proof dependencies are imported without `public` unless they are
also statement dependencies. These include the affine-atlas open cover,
étale open image, point-open calculus, multivariable polynomial ring,
affine quasi-compactness and quasi-separatedness, polynomial domain instance,
prime-spectrum basic opens/compactness, ideal span, and prime residue-field
algebra. Mathlib leaves with no `lean` record were resolved using their
`mathlib_match` records. `lem-sfb-space-qcqs-permanence` has neither a Lean
record nor a Mathlib match, so it has no module to import yet; it occurs only
in the future proof, not the signature, and remains explicitly cited in the
docstring. No missing statement notion or unusable dependency was found.

Edge cases checked before drafting:

- Empty X: every base-change source is empty and compact, and its images of
  closed subsets are empty and closed. No nonemptiness binder excludes it.
- Empty Y or empty S: maps to them have empty source point spaces; the
  affine tests include the zero-ring spectrum. The statement is still true.
- Identity maps and isomorphisms: universal closedness holds and the affine
  tests recover affine schemes, which are quasi-compact; no global
  quasi-compactness of X or Y is imposed.
- Infinite disjoint unions over a nonempty point are generally not
  universally closed. The hypothesis is substantive, not ordinary
  closedness alone (the map to a point alone would not suffice).
- The polynomial argument handles an empty variable-support set J and finite
  residue fields by using the generic point of the polynomial domain, not
  by choosing rational values at which a nonzero polynomial is nonzero.
- Non-quasi-separated algebraic spaces and nonrepresentable maps are allowed;
  any quasi-separatedness used in the proof belongs to the affine target.

Searches made for reuse (2026-10-24):

- `msearch.py ... leanfinder "Every universally closed morphism of algebraic spaces is quasi compact"`:
  eight hits, headed by `AlgebraicGeometry.instQuasiCompactOfUniversallyClosed`;
  all relevant results concern schemes. Read its actual Scheme binders and
  the instance in `Mathlib/AlgebraicGeometry/Morphisms/UniversallyClosed.lean`.
- `msearch.py ... loogle '"UniversallyClosed", "QuasiCompact"'`:
  two hits, the same scheme instance and fpqc descent for scheme morphisms.
- `msearch.py ... grep 'UniversallyClosed.*QuasiCompact|AlgebraicSpace' AlgebraicGeometry`:
  seven hits in scheme valuative-criterion, flat-descent and universally-closed
  modules, none about arbitrary algebraic spaces.
- `msearch.py ... leansearch "Every universally closed morphism of algebraic spaces is quasi compact"`:
  eight hits, again scheme statements and scheme-morphism definitions only.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the proposed theorem name,
  `MapIsUniversallyClosed.*MapIsQuasiCompact`,
  `quasiCompact_of_universallyClosed` and `universally_closed_quasi`:
  no existing statement matching this node. A direct search for the node id
  in `lean/WeilConjectures` also returned no match. Broader concept searches
  found the existing point topology and morphism-property definitions used.

Validation: `scompile.py Q153 lem-sfb-space-universally-closed-quasicompact`
compiled the delivered module in sandbox mode (8.7 s) and under its final
module name (1.8 s), with no errors or warnings. No local/global build was run.
No statement dispute, correction, new node, or dependency repair is needed.

## Second reading by Q153

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
