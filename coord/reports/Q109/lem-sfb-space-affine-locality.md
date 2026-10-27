## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceAffineLocality` states
`AlgebraicGeometry.AlgebraicSpace.affine_locality_and_permanence`. It introduces no
new definition and proves nothing: the single theorem has proof `by sorry`.
The module and theorem docstrings cite Stacks Tags 03WG, 03WH, 03WI, 03KG and
03KM; the theorem docstring carries all seven proof steps of the node.

Hypothesis and clause correspondence:

- Base scheme and size convention: `{S : Scheme.{u}}`, with `universe u` explicit
  and `set_option autoImplicit false`. All spaces, scheme tests, sheaves and maps
  use the universes of the recorded algebraic-space definition; no additional
  equality or smallness assumption is imposed. There is no indexing set in this
  assertion: the locality witness is a single scheme atlas.
- Algebraic spaces and their morphism: `{X Y : AlgebraicSpace S} (f : X ⟶ Y)`.
  These are exactly the recorded full subcategory of big-fppf sheaves and its
  natural transformations. No assumptions on the small-etale structure sheaves
  are needed for this geometric statement; their existing definitions are retained.
- Affineness uses the existing `MapIsAffine f`: each affine scheme test has an
  affine scheme representing its cartesian square. The conclusion explicitly
  supplies `IsRepresentable f.hom.hom`, so the representability in the node's
  definition is present and is not assumed without proof. This is the affine-test
  recognition of node proof step 1 and Stacks 03WG(1) iff (2).
- Target locality is the first equivalence: `MapIsAffine f ↔ ∃ V a, ...`.
  `V : Over S` is the scheme atlas; `a : yoneda.obj V ⟶ Y.obj.obj` is its map;
  `IsEtale a ∧ IsSurjective a` expresses representable surjective etaleness using
  the recorded scheme-test definitions, each of which includes representability.
  The witnesses `U : Over S`, `p : U ⟶ V`, `q : yoneda.obj U ⟶ X.obj.obj`
  and `IsPullback q (yoneda.map p) f.hom.hom a` identify precisely `X ×_Y V`.
  `IsAffineHom p.left` states that its scheme projection to V is affine.
  Neither U nor V is required affine or quasi-compact here.
- Arbitrary algebraic-space base change: for every `X' Y'`, maps `g : Y' ⟶ Y`,
  `p : X' ⟶ X`, `f' : X' ⟶ Y'` and
  `IsPullback p.hom f'.hom f.hom g.hom`, conclude `MapIsAffine f'`.
  These are squares of the actual fppf sheaves. Quantifying over every cartesian
  square includes the chosen sheaf pullback and every isomorphic presentation;
  it makes no scheme or representability restriction on the base-change map g.
- Composition: for every `Z : AlgebraicSpace S` and `g : Y ⟶ Z`,
  `MapIsAffine g → MapIsAffine (f ≫ g)` under `MapIsAffine f`.
- Quasi-compactness: `IsQuasiCompactPresheafMap f.hom.hom` uses exactly affine
  tests whose pullback source admits a quasi-compact, surjective etale scheme atlas.
- Separatedness: `IsSeparatedPresheafMap f.hom.hom` uses the named canonical
  relative diagonal and `IsRepresentableWith` of scheme closed immersions.
  Thus the conclusion includes representability and closed immersion of every
  scheme test of that diagonal, as the node specifies.
- Scheme target: for every `V : Over S`, an isomorphism
  `Nonempty (Y.obj.obj ≅ yoneda.obj V)` implies existence of `U : Over S` and
  `Nonempty (X.obj.obj ≅ yoneda.obj U)`. This expresses scheme source without
  requiring that Y be literally a particular chosen bundled scheme sheaf.
- Affine target: the same clause includes `IsAffine V.left → IsAffine U.left`.
  An isomorphism with any scheme presentation of the target transfers affineness;
  choosing one U before this implication does not strengthen the statement,
  since affineness is invariant under the unique isomorphism of representations.
- Quasi-compact target: its premise is the literal atlas existential
  `∃ V a, CompactSpace V.left ∧ IsEtale a ∧ IsSurjective a`.
- Absolute quasi-separated target: `IsAbsolutelyQuasiSeparated Y`, the recorded
  affine-pair criterion for quasi-compactness of the diagonal over Spec Z. This
  avoids replacing the absolute diagonal by the relative diagonal over S.
- Final conclusion: the identical quasi-compact-atlas existential for X,
  together with `IsAbsolutelyQuasiSeparated X`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  full definitions and their docstrings were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsRepresentable`, `IsEtale`, `IsSurjective`, and
  `IsAlgebraicSpace`. Their full signatures and definitions were read.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom` (preimage of every
  affine open is affine); `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `IsClosedImmersion` (closed embedding and surjective stalk maps).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite`: `MapIsAffine`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`:
  `IsQuasiCompactPresheafMap`, `diagonalPresheafMap`, `IsSeparatedPresheafMap`.
  The four existing definition-node owners of these predicates have been added
  to `stmt_deps`; no definition or mathematical node statement was changed.
- Recorded proof modules are imported privately: AlgebraicSpaceFibreProductsEtaleCovers
  (`fibreProduct_isAlgebraicSpace` and the covering/scheme-test statements),
  WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability
  (`isRepresentable_of_isSheaf_of_zariskiCovers`),
  AlgebraicSpaceFourPropertyFppfDescent (`four_property_fppf_descent`),
  AlgebraicSpaceEtaleOpenImage (`points_compactSpace_iff`, `etale_open_image`),
  AlgebraicSpaceRepresentableEtaleSchemeTests (`representable_etale_scheme_tests`),
  and SpaceChangeBase (`exists_spaceChangeBase`). The relevant full signatures
  and docstrings were read. Mathlib proof leaves are supplied by Affine,
  Separated, QuasiSeparated, Integral, UniversallyClosed, Limits and Etale,
  including closed-immersion base change and the affine-scheme qcqs instances.
- `lem-sfb-qc-space-affine-etale-atlas` currently has neither Lean record nor
  Mathlib match, so there is no proof module to import for it. It is only a proof
  dependency; it is not needed to elaborate this statement. Its use remains in
  the natural-language proof and the node's unchanged `proof_deps`.

Edge cases checked before writing:

- Empty scheme/space and empty affine tests are allowed. The zero ring's spectrum
  is affine, the empty scheme is quasi-compact, and there is no nonempty premise.
- The target atlas V need not be quasi-compact or affine; otherwise the locality
  criterion would exclude non-quasi-compact targets.
- Arbitrary base change can be by a nonschematic space. The square is a sheaf
  square and the statement never replaces it by a scheme-only square.
- Y can be nonseparated, non-quasi-separated, or over a non-quasi-separated S.
  Only the final implication assumes Y qcqs, and its QS predicate is absolute.
- Identity and isomorphism maps fit the assertions; no artificial finite-type,
  surjectivity, nonzero-ring, coefficient or characteristic hypothesis occurs.
- Representability of f is a conclusion of affine-test recognition, rather than
  an extra hypothesis restricting the locality equivalence.

Searches made:

- `msearch.py ... leanfinder "Affineness of algebraic space morphisms is etale local
  on target and stable under base change and composition"`: eight hits, on
  `AffineTargetMorphismProperty`, `HasAffineProperty`, `affineAnd` and scheme
  local-property/descent machinery; no algebraic-space statement.
- `msearch.py ... leansearch "affine morphism algebraic spaces etale local target"`:
  eight hits, including `IsAffineHom` and `HasAffineProperty.iff_of_openCover`;
  all geometric statements are for schemes.
- `msearch.py ... loogle "AlgebraicGeometry.IsAffineHom,
  AlgebraicGeometry.AlgebraicSpace.MapIsAffine"`: zero hits, with unknown
  identifier for the project-only `AlgebraicSpace.MapIsAffine`.
- `msearch.py ... grep "MapIsAffine|AlgebraicSpace|affine.*etale" AlgebraicGeometry`:
  nine hits, all on Mathlib's scheme affine-etale site; no spaces implementation.
- `rg` in `lean/WeilConjectures` for `MapIsAffine`, the item id and affine-space
  locality: no matching algebraic-space theorem. Scheme affineness results exist.
- `rg` in `lean/Sheaf` and `dag/lean_names_upstream.json` located the four reused
  predicates and consumers, and the existing four-property fppf descent theorem;
  none states the complete item. Searching DAG definition records located the
  existing owners; no new notion/node was necessary.
- Read `literature/stacks-project/spaces-morphisms.tex`, affine section, especially
  `lemma-affine-local`, `lemma-composition-affine` and `lemma-base-change-affine`.
  The atlas equivalence matches 03WG(1), (2), (4); the permanence clauses agree
  with 03WH and 03WI and with the node's recorded qc/separated proof.

Validation: `scompile.py Q109 lem-sfb-space-affine-locality` compiled this file
both as the sandbox module and its actual library module in 1.6 seconds each,
without errors or unexpected warnings. No statement correction, new node,
dependency repair, or STATEMENT-DISPUTED fault was needed.

## Second reading by Q109

I reopened the node and the completed module for a second pass (self-check;
the maintainer's independent review is still required by the dispatch brief).
Matched the first equivalence to exactly the scheme-atlas condition, checked that
`IsAffineHom` applies to p.left rather than to the atlas, checked base-change
square orientation and both endpoints, and checked composition order `f ≫ g`.
Read the actual quasi-compact and separated definitions again: the QC conclusion
uses affine-test atlases, and the separated conclusion tests the relative diagonal
by closed immersions. Checked that the scheme-target conclusion supplies both
scheme representability and the affine case, and that the final implication
assumes and concludes absolute QS, independently of the base scheme.
No mismatch was found and no Lean change was needed. Added the four already
landed predicate-owner definition nodes to the item's stmt_deps, so the statement
explicitly depends on the shared definitions it uses. No independent reviewer
was spawned, as explicitly prohibited by the worker brief.
