## Worker report

Item: lem-sfb-space-fibre-product-comparison, stage 2, group Q15.
Module: Sheaf.AlgebraicGeometry.SpaceFibreProductComparison.
Declaration: AlgebraicGeometry.AlgebraicSpace.fibreProduct_comparison_properties.

Source read: literature/stacks-project/spaces-morphisms.tex,
lemma-fibre-product-after-map (Tag 03KN), statement and proof, and
lemma-properties-diagonal (Tag 03HK). The statement is exactly clauses (1) and (4)
of 03KN. The accepted stage-1 split is unchanged. The inherited BLOCKED ending was
about stage-1 deliver.py; brief-stage2 section 0 expressly permits this stage-2
handoff. The current item has no Lean record and no repair note.

The module states the theorem with sorry and defines no new objects. Mathlib already
provides the actual canonical map as CategoryTheory.Limits.pullback.mapDesc.
Applying it to f.hom, g.hom, h.hom forms the comparison in fppf sheaves. Its underlying
presheaf map is the .hom used in the predicates. mapDesc is defined by pullback.map
with identity maps on the two factors; its components are the original projections.
This is not an arbitrary morphism or an existential choice.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Scheme S, with the size convention | `{S : Scheme.{u}}`, with explicitly declared `universe u` |
| Algebraic spaces A, B, Z, T over S | `(A B Z T : AlgebraicSpace S)`, the existing full subcategory of fppf sheaves with representable diagonal and a scheme atlas |
| Morphisms A to Z, B to Z, Z to T | `(f : A ⟶ Z) (g : B ⟶ Z) (h : Z ⟶ T)` |
| Sheaf fibre products and canonical comparison i | `pullback.mapDesc f.hom g.hom h.hom`; the imported closure theorem identifies its source and target sheaf pullbacks as algebraic spaces |
| i is representable by schemes | `IsRepresentable (pullback.mapDesc f.hom g.hom h.hom).hom` |
| Monomorphism, injective on sections over every S-scheme | `∀ C : Over S, Function.Injective ((pullback.mapDesc f.hom g.hom h.hom).hom.app (op C))` |
| Locally of finite type after every scheme base change | `IsRepresentableWith (fun _ _ p ↦ LocallyOfFiniteType p.left)` applied to that map |
| Separated: relative diagonal representable by closed immersions | `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) (pullback.diagonal ...)` |
| Locally quasi-finite after every scheme base change | `IsRepresentableWith (fun _ _ p ↦ Scheme.Hom.IsLocallyQuasiFinite p.left)` applied to that map |
| If h is quasi-separated | antecedent `IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left) (pullback.diagonal h.hom.hom)` |
| Then i is quasi-compact | consequent `IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left)` applied to the comparison |

For the last two lines, a representable morphism is quasi-compact exactly when the
representing source over every affine scheme test is quasi-compact. Indeed, the
all-scheme form says that each representing projection is quasi-compact; over an
affine target this means that its whole source is quasi-compact. Conversely, testing
on the affine opens of any test scheme establishes quasi-compactness of its
representing projection. I read Mathlib's quasiCompact_iff_forall_isAffineOpen and
the HasAffineProperty instance for QuasiCompact in Morphisms/QuasiCompact.lean.
Thus the formulation does not strengthen the affine-test clause. The diagonal of
h is representable for any algebraic-space h; including its representing square
in the antecedent adds no mathematical assumption. IsRepresentableWith supplies
one representing scheme for each test; all representing schemes are uniquely
isomorphic over that test, and the scheme properties used here are invariant under
such an isomorphism, so this expresses the node's every-base-change condition.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom
  (def-pc-scheme), with schemes over S encoded by CategoryTheory.Over S.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicGeometry.AlgebraicSpace,
  AlgebraicSpace.IsRepresentableWith, and AlgebraicSpace.IsRepresentable
  (def-trf-algebraic-space). Their full definitions and source docstrings were read.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  AlgebraicSpace.fibreProduct_isAlgebraicSpace, plus its two companion statements
  etaleCover_pullback and etale_fibreProduct_isScheme, read from the recorded module
  (lem-trf-space-fibre-products-etale-covers). The first gives the algebraic-space
  interpretation of the sheaf pullbacks; the other clauses are not needed here.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: QuasiCompact
  (def-weil-finite-type-morphism). These are exposed through the quasi-finite import.
- WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism:
  Scheme.Hom.IsLocallyQuasiFinite and IsQuasiFiniteAtPoint (pqf-def-quasifinite).
  This uses the Stacks finite-type-inclusive notion, not Mathlib's weaker bare
  LocallyQuasiFinite predicate. The complete recorded source was read.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion
  (def-weil-closed-immersion), read including its closed-embedding and stalk conditions.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback.mapDesc,
  including its implementation by pullback.map with identity factor maps.
  Mathlib.CategoryTheory.Limits.Shapes.Diagonal: pullback.diagonal.
- def-weil-size-convention is a metatheoretic convention, not a declaration;
  the existing algebraic-space universe convention is retained without any new
  universe equality or bound.

Proof dependency imports: the recorded
Sheaf.AlgebraicGeometry.MonomorphismFiniteTypeComposite is a plain proof import;
its Scheme.Hom.monomorphism_properties_of_locallyOfFiniteType_comp signature and
proof docstring were read. The other stated proof dependencies are public statement
imports or their transitive imports. lem-sfb-space-diagonal-scheme-tests has no
recorded Lean statement in the current DAG, so there is no module to import for it;
it is named in the complete proof docstring, not introduced as an assumption.
It is only a proof prerequisite and no missing statement object depends on it.

Edge cases checked before writing:

- Empty A or B gives an empty source and target comparison with all asserted
  properties; the empty scheme is permitted among the scheme tests.
- For h = identity, the comparison is an isomorphism. No identity case is excluded.
- With A = B = Z and f = g = identity, the comparison is the relative diagonal
  of h. Thus the theorem still covers a nonseparated h (for example the affine
  line with doubled origin). Separatedness of the comparison is separatedness
  of that map, not closedness of the image of the diagonal of h.
- Without quasi-separatedness, the final implication makes no quasi-compactness
  assertion. No quasi-compactness of A, B, Z, T or S has been imposed.
- Nonreduced test schemes remain allowed. The scheme-test definition detects
  the scheme structure, not merely equality on geometric points.

Searches actually run in this session:

- msearch.py leanfinder: "The canonical comparison A times Z B to A times T B
  for algebraic spaces is a representable separated locally quasi finite
  monomorphism". Eight hits, including scheme pullback comparisons and scheme
  projection permanence, but no result about arbitrary algebraic spaces.
- msearch.py loogle: "CategoryTheory.Limits.pullback.map,
  AlgebraicGeometry.LocallyOfFiniteType". Zero hits.
- msearch.py leansearch: "The comparison of fibre products of algebraic spaces
  over different bases is a representable locally finite type separated locally
  quasi finite monomorphism". Eight hits, including scheme local-finite-type and
  locally-quasi-finite base change and functor-relative representability; none is
  this algebraic-space comparison theorem.
- msearch.py grep: "AlgebraicSpace|fibreProductComparison|fiberProductComparison"
  in Mathlib/AlgebraicGeometry. Zero hits.
- rg over lean/WeilConjectures and lean/Sheaf for
  "space-fibre-product-comparison|fibreProductComparison|fibre_product_comparison|fiberProductComparison":
  zero hits. A broader search for fibre-product comparisons found unrelated
  cohomological and site comparisons, not this theorem.
- Direct rg and source reading of Mathlib's Pullback/HasPullback.lean located
  pullback.mapDesc at line 277: it is exactly the required canonical construction,
  so no helper definition or new definition node was added.
- DAG search for 03KN/fibre-product-after-map found this item and applications
  with additional assumptions; no duplicate statement with a usable Lean record.

Validation: scompile.py Q15 lem-sfb-space-fibre-product-comparison on the delivered
module succeeded in both sandbox and library module modes (4.2 s and 4.3 s), with
no errors or unexpected warnings. All variables/universes are explicit and
`set_option autoImplicit false` is enabled. There are no diagnostics in the file,
no new nodes, no dependency repairs, and no statement corrections or disputes.

## Second reading by Q15

A separate reread of the node and final signature checked each of the six conjuncts
against 03KN(1),(4). This is this worker's reread; the independent maintainer review
is still required. The binders preserve the common base S and all four algebraic
spaces, with arbitrary f, g and h. The map is Mathlib's canonical mapDesc, formed
in sheaves and then forgotten to presheaves, rather than a supplied comparison.
The monomorphism conjunct quantifies over every S-scheme, and the finite-type and
quasi-finite conjuncts use the existing representing-square predicate. The latter
includes finite type via the recorded Stacks definition. The separatedness
conjunct concerns the diagonal of the comparison itself. The last conjunct assumes
quasi-compactness only of h's diagonal and concludes exactly quasi-compactness on
scheme tests of the comparison. The affine-test equivalence is explained above;
it introduces no separation or finiteness condition on the objects. No mismatch
was found and no node or signature correction was needed. All five steps of the
accepted proof are preserved in the theorem docstring; the unstated diagonal-test
proof prerequisite is identified explicitly above instead of being silently used
as a new hypothesis.
