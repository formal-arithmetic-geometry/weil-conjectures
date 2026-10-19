## Worker report

This is a stage-2 statement delivery, not another stage-1 split. The previous attempt's
observation that NY reviewed and merged the split does not supply a Lean statement.
The base node had no `lean` record. No shared source or upstream source was edited.

`Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover` states
`AlgebraicGeometry.AlgebraicSpace.exists_affine_etale_cover_and_point_topology`.
Its only theorem proof is `sorry`; its docstring contains all five DAG proof steps.
The natural-language statement, proof and proof dependencies are unchanged.
Only its `lean` and the added definition dependency change.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; the algebraic space is
  `(E : AlgebraicSpace S)`, using the recorded fppf-sheaf/representable-diagonal/atlas
  definition without a private replacement or added hypothesis.
- The field-valued point classes in the introductory sentences are `Point E.obj.obj`.
  `PointRepresentative` stores the field, map to the base, and presheaf value.
  `PointRepresentative.Rel` requires equality after restriction from both representatives
  to one field spectrum over the base. Scheme maps between field spectra encode the
  two field embeddings; no separability or algebraicity is required.
  `Point` is the actual `Quot` of this common-extension relation. It has real data and
  introduces no existence choice. The relation is an equivalence: reflexivity uses
  the same field, symmetry interchanges the arrows, and transitivity amalgamates the
  two extension fields over the shared middle field. Thus taking its generated quotient
  gives exactly the point equivalence of Tag 03BU.
- For `t : yoneda.obj T ⟶ E.obj.obj`, `schemePointMap t x` is the quotient class of
  `T.left.fromSpecResidueField x`, evaluated under `t` by Yoneda. Its base is precisely
  this residue-field map followed by `T.hom`; its field is `T.left.residueField x`.
- `W : Over S` and `w : yoneda.obj W ⟶ E.obj.obj` are the required scheme and atlas.
  `I : Type u`, `A : I → Scheme.{u}`, and component maps `ι` express the disjoint union:
  `Nonempty (IsColimit (Cofan.mk W.left ι))` is the scheme coproduct universal property,
  and `∀ i, IsAffine (A i)` states exactly that each summand is affine. Scheme coproducts
  are disjoint unions with open components; this does not assume a finite index set.
- Each component factors over an affine open of S through the quantified
  `U : S.Opens`, `IsAffineOpen U`, and `a : A i ⟶ U.toScheme`, with the triangle
  `a ≫ U.ι = ι i ≫ W.hom`. This imposes no affineness on S itself.
- `IsRepresentable w ∧ IsSurjective w ∧ IsEtale w` uses the dependency's scheme-test
  definitions of representable, surjective and étale natural transformations.
  `Function.Surjective (schemePointMap w)` separately retains point-surjectivity.
- The existential topology `τ : TopologicalSpace (Point E.obj.obj)` satisfies
  `τ = TopologicalSpace.coinduced (schemePointMap w) inferInstance`. By the actual
  definition of `coinduced`, a subset is open exactly when its inverse image is open
  in W. Together with point-surjectivity, this is the required quotient topology.
- The next universally quantified clause over every scheme V and map p equates τ with
  the coinduced topology whenever p is representable, surjective and étale. This is
  independence from every such atlas, without requiring V to be a union of affines.
- The final universal clause covers every scheme T over S and every morphism t,
  without any étaleness hypothesis for continuity. `@Continuous ... τ (schemePointMap t)`
  is continuity from the ordinary topology on T to precisely τ.
- Under only `IsEtale t` (which already includes representability),
  `@IsOpenMap ... τ (schemePointMap t)` states openness, and
  `@IsOpen ... τ (Set.range (schemePointMap t))` retains the final open-image clause.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`
  and `Spec.map`. `Over S` retains all structural maps to S.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentable`, `IsSurjective`, `IsEtale`, and the underlying
  presheaf `E.obj.obj`. Their full defining signatures were read.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, used in the
  scheme-test definition of representable étaleness.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  canonical open-subscheme inclusions are `U.ι`, with domain `U.toScheme`.
- `Mathlib.Algebra.Field.Defs`: `Field`, not a field plus a stronger extension condition.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.fromSpecResidueField`, used in the explicit point map.
- `Mathlib.AlgebraicGeometry.Limits`: scheme coproducts; `Cofan` and `IsColimit`
  express their universal property. The proof-only scheme lemmas are in this module,
  `OpenImmersion`, `AffineScheme`, `Morphisms.Etale` and `Morphisms.UniversallyOpen`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint`:
  `AlgebraicSpace.exists_scheme_fibreProduct_point`, imported privately as soon as its
  stage-2 declaration became available during this work. Its common-field compatibility
  and scheme-representing pullback signature were read in full.
- `Mathlib.Topology.Defs.Induced`: `TopologicalSpace.coinduced` is the ordinary final
  topology, not an arbitrary topology on a different point set.

Edge cases checked before writing: the empty algebraic space admits empty W and an empty
index family; `Cofan` does not require `Nonempty I`. No nonempty base or space, finite
index, quasi-compactness, separatedness, or characteristic assumption is introduced.
For a scheme algebraic space the residue-field classes recover its ordinary points;
the topology statement applies to its identity atlas. A non-surjective étale t still
has an open image; surjectivity is required only for atlases. Points represented over
different fields can agree after a common extension. All fields and schemes use the
universe u of the recorded big site, the index is `Type u`, and the quotient lives in
`Type (u+1)` because its field representatives quantify over `Type u`. The latter is a
representation size, not an exclusion of point classes. All variables and universes
are explicit. There are no hollow definitions, extra theorem obligations or statement
corrections, and no STATEMENT-DISPUTED issue.

Searches for an existing theorem (all through the prescribed msearch wrapper where
applicable, plus direct source reads):

- LeanFinder: "Every algebraic space admits a surjective etale atlas which is a disjoint
  union of affine schemes and its quotient topology is independent of the atlas".
  Eight scheme/ring results: AffineSpace.instSurjectiveOverSchemeInferInstanceOverClass,
  Scheme.Etale, instSurjectiveDescI₀SchemeF, Scheme.etalePretopology,
  Scheme.instCategoryEtale, Scheme.smallEtalePretopology, instUniqueI₀SchemeCover,
  Algebra.IsStandardEtale.of_surjective. None states the algebraic-space theorem.
- Loogle: `AlgebraicGeometry.AlgebraicSpace, AlgebraicGeometry.Etale`: zero hits,
  unknown identifier AlgebraicGeometry.AlgebraicSpace.
- Mathlib grep: `AlgebraicSpace|PointClass|FieldPoint` under AlgebraicGeometry:
  18 hits, all PointClass hits about Weierstrass elliptic-curve coordinates.
- Upstream rg for the node id, AlgebraicSpace, PointClass, and FieldPoint found no
  corresponding algebraic-space theorem or quotient; FieldPoint hits were scheme-only.
- Side-library rg and direct reads found AlgebraicSpaceJointSurjectivity,
  AlgebraicSpaceFibreProductPoint and AlgebraicSpaceAffineAtlasOpenCover. The first two
  expand representative conditions; the third is the different Tag 03FY open-subspace
  cover, not the Tag 03FX single disjoint-union atlas and topology theorem.

The source was read directly in spaces-properties.tex: the relation preceding Tag 03BU,
definition-points and lemma-scheme-points, Tag 03BX (lemma-topology-points and proof),
and Tag 03FX (lemma-cover-by-union-affines and proof). No online source was needed.

Validation: every delivered module is compiled separately through scompile.py; the
initial IsColimit-in-Prop elaboration error was fixed by `Nonempty (IsColimit ...)`.
The delivery dry run and its per-file checks are run after the final record generation.

## New nodes

`def-a1-algebraic-space-point-classes` supplies the missing quotient point type and its
canonical map from scheme points, in `AlgebraicSpacePointClasses.lean`. Its source is
Tag 03BU, the preceding common-extension relation, and the following scheme-points
identification. The data are explicit: a field-valued representative, the common-field
relation, its quotient, and the residue-field representative of a scheme point.
This is needed to type the topology clauses; it does not redefine the existing
`IsJointlySurjective` family predicate, which works without constructing a quotient.
The joint-surjectivity node's statement explains point classes but its only recorded
and implemented declaration is that family predicate. Neither it nor the existing
fibre-product-point theorem provides a point type or map with which to state continuity.
Their implementations and records are unchanged.

Searches: LeanSearch "quotient of field valued points of an algebraic space by common
field extensions" returned eight hits (scheme residue-field equivalences and unrelated
Galois, Brauer and rational-map quotients), no algebraic-space point quotient. Loogle
`AlgebraicSpace.Point, Quot` returned zero hits / unknown identifier AlgebraicSpace.Point.
Mathlib grep `PointRepresentative|schemePointMap|namespace AlgebraicSpace` returned zero
hits. Upstream and side rg for these names and quotient-point patterns found no such
construction. DAG searches for field-valued point classes and common field extensions
found the family predicate and statements using the notion, no quotient definition.
`blueprint_refs.py search 'field-valued point classes'` returned zero blueprint nodes;
`blueprint_refs.py ancestor` confirmed `lem-a1-affine-hc0`. The new id had no matches.
The node records the search queries and results. Its chapter and unit are the item's,
and it is cited directly in the item's added stmt_deps.

Preflight metadata repair: the new definition uses the chapter prefix `a1`, and its
blueprint.from.via records the complete created.item chain required by the server.

## Second reading by Q05

Independent maintainer reading of immutable delivery
cc891cf4c7a054ab3c10257c86757364699ab733, 2026-10-18. This section replaces the
worker's placeholder; it does not assert that the worker performed a second reading.

I read the item and all seven statement dependencies from the immutable snapshot,
both delivered Lean files, their complete docstrings and declarations, and the source
in spaces-properties.tex: the common-extension relation and definition-points
(Tag 03BU, lines 235-287), lemma-scheme-points, lemma-topology-points and its proof
(Tag 03BX, lines 372-457), and lemma-cover-by-union-affines and its proof
(Tag 03FX, lines 699-722). I also read the actual recorded algebraic-space interface
in the read-only group clone, including IsRepresentableWith, IsRepresentable,
IsEtale, IsSurjective, IsAlgebraicSpace and AlgebraicSpace, and the scheme fibre-product
point declaration used by the proof plan.

Hypotheses and clauses, checked individually:

- `{S : Scheme.{u}}` is an arbitrary scheme; `(E : AlgebraicSpace S)` is the recorded
  full subcategory of fppf sheaves with representable diagonal and a surjective etale
  scheme atlas. There is no separation, quasi-compactness or finiteness hypothesis.
- `PointRepresentative` stores an actual field K, its map to S and a presheaf value.
  `Rel` is equality after pullback along two field-spectrum maps over S. By full
  faithfulness of Spec these are exactly field embeddings into a common extension.
  `Point` is their generated quotient. The relation is already an equivalence:
  transitivity uses an amalgam of the two extensions over the middle field, so the
  generated quotient adds no unintended identifications. This also works for arbitrary
  presheaves, as the new definition node states. No data are supplied by sorry.
- `schemePointMap` explicitly uses `residueField`, `fromSpecResidueField`, the composite
  structural map to S, and the Yoneda evaluation of t. It is the canonical residue-field
  class in the node, with no arbitrary map or choice of atlas.
- `W : Over S`, the family `A : I -> Scheme.{u}`, and
  `Nonempty (IsColimit (Cofan.mk W.left iota))` say W is the coproduct of the family.
  Scheme coproducts are actual disjoint open unions (Mathlib Limits, sigmaOpenCover,
  sigmaMk and disjoint_opensRange_sigmaiota). Every member is affine. The existential
  affine open U of S and `a >> U.iota = iota i >> W.hom` give the required factorization
  of every component; S itself need not be affine.
- `IsRepresentable w`, `IsSurjective w`, and `IsEtale w` have the recorded scheme-test
  meanings. `Function.Surjective (schemePointMap w)` independently retains the explicit
  point-surjectivity clause.
- The topology tau is on exactly `Point E.obj.obj`. Its equality with the coinduced
  topology means an open set has open inverse image in W; together with surjectivity
  this is the quotient topology. The next quantifier covers every representable
  surjective etale scheme atlas, with the same tau, establishing independence.
- The last quantifier covers every T over S and every map t, with unconditional
  continuity into tau. Only the open-map and open-range clauses require `IsEtale t`.
  That predicate already includes representability. No surjectivity of t is assumed.

All five proof steps are present in the theorem docstring. Step 1 refines the atlas
by affine opens over affine opens of S and takes their coproduct. Step 2 represents
scheme tests by coproducts of the pulled-back open pieces; etaleness is affine-local
and surjectivity follows from coverage. Steps 3-5 use the scheme fibre product and
open etale projections to compare inverse images, descend continuity and descend
openness. The imported exists_scheme_fibreProduct_point supplies precisely a
representing scheme and a point over compatible field representatives, not an
unrelated product. Its expanded field condition agrees with equality in Point.
The elementary set-image arguments do not assume a fibre-product bijection on points.

I checked the dependency declarations in Mathlib Scheme (Scheme, Hom, Spec, Spec.map),
OpenImmersion (IsOpenImmersion), Morphisms/Etale (Etale and its flat/unramified/finite
presentation characterization), Algebra/Field/Defs (Field), ResidueField, and
Topology/Defs/Induced (coinduced). Every dependency has the required interface; no
section 1(B) repair is needed. The new definition node is in the item's chapter,
kind definition, status split, cites its ingredients, has empty proof/proof_deps,
mathlib_match null, worker creation metadata, blueprint ancestry, none audits and
all four declarations recorded. Its source and statement agree.

Independent rg searches in upstream WeilConjectures, Mathlib AlgebraicGeometry and
the side library found no pre-existing field-point quotient or identical theorem.
I opened AlgebraicSpaceJointSurjectivity and AlgebraicSpaceAffineAtlasOpenCover:
the former defines a lifting predicate, not a quotient, and the latter is Tag 03FY's
open-subspace cover, not this Tag 03FX atlas/topology result. The worker records
LeanSearch, Loogle/LeanFinder and text searches; their results do not identify a match.
The missing quotient helper is properly supplied in this delivery under section 1(A).

Edge cases: I may be empty; no Nonempty or Fintype instance is required. Empty E has
empty W and empty point set, and all assertions still hold. Scheme identity atlases
recover the usual topology. Non-surjective etale maps still have open images. Fields
of every characteristic and arbitrary, including transcendental, common extensions
are permitted. Scheme and field universes follow the recorded big site u; the index
can be the atlas's set of points in Type u, while representatives and their quotient
live in Type (u+1). This size increase imposes no equality of independent universes
and excludes no test schemes of the recorded site. Every binder is explicit.

Both new lean.statement fields were compared with the declarations verbatim. Both
modules have source/blueprint module and declaration docstrings, no line over 100
characters, no local proof beyond the item's sole `by sorry`, and no hollow definition.
Private imports of proof-dependency modules are allowed by brief-stage2 section 3.
No statement_change is necessary and no citer audit is triggered. No pro-etale
substitute or dropped infinity/dg/model machinery occurs. The current route-pivot
list has no item statement/proof dependency on it, and no repair note for this item
exists at origin/newtargets-dag.

Finding H11 (also the substantive report requirement of H1): the delivered second
reading heading contained only a placeholder. This complete independent reading
repairs that mechanical landing defect. The Worker report and mathematical files
are retained. No substantive mathematical fault was found.

Compiler evidence and final checks:

I reproduced compilation from the immutable snapshot using exactly:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q05 lem-a1-space-affine-etale-cover snapshot/lean/Sheaf/AlgebraicGeometry/AlgebraicSpacePointClasses.lean snapshot/lean/Sheaf/AlgebraicGeometry/AlgebraicSpaceAffineEtaleCover.lean
```

Result: exit 0, no errors or warnings. The wrapper compiled the sibling point module
into a private overlay, then separately checked the point module and the cover module.
Its output recorded: private overlay point module 16.4 s; preliminary point module
11.1 s; sandbox point module 2.2 s; library point module 15.0 s; sandbox cover module
21.2 s; library cover module 13.7 s. Each invocation retained the 60 s limit.
The installed scompile.py currently sends its payload to nt_srv_compile.py
--wire-confirm, rather than exposing a local-only option; this prescribed wrapper
provided both the private side overlay and server confirmation. I did not invoke
ssh directly. The delivered report's compile paragraph was a claim without attached
success output; this independent successful reproduction supplies the missing evidence.
No compiler-affecting file was changed by the review, so the report-only repair needs
no additional compilation.

The replacement report filename was checked against merge_delivery.py's stage-2
--apply-fixes handler (rep_name = item + '.report.md'). It is a complete replacement,
not a patch or an instruction to the group. I did not run merge, deliver, preflight,
a global build or any direct repository mutation. All delivery reads used the
snapshot; dependency and literature context came from the permitted read-only clones.
The immutable delivery and branch head were not changed. The only reviewer writes
are review.md and the complete report under fixes/.

Final finding list: H11/H1 second-reading placeholder, fixed by this replacement
report; no mathematical, universe, dependency-interface, hollow-definition,
statement-verbatim, docstring, compilation or route-pivot fault found. Verdict FIX.
