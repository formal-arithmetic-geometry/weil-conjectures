## Worker report

This stage-2 delivery states `AlgebraicGeometry.AlgebraicSpace.regularGroupRigidifiedLineExtension`
in `lean/Sheaf/AlgebraicGeometry/RigidifiedLineExtension.lean`, with `sorry` as its entire
proof. Two definition modules supply the previously absent notions. The landed Q04 node
`def-sfb-space-module-tensor-composition` supplies the existing tensor-composition interface;
this delivery does not modify its node or declarations. No
existing statement, proof plan, source, or reviewed split is changed. The item's
`stmt_deps` gains the two new definitions, the landed Q04 tensor-composition definition,
and the landed regular-scheme definition.
No existing dependency record is changed.

The prior worker ending concerned the stage-1 split, already accepted from Q125. The live
node has no Lean record; `coord/queue.tsv` lists this item at stage 2. The explicit stage
handoff in `coord/brief-stage2.md` section 0 applies. This is the statement of the accepted
split, not a second stage-1 split. This packet repairs the independent review of returned head `0c5fed853864`, as detailed below.

Clause-by-clause correspondence:

- The regular locally Noetherian base is `(S : Scheme.{u}) [IsLocallyNoetherian S]
  [IsRegular S]`. The imported recorded `IsRegularScheme` definition is exactly this
  conjunction; its existing upstream stalkwise class `IsRegular` is reused. No global
  Noetherian, quasi-compact, separated, integral or connected condition is imposed on S.
- The dense open immersion is `(V : Scheme.{u}) (j : V ⟶ S) [IsOpenImmersion j]
  (hj : DenseRange j.base)`. It need not be quasi-compact and may be the identity.
- The algebraic space is `(G : AlgebraicSpace S)`. Its structural map is the unique map
  `groupSpaceProjection G` to `groupSpaceBase S = schemeSpace (Over.mk (𝟙 S))`.
  This represents the p in the prose; it is not an arbitrary additional structure map.
- `(H : CommutativeSpaceGroup G)` contains actual commutative group structures on every
  functor-of-points value and preservation of multiplication and identity by restrictions.
  Inverses are preserved because a unital multiplicative map between groups preserves
  inverses. Thus this is precisely a natural group-space law, not just unrelated groups.
  Its identity section `H.identity` sends every point to 1. Yoneda gives the operations
  as space morphisms, including multiplication on the sheaf product.
- `hG : IsSmoothIntegralGroupSpace G` consists of six conditions: chartwise smoothness,
  separated relative diagonal, chartwise local finite presentation, quasi-compact p,
  quasi-compact diagonal, and `GroupSpaceIntegralFibres G`. The latter tests every
  algebraically closed field K in universe u and every Spec K → S, requiring an
  irreducible point space and reducedness of every representable étale scheme chart.
  These are integrality of the fibre, not integrality of every chart (which would
  incorrectly exclude disjoint chart unions). Finite presentation includes both its
  global conditions, rather than just local finite presentation.
- `Gᵥ`, `pᵥ`, `i`, and `hcart : IsPullback ...` represent the actual G ×_S V with its
  two projections. `eᵥ`, `we`, and `heᵥ` specify its induced identity section. These
  are presentations of the named base-changed object, not extra geometric hypotheses:
  the fibre-product universal property supplies them and makes them unique. Every
  model is allowed. Everything remains in the category of spaces over S, including
  represented V; the small étale module categories are those already defined there.
- `RigidifiedModule e` is the existing costructured-arrow category of maps e*L → O.
  `IsRigidifiedLine e` requires `X.IsLineModule L.left` and `IsIso L.hom`.
  `RigidifiedLines e` is its full-subcategory core. Consequently its objects retain
  the chosen rigidification, and its arrows are precisely line-module isomorphisms
  satisfying e*(v) followed by the target rigidification = source rigidification.
- The first conclusion is `(...rigidifiedLinePullback ...).IsEquivalence` for the
  canonical tensor restriction along i, including the induced identity trivialization.
  Essential surjectivity gives extension of every specified rigidified line. Full
  faithfulness gives a unique extension of each specified rigidification-preserving
  isomorphism. No multiplication-compatible structure on the line is assumed.
- The second conclusion quantifies every étale scheme map `a.left : T.left ⟶ S`.
  `IsPullback k.left d.left j a.left` is U = V ×_S T. The next three pullback squares
  give G', Gᵥ' and their actual projection maps b,c,i'. Their sections are induced by
  the three commuting section squares. The asserted natural isomorphism z compares
  restriction then pullback with pullback then restriction. Its map on underlying
  modules is fixed to `moduleTensorComposition c i`, equality along `hb`, and
  `(moduleTensorComposition i' b).inv`. These are the existing tensor-normalized
  comparisons. Naturality includes the specified isomorphisms. The new definition
  node also records uniqueness of this comparison for every such square, so successive
  comparisons are coherent; full faithfulness gives unique comparison of extensions.
- Every module pullback in all three modules is the recorded `moduleTensorPullback`,
  with its existing `moduleTensorSquare` and `moduleTensorComposition`. No freely
  supplied inverse image functor, ringed-site map, unit isomorphism or comparison is
  used as a hypothesis. The new unit identification is chosen only from an existence
  and uniqueness statement fixing its value on ALL local tensors to multiplication.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`; its upstream
  `WeilConjectures.AlgebraicGeometry.Regular` class `IsRegular` supplies stalk regularity.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`, `IsLineModule`,
  `Modules`, `EtaleSite`, `structureSheaf`. These are the recorded definition, no copy.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace` and its representable
  sheaf construction, owned by the landed `def-trf-scheme-algebraic-space`. The canonical
  ringed-site model is unchanged.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleTensorPullback`,
  `moduleTensorSection`, `ModuleChart`, `moduleChartScalar`, `moduleTensorAdjunction`.
- `Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange`: `moduleTensorSquare`,
  `moduleTensorComposition`, `moduleCompositeChart`, and their two supporting theorems;
  read their complete normalized pure-tensor signatures and docstrings. The four composition declarations have
  landed Q04 ownership in `def-sfb-space-module-tensor-composition`; `moduleTensorSquare`
  is the displayed composite of those comparisons and equality of space maps.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsSeparated`, `MapIsLocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact` (only this generic
  definition, no proper-curve assumption).
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology` and `AlgebraicSpacePointClasses`:
  `Point`, `pointTopologicalSpace`. Fibres use the actual presheaf fibre product.
- `Mathlib.AlgebraicGeometry.Properties`: `IsReduced` on scheme charts.
- Proof-only import `Sheaf.AlgebraicGeometry.AlgebraicSpaceInvertibleDescent`:
  `exists_lineModule_of_etale_descent` with its actual specified overlap data and Hom
  bijection. The vertical-divisor and divisor-line-dictionary proof nodes have no Lean
  record yet, so there is no corresponding module to import. Their full accepted proof
  plan is reproduced in the main theorem docstring.

Edge cases checked before writing: S empty (then G and V are empty), V=S (restriction
is identity up to canonical tensor comparison), trivial group G=S, G_m over a DVR with
its generic open, and disjoint/reducible regular bases. No connectedness, nonemptiness,
positive dimension or characteristic restriction appears. Finite and infinite affine
covers are admitted. The empty dense open forces S empty. Étale charts of an integral
fibre can be disconnected; reducedness is checked chartwise, irreducibility on the
fibre itself. No independent smaller field/test-scheme universe makes the geometric
condition vacuous. An arbitrary algebraic space is retained throughout.

Searches: all `msearch.py` invocations used group Q21 and this item; their real outputs
are logged in `searches.jsonl` and represented in both new nodes' `mathlib_searches`.
LeanFinder queries were the extension theorem in plain language, the rigidified line
module groupoid, and smooth commutative group algebraic spaces with integral fibres.
LeanSearch queried commutative group spaces, rigidified lines and tensor composition.
Loogle queried `AlgebraicGeometry.AlgebraicSpace, CategoryTheory.Equivalence` (unknown
AlgebraicSpace in Mathlib) and `AlgebraicGeometry.Smooth, AlgebraicGeometry.GeometricallyIntegral`
(no hits). Mathlib grep queried `Rigidified|rigidified|AlgebraicSpace` (0 hits) and
`RigidifiedLine|CommGroupSpace|GeometricallyIntegral` (scheme integral-fibre and abelian
scheme hits). The scheme and manifold results do not state this space theorem.
Project searches with rg in BOTH WeilConjectures and Sheaf found no rigidified-line
category or space-group definition. Broader rigidifi hits concern scheme gluing of
trivializations or moduli level structures; their objects differ. `blueprint_refs.py`
searches for 'rigidified line' and 'group algebraic space' returned 0 nodes; definition
node grep likewise found no such existing definition node. Searches discovered and
allowed reuse of the exact tensor-module operations and their normalized comparisons.

Primary source read: Deligne, Le lemme de Gabber, Section 4.2, printed p.142, PDF page
12, https://www.numdam.org/article/AST_1985__127__131_0.pdf. Lines 378–395 explain
extension over the regular universal bases, identity correction and uniqueness from
irreducible geometric fibres, followed by étale compatibility. Section 1.1 explains
commutative group algebraic spaces. The delivery states the accepted general supporting
lemma; it does not change the unit or insert a Picard-scheme restriction.

Validation: each delivered file has been compiled separately with `scompile.py`, then
all three were compiled together by that wrapper in dependency order. Every file was
clean, with no unexpected warnings. All universes and variables are explicitly bound,
and all files begin with `module`. No theorem is proved, no definition has sorry data,
and the two choices use uniquely normalized universal properties. No statement dispute
or correction is needed.

## New nodes

`def-sfb-rigidified-space-lines`: groupoid of actual rigidified line modules, its canonical
tensor pullback, the multiplication-normalized unit identification, underlying-module
forgetful functor and the uniquely tensor-normalized comparison for commuting squares.
The complete notion is absent from the DAG and both source trees; Mathlib supplies
costructured arrows, full subcategories and cores, all reused. Source: Deligne 4.2 and
Stacks 03D7/03G8. Three kinds of actual searches are in the node. Its three postponed
supporting theorems are named, attached to this node and have full source/proof docstrings.
Definitions contain real constructions; only the unit identification is chosen, from
its complete unique pure-tensor characterization. The other pullback comparisons were
already supplied by a landed module and are reused.

`def-sfb-smooth-integral-group-space`: natural commutative groups on the functor of points,
identity section, represented base, structure and represented scheme maps, and the exact
smooth/separated/finitely-presented/integral-geometric-fibre predicates needed here.
Source: Deligne 1.1/4.2 and the existing Stacks-based chart definitions. This specializes
the existing generic space morphism chart test and quasi-compactness, without copying
them. No properness, scheme representability or dimension bound enters. The three kinds
of actual searches found only scheme groups and manifold sheaves, which do not provide
this notion. All definitions have actual data. This node's recorded main declaration
and its declaration list jointly give both the group law and geometric hypotheses.

Both new nodes retain blueprint.from.node = null: the prescribed ancestor command
reports that the inherited item's ancestor is None. Their via chains put the item in
front of its inherited via chain, and their place names the precise supporting proof
notion. This is the existing blueprint linkage; it is not silently fabricated.

The existing Q04 node `def-sfb-space-module-tensor-composition` is reused directly.
It records `moduleCompositeChart_triangle`, `moduleCompositeChart`,
`moduleTensorComposition_existsUnique` and `moduleTensorComposition` in the unchanged
`Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange` module. Its unique local-tensor
formula is precisely the composition comparison used in the main theorem and in
`RigidifiedLines`. The same module's `moduleTensorSquare` is definitionally the first
composition comparison, equality of the composite maps, and the inverse of the second.
No additional structure or flatness assumption is used. This existing node is not part
of this packet and no replacement ownership record is delivered.

## Second reading by Q21

No independent worker was started, as the dispatcher brief expressly forbids other
agents. The maintainer's independent delivery review supplies the independent reading.
A final self-check opened all three modules and all delivered nodes: all hypotheses and
clauses map as above; the item statement and accepted proof split remain unchanged.

Dry-run repair: current preflight requires `import_flags` on every new definition node;
both now carry the empty list. The first dry run compiled all three files and rejected
only these two missing fields; nothing was pushed.


## Repair of returned head 0c5fed853864

F1 (H12/H2): replaced the theorem-node citation in
`def-sfb-rigidified-space-lines` by `def-sfb-space-module-tensor-composition` and
added that definition owner directly to the item's `stmt_deps`, since its displayed
formula uses `moduleTensorComposition`. The owner has `existing: true` on the five
unchanged declarations named by the review. Searches of the current read clone found
no landed Q04 owner to reuse. The initial saved-packet dry run passed at `99171f99a58`;
that mechanical pass did not resolve the independent review's missing ownership, so
this repair supplies it explicitly.

F2 (H12): `def-sfb-smooth-integral-group-space` now cites the landed
`def-trf-scheme-algebraic-space` for `schemeSpace`, in both statement and `stmt_deps`,
in place of `lem-trf-space-enlarged-etale-ringed-site-model`. The landed definition's
record names the actual representable-sheaf construction already imported by the
unchanged `RegularGroupSpace.lean`.

The advisory unused ringed-site theorem citation in `def-sfb-rigidified-space-lines`
was removed: its module notions are owned by `def-trf-space-etale-module-functors`.
The optional strengthening of the etale clause was not needed: the reviewer accepted
its precise generic comparison. The item and all three Lean files retain exactly the
reviewed mathematics, signatures, docstrings and sorry-only proofs. The item has no
statement correction; its accepted stage-1 split is preserved.

Self-check: the new owner has no flatness, smoothness, cartesianness or field hypothesis;
composition works for arbitrary composable maps and the square comparison for every
commuting square. Inserting identity maps and identity charts retains the same tensor
normalization. The existing supporting existence-and-uniqueness theorem fixes every
local tensor, so no arbitrary isomorphism is introduced. The new-node dependencies are
exactly its two cited definition nodes. The two repaired new nodes cite definition
owners, and the main item directly owns its displayed tensor-composition use.

Repair validation: `scompile.py` compiled all three delivered Lean modules against the
live published library, separately and in dependency order, without errors or unexpected
warnings. The new existing-declaration owner is also checked by the delivery wrapper.
The local Stacks sources were read at Tags 03D7, 03D8 and 03G8: adjunction, composition
of module pullbacks, and the canonical ringed-topos map for spaces, respectively.

## Repair of returned head b5bfb0f4e603

L: the node `def-sfb-space-module-tensor-composition` now exists on `sheaf-dag`,
created and independently reviewed in Q04's delivery. Removed Q21's redundant node
file from the sandbox packet. The item and `def-sfb-rigidified-space-lines` already
cite that exact id and now resolve it to the landed Q04 record without changing it.
The latter's prose makes explicit that a square comparison is composed from the
recorded composition comparisons and equality of composite space maps. Thus Q04's
four-declaration ownership record suffices, without adding `moduleTensorSquare` to it.

The initial saved-packet dry run passed mechanically at `25e00478d6e` but printed
that Q21's stale copy differed from main in protected fields and dependency lists.
That pass was not treated as repair: removing the redundant node makes this delivery
preserve Q04's live record in full. This supersedes the earlier report's historical
claim that Q21 needed to create a third definition node.

Self-check against current main: only the item gains `lean` and the four additional
statement dependencies; the two new definition nodes are absent from main; the landed
tensor-composition node is neither delivered nor changed. Re-read its full recorded
signature, unique pure-tensor theorem and docstrings in the existing module. All three
Lean files are unchanged from the returned packet, including the theorem's regular,
locally Noetherian, dense-open, group, finite-presentation and geometric-integrality
hypotheses and its two conclusions. The tensor comparison still ranges over arbitrary
maps and the identity-square cases; no canonical map is replaced by a free choice.
No statement correction or statement dispute is introduced.

Repair validation (2026-10-24 UTC): `scompile.py` compiled all three delivery modules
separately and in dependency order against the live build, with no errors or unexpected
warnings. Signature extraction matches all three `lean.statement` records verbatim,
and each `lean.declarations` inventory matches its file. The packet contains exactly
three node files and three Lean modules; Q04's existing node is absent from the packet.
