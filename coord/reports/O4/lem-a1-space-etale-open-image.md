## Worker report

The delivery states `lem-a1-space-etale-open-image` without changing its natural-language
statement. Four named theorems in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage` render its clauses. Each has only
`sorry` as proof and a source/proof-plan docstring. Two new definition modules supply the
missing quotient point space, its explicit topology, and the ordered type of open subfunctors.
All definition data are explicit; none uses a postponed existence theorem or a choice of atlas.

Hypothesis and clause matching:

- The base scheme is `{S : Scheme.{u}}`. The same `u` is used for all test schemes and
  fields, as in the recorded algebraic-space interface; the quotient point type may live
  in `u+1`. No independent, possibly smaller, test-field universe is introduced.
- Algebraic spaces over `S` are `AlgebraicSpace S`, the recorded full subcategory of fppf
  sheaves. Morphisms `q : E ⟶ F` and `g : G ⟶ F` are its natural transformations.
- A field-valued point is `FieldRepresentative`: a field `K : Type u`, structural map
  `s : Spec K ⟶ S`, and section `x`. `FieldRepresentative.Rel` identifies restrictions
  to a common field spectrum over `S`; morphisms between field spectra are the
  contravariant field embeddings. `Points` is the explicit `Quot` of this relation.
  Quotienting a relation imposes its equivalence closure, which here is the usual common
  extension equivalence. `pointImage f` is exactly the set of classes of representatives
  in the source after applying `f`, and chooses no representatives.
- `schemePoint a` sends a scheme point to its residue-field representative. The topology
  `pointsTopologicalSpace` is the supremum of the coinduced topologies of ALL representable
  étale scheme-source maps; its opens are precisely the subsets whose inverse images in
  each such scheme are open. `points_atlas_isOpen_iff`, with `IsEtale a` and
  `IsSurjective a`, states explicitly that a single arbitrary atlas detects the opens.
  Thus the construction gives the specified atlas topology without selecting an atlas.
- `OpenSubspace F` is the subtype of `Subfunctor F.obj.obj` whose inclusion `A.ι` satisfies
  the recorded `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)`. Its order is
  the inherited subfunctor inclusion order. An open representable subfunctor of an
  algebraic space is automatically an fppf sheaf and algebraic space; the definition
  imposes the scheme-test condition used in the node rather than choosing a presentation.
- `openSubspace_points_orderIso` gives an order isomorphism with
  `TopologicalSpace.Opens (Points F.obj.obj)` and requires its value at EVERY `A` to equal
  `pointImage A.val.ι`. This identifies the actual correspondence, rather than merely
  asserting that some unrelated bijection exists.
- In `etale_open_image`, `hq : IsEtale q.hom.hom` is exactly representable étaleness, using
  the recorded scheme-test definition. `IsOpen (pointImage q.hom.hom)` is openness of
  the point image. The existential `A : OpenSubspace F` is the requested image subspace
  `I`, and `pointImage q = pointImage A.ι` identifies it with that image.
- `qI : E.obj.obj ⟶ A.val.toFunctor`, `qI ≫ A.val.ι = q.hom.hom`, `IsEtale qI`, and
  `IsSurjective qI` state the factorization and its representable surjective étaleness.
  Surjectivity here is the recorded condition on ALL scheme base changes.
- The base-change clause quantifies over EVERY `G : AlgebraicSpace S` and EVERY
  `g : G ⟶ F`, with no hypotheses on `g`. Its first conjunct makes
  `(A.val.preimage g.hom.hom).ι` a representable open immersion. This is literally the
  fibre-product subfunctor `I ×_F G`, using Mathlib's `Subfunctor.preimage`. The second
  conjunct equates its point image with that of `(pullback.snd q.hom g.hom).hom`, the
  projection `E ×_F G → G`. Together with the open-subspace correspondence this is
  precisely equality of the image open subspace with the pullback open subspace.
- `CompactSpace (Points E.obj.obj) → CompactSpace (Points A.val.toFunctor)` states
  quasi-compactness of `|I|` when `|E|` is quasi-compact. Mathlib's `CompactSpace` means
  compactness by finite open subcovers and does not assume Hausdorffness.
- `points_compactSpace_iff` quantifies over an arbitrary algebraic space `Z` and states
  both directions of the atlas criterion. Its right side existentially supplies an
  `S`-scheme `U`, `a : yoneda.obj U ⟶ Z.obj.obj`, `CompactSpace U.left`, `IsEtale a`,
  and `IsSurjective a`. No fixed atlas or extra separation condition is imposed.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsEtale`, `IsSurjective`, and `IsAlgebraicSpace`; their full signatures and docstrings
  were read. In particular these are predicates on presheaf transformations, and
  algebraic-space morphisms require `.hom.hom`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and `etale_fibreProduct_isScheme`.
  The actual sheaf fibre product and its second projection are used in the conclusion.
- New definition dependencies use Mathlib `Field` and `CategoryTheory.Subfunctor`
  (`Mathlib.CategoryTheory.Subfunctor.Basic`, and `.Image` for `preimage`).
- Available proof interfaces are imported: `etale_relation_quotient` in
  `Sheaf.AlgebraicGeometry.EtaleRelationQuotient`; `etale_relation_finding_opens` in
  `Sheaf.AlgebraicGeometry.EtaleRelationFindingOpens`; the Mathlib scheme étale
  base-change/composition/open-immersion instances, coproduct constructions in
  `Mathlib.AlgebraicGeometry.Limits`, and affine quasi-compactness/quasi-separatedness.
  The two proof-only nodes `lem-a1-space-affine-etale-cover` and
  `lem-a1-etale-atlas-presentation` have no recorded Lean declaration, so there is no
  proof import for them; the remaining proof interfaces are imported.
  They are not statement prerequisites and no replacement theorem was introduced.

Edge cases checked before writing: the empty algebraic space and empty image give the
empty open subfunctor; the quasi-compact atlas can then be the empty scheme. The identity
map has the whole open subspace as image. An open immersion factors through its own open
subspace. A map into a disjoint component has empty pullback image. Non-surjective `g`,
empty `G`, and arbitrary non-flat/non-étale base changes remain allowed. No Hausdorff
assumption is hidden in quasi-compactness, and no nonempty hypothesis excludes the empty
finite subcover. Fields of the same universe as the big site are allowed without any
finite-type or algebraic-closure restriction. The topological construction uses every
étale scheme-source map, and the atlas theorem ensures independence of presentation.

Searches: `msearch.py` LeanFinder for “Algebraic spaces open subspaces correspond to open
subsets and representable etale morphisms have open image” returned scheme étale-locus,
open-immersion and opens-range results, no algebraic-space statement. Loogle for
`AlgebraicGeometry.AlgebraicSpace, IsOpenMap, Opens` returned unknown identifier/no hits.
Mathlib grep `AlgebraicSpace|OpenSubspace|FieldRepresentative|pointTopology` returned zero
hits. Upstream `WeilConjectures` grep for `AlgebraicSpace` and this item id returned zero
hits. The side library has algebraic spaces and expanded joint-surjectivity but no quotient
point space/topology or open-subspace type. Exact proposed-name checks in the upstream
name inventory and sources found no collision in the algebraic-space namespace. DAG
searches and `blueprint_refs.py search` found no definition nodes for these notions;
`lem-a1-space-affine-etale-cover` is a theorem mentioning the topology, not a definition
interface. Additional LeanSearch, LeanFinder, Loogle and grep queries and their actual
outputs are stored in both new nodes' `mathlib_searches` records.

No statement correction, disputed statement, unusable dependency record, or hollow data.
Validation: all three modules compiled individually through `scompile.py`, with no errors
or warnings. The required delivery dry run follows the node/report preparation.

## New nodes

`def-a1-space-point-topology` supplies field-valued representatives, common-extension
agreement, their quotient `Points`, the image subset `pointImage`, scheme residue-field
points, and the final topology of étale scheme-source maps. Its source is Stacks 03BU,
03BX and the scheme-point construction in the points section. It cites the existing
scheme, algebraic-space and field nodes. The searches above found no existing declaration
or definition node. The existing joint-surjectivity predicate describes lifting after
extensions, not the quotient point space or its topology. The data are explicit; there
are no postponed helper proofs in this definition module.

`def-a1-space-open-subspace` supplies the ordered subtype `OpenSubspace` of actual
subfunctors with representable open inclusion. Its source is Stacks 02YU and 03BZ. It cites
the existing scheme, algebraic-space, subfunctor and scheme open-immersion nodes. Mathlib
has the generic subfunctor and preimage constructions but no algebraic-space open-subspace
type; the upstream and side-library searches likewise found none. The type and its
inherited partial order contain real data and no `sorry`.

Preflight metadata repair: the server reports a longer current blueprint ancestry than
the initial shared checkout. Both new nodes now carry that complete current via path.
The first dry run had no compile or mathematical finding; it rejected only those two
ancestry records. The corrected packet is rechecked by the required dry run.

## Second reading by N4

Read packet.md, check-brief2.md, the immutable item node, all six statement dependencies, the source place (Stacks spaces-properties.tex Tags 03BX, 03BZ, 03IR, 03H4, 03H5, 03E4), and all three delivered Lean modules. The four theorem signatures in `AlgebraicSpaceEtaleOpenImage.lean` render the node clauses in order: atlas topology, open-subspace order correspondence, open etale image with factorization/base change/quasi-compactness, and the compact-point atlas criterion. The two definition modules provide explicit field representatives/relations/quotient points/topology and the ordered open-subfunctor subtype; no hollow data or pro-etale machinery occurs.

Checked hypotheses, quantifier order, universes, dependency declarations, source and blueprint docstrings, and edge cases (empty spaces/images, identity/open immersions, empty base change, arbitrary non-flat `g`, and finite subcovers). Searches recorded by the worker found no existing algebraic-space point-topology/open-subspace/open-image declaration in Mathlib or the project. The source-based proof plan matches the cited Stacks tags and the route-pivot policy.

Per-file compilation was reproduced with `scompile.py` for the two definition modules; the combined three-file overlay invocation was also run, with server-side compilation still pending at review time. No Lean or repository files were modified. The only delivery defect found is mechanical: this section previously stated that no second reading had occurred and therefore was not a real second-reading record. This replacement records the independent checks above.

## Return repair verification

Applied the independent reviewer's supplied replacement report for returned head
`1d6f2f084e5c40ed8f1132951fd6a21d3c61f425`. The three node records match that
immutable packet, and the theorem module is unchanged. Against the current shared
main checkout, the item changes only `lean` and the two added definition dependencies.
All three recorded signatures match their source files.

On 2026-10-18, `deliver2.py N4 lem-a1-space-etale-open-image --no-push` passed
with commit `12cf18afa3`: its combined `scompile.run_many` invocation checked all three
modules together in dependency order, including the final theorem module, and the
server preflight passed. This completes the combined compilation left pending in
the independent review. The repair consists of the supplied independent reading
and this completed verification; no mathematical statement or definition changed.

The returned independent check also required the new point-topology node to make its
`def-weil-field` statement dependency visibly explicit. Its sentence now says “a field
$K$ in the sense of [def-weil-field]”; the dependency remains in `stmt_deps`, and the
definition and Lean declarations are otherwise unchanged.

## Reviewer fix (independent stage-2 review of 570a1e037d55)

One definition per notion (H4). While this delivery was in review, def-a1-algebraic-space-point-classes
(Q05, `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `PointRepresentative`,
`PointRepresentative.Rel`, `Point`, `schemePointMap`) landed on newtargets-dag. It is the same notion as
this delivery's `FieldRepresentative`, `FieldRepresentative.Rel`, `Points` and `schemePoint`: the same
structure, the same common-extension relation, the same `Quot` and the same residue-field map. The
landed lem-a1-space-affine-etale-cover, cited in steps 2, 6 and 10 of this item's proof, is stated on
`Point`. The reviewer therefore made these changes:

- `AlgebraicSpacePointTopology.lean` imports `AlgebraicSpacePointClasses` and keeps only what is new:
  `PointRepresentative.map`, `pointImage`, and the final topology instance `pointTopologicalSpace` on
  `Point F`. The mathematics is unchanged; the topology is the supremum of the coinduced topologies of
  all representable étale scheme-source maps.
- def-a1-space-point-topology now cites [def-a1-algebraic-space-point-classes] for the point classes and
  the scheme point map. It defines only the point image and the topology, and its `lean` record names
  `pointTopologicalSpace`.
- `AlgebraicSpaceEtaleOpenImage.lean` renames `Points` → `Point` and `schemePoint` → `schemePointMap`
  in the four signatures, and adds the proof-only import of the now-recorded
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover`. No hypothesis or conclusion changed.

Per-file compiles of all three modules passed through `nt_compile.py`, with no errors or warnings. A
probe checked that `A ≤ B ↔ A.val ≤ B.val` holds by `Iff.rfl` on `OpenSubspace`, and that `O` is open
iff `schemePointMap a ⁻¹' O` is open for every étale `a : yoneda.obj T ⟶ F`.
