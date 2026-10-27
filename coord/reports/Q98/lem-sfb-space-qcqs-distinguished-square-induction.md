## Worker report

States `AlgebraicGeometry.AlgebraicSpace.qcqs_etale_distinguishedSquare_induction`
in `Sheaf.AlgebraicGeometry.SpaceQcqsDistinguishedSquareInduction`. The only new
Lean declaration is this theorem, with proof `by sorry`. No definitions or proofs
are introduced. The source was read directly in
`literature/stacks-project/spaces-perfect.tex`, lemma-induction-principle (08GP),
including its proof and the preceding distinguished-square restriction lemma.
The mathematical statement is unchanged.

Clause-by-clause correspondence:

- The base scheme and universe convention are `{S : Scheme.{u}}` with explicit
  `universe u`; `X : AlgebraicSpace S` is the recorded fppf-sheaf definition.
  No separation or quasi-compactness condition is imposed on S.
- Quasi-compactness of X is `hXqc : CompactSpace (Point X.obj.obj)`, using the
  existing atlas topology. This is exactly the finite-subcover condition.
- Absolute quasi-separatedness is `hXqs : IsAbsolutelyQuasiSeparated X`.
  This existing definition is the equivalent affine-pair scheme-test criterion
  for the absolute diagonal (Stacks 0AHR), not the relative diagonal over S
  or mere topological quasi-separatedness.
- The property of etale maps T to X is `P : Over X → Prop`. Its relevant
  domain is restricted explicitly by `IsChartwiseEtale T.hom`,
  `CompactSpace (Point T.left.obj.obj)`, and
  `IsAbsolutelyQuasiSeparated T.left`. P may be extended arbitrarily outside
  that domain: no assumption or conclusion reads such an extension value.
  For affine objects the latter two predicates follow from affineness.
- Isomorphism invariance is `h_iso`, restricted to two objects in that domain,
  and an isomorphism `T ≅ T'` in the over category. Thus the isomorphism
  commutes with the maps to X and preserves both truth directions.
- Assumption (a) is `h_affine`. Its affine test is an actual `A : Over S`
  with `IsAffine A.left` and an isomorphism of presheaves
  `T.left.obj.obj ≅ yoneda.obj A`. This permits every affine scheme, not just
  a chosen collection of charts, and imposes no nonemptiness assumption.
- Assumption (b) is `h_square`. W, U, V and O are algebraic spaces with
  their maps to X (`Over X`). Each has the domain conditions explicitly
  listed. In particular W is qcqs and U is quasi-compact as required.
  Quasi-separatedness and etaleness of the other vertices are precisely
  the node's sentence that all objects in (b) belong to P's domain.
- The morphisms `i : U ⟶ W`, `p : V ⟶ W`, `a : O ⟶ U` and `b : O ⟶ V`
  are over X. `IsPullback a.left.hom b.left.hom i.left.hom p.left.hom`
  says that the fourth vertex O is the sheaf fibre product U times_W V.
  It does not ask only for a cartesian square of point sets.
- The open immersion is identified with the recorded `OpenSubspace W.left`:
  an isomorphism `e : U.left.obj.obj ≅ A.val.toFunctor` with
  `e.hom ≫ A.val.ι = i.left.hom.hom`. Thus this is the actual open-subfunctor
  inclusion, with arbitrary isomorphic presentations allowed.
- The other square map is representable etale by `IsEtale p.left.hom.hom`.
  Its source V is affine by the same scheme-representability criterion as (a).
  The domain etaleness of T to X uses the existing chartwise notion;
  representability is required separately for p exactly where the node asks.
- `C : ClosedSubspace W.left` is reduced by
  `IsReduced (C.val : AlgebraicSpace S)`. Its support equation
  `pointImage C.val.arrow.hom.hom = (pointImage i.left.hom.hom)ᶜ`
  identifies it with the reduced closed complement Z.
  `IsIso (Limits.pullback.snd p.left.hom C.val.arrow.hom)` is exactly the
  projection V times_W Z to Z. The dependency's existence and uniqueness
  ensure that quantifying over such complements is equivalent to using Z.
- The implication `P U → P V → P O → P W` is the three-premise gluing clause.
- The first conclusion quantifies every qcqs chartwise etale algebraic space
  T over X. The second conclusion `P (Over.mk (𝟙 X))` explicitly includes X.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale` and the full-subcategory morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `Point`,
  `pointImage`, `pointTopologicalSpace` (Point is re-exported from PointClasses).
- `Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport`:
  `exists_unique_reduced_closed_subspace`, with its `ClosedSubspace` and
  `IsReduced` dependencies.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`. The landed node
  `def-sfb-space-absolute-quasi-separated` was added to stmt_deps.
- `Sheaf.AlgebraicGeometry.AtlasEtaleRestriction`: re-exports the existing
  `IsChartwiseEtale` from `EnlargedEtaleRingedSite`. The new definition node
  `def-sfb-space-chartwise-etale-morphism` now records that existing predicate
  directly; no enlarged-site comparison theorem is a statement prerequisite.
- Proof imports: `SpaceQuasiCompactAffineTests` (its four scheme-test,
  locality, base-change and representability statements),
  `WeilConjectures.AlgebraicGeometry.QuasiCompactOpenInduction`
  (`quasiCompactOpen_induction`), `SpaceChangeBase` (`exists_spaceChangeBase`),
  and `AlgebraicSpaceEtaleOpenImage` (`etale_open_image` and open-subspace
  and compactness comparisons). Their signatures and source docstrings were read.
- Proof nodes `lem-sfb-space-qcqs-permanence`,
  `lem-sfb-qcqs-space-splitting-filtration` and
  `lem-a1-space-point-open-calculus` currently have no recorded Lean declaration,
  so no proof import is supplied for them. They are not statement prerequisites.
  `lem-weil-pbc-qcqs-finite-affine-open-cover` is a Mathlib leaf using
  `isCompact_iff_finite_and_eq_biUnion_affineOpens`, already reached through
  the proof imports. No import was omitted to avoid an import cycle.

Edge cases checked before writing and on second reading: the empty affine
scheme (including an empty X) is admitted by `IsAffine` without `Nonempty`;
U empty makes the complement all of W, so the distinguished condition is
that p is an isomorphism; U = W makes the complement empty and the same
condition is automatic there; V may be empty; all square objects may be
algebraic spaces except the affine V requirement. S is arbitrary, including
non-quasi-separated S. No independent smaller test universe is used. Arbitrary
presentations of overlaps and complements are permitted through the actual
sheaf universal property and isomorphism invariance. No disputed statement
or statement correction was needed.

Searches made (2026-10-24):

- `msearch.py ... leanfinder` with “A property of quasi compact quasi separated
  etale algebraic spaces holds by induction using affine spaces and elementary
  distinguished squares”: 8 hits, including scheme compact-open induction,
  scheme quasi-separatedness and scheme etale composition; no space statement.
- `msearch.py ... leansearch` with “Induction on quasi compact quasi separated
  algebraic spaces with elementary distinguished squares”: 8 hits, all scheme
  or topological quasi-separatedness predicates/recursors; no matching statement.
- `msearch.py ... loogle` with
  `AlgebraicGeometry.compact_open_induction_on, AlgebraicGeometry.quasiCompactOpen_induction`:
  0 hits, the project induction identifier is unknown to the search service.
- `msearch.py ... grep 'induction|[Dd]istinguished[Ss]quare' AlgebraicGeometry`:
  25 displayed hits, including scheme compact-open and etale-object induction,
  but none for algebraic spaces.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf`, including the item id,
  distinguished-square names, absolute quasi-separatedness and quasi-compactness
  predicates, found proof-docstring references to this item but no declaration.
  It found the existing `IsAbsolutelyQuasiSeparated` and `IsChartwiseEtale`
  interfaces, reused here. DAG searches located uses of these interfaces; the repair below adds the
  missing dedicated definition node for chartwise etaleness.
  The chosen theorem name has no pre-existing Mathlib or project occurrence.

Validation: scompile.py compiled both the sandbox probe and the final library
module successfully against the live published library (and refreshed the
landed SpaceChangeBase overlay). No compiler errors or unexpected warnings.
`set_option autoImplicit false` checks all variable and universe binding.

## Second reading by Q98

A second pass reopened the node and the full Lean signature. It checked the
base scheme and absolute (not relative or merely topological) qs condition,
P's domain, both directions of over-X isomorphism invariance, the empty affine
case, all four square vertices, the open-subfunctor identification, representable
etale p, affine V, reduced closed support, and the actual pullback projection.
It also checked each of the three P premises and both conclusions. All match.
The distinction between chartwise etaleness of objects and representable
etaleness of p was retained explicitly; restricting all objects to representable
etale objects would omit cases. No changes were needed after this pass.
This was an in-session second reading; the dispatcher prohibits starting other
agents, and the maintainer's independent review remains the delivery review.

## New nodes

`def-sfb-space-chartwise-etale-morphism` records the already existing definition
`AlgebraicGeometry.AlgebraicSpace.IsChartwiseEtale` in
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite` with `existing: true`. Its
source is Stacks 03FR (definition-etale), used by 03G0. The definition is
not moved or duplicated. For arbitrary S, X, Y and f, its universal `T : Over S`
and `a : yoneda.obj T ⟶ X.obj.obj` bind every scheme chart; `IsEtale a` is
representable etaleness and `IsEtale (a ≫ f.hom.hom)` is exactly the same
condition on the composite. There is no representability assumption on f.
The ambient `u` and `{S : Scheme.{u}}` use the project's size convention.

Fresh LeanSearch found eight scheme-only etale predicates and permanence facts;
Loogle reported the project name unknown, with zero hits; Mathlib grep for
`IsChartwiseEtale|[Cc]hartwise|[Aa]lgebraic[Ss]pace` in AlgebraicGeometry found
zero hits. The full outputs are preserved in the new node's mathlib_searches.
Project rg found the definition at EnlargedEtaleRingedSite.lean:47 and no
upstream WeilConjectures copy. DAG and blueprint_refs searches found uses in
theorem nodes and unrelated gluing notions, but no definition node owning this
predicate. This is precisely the missing ownership identified by the return.

## Repair of returned delivery

The independent review at a7c45ccdf795 accepted the mathematical statement and
returned one ownership fault. Added the definition node above, replacing
`lem-trf-space-enlarged-etale-ringed-site-model` in the item's stmt_deps. The
theorem's content is not needed to state the induction principle. The Lean
module and its signature remain unchanged. Compared the saved packet with
the current shared node: its only item-field changes are lean and the allowed
statement dependencies. The delivery wrapper refreshes and rebases onto the
current live branch. The initial retained-packet dry run passed at 532b4158475;
that mechanical pass alone did not repair the review fault.

Repair self-check by Q98: reopened the existing definition and Stacks 03FR and
03G0. The new node matches every binder and clause of the actual definition,
including the empty scheme chart, arbitrary base S, and absence of a
representability restriction on f. The identity case reduces to the unchanged
chart hypothesis; no nonemptiness condition occurs. Reopened the unchanged
induction signature and verified that its IsChartwiseEtale occurrences now
have the direct definition-node dependency. All conclusions and the
representable etaleness condition on p are unchanged. The maintainer's
independent statement review remains applicable. No statement correction or
additional postponed theorem is introduced.

Validation of repair: scompile.py compiled the unchanged induction module cleanly
against the published live build. The repair dry run required the current
new-node schema field import_flags; added its empty list and reran validation.
