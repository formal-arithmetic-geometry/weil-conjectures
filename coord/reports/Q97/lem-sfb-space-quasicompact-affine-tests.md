## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests` states the full node
in four named theorems, all with `sorry` proofs. It defines no new notions. Its public
namespace is `AlgebraicGeometry.AlgebraicSpace`. The accepted stage-1 statement and proof
are unchanged. The inherited BLOCKED ending referred to a stage-1 unchanged-item gate;
coord/brief-stage2.md §0 explicitly authorizes this stage-2 handoff. The current item had
no Lean record and is listed at stage 2 in coord/queue.tsv.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`, with explicit `universe u`; algebraic spaces
  `X Y : AlgebraicSpace S` and `f : X ⟶ Y` use the recorded sheaf/full-subcategory model.
  All scheme tests and atlas schemes are `Over S` in the same scheme universe. No
  separation, representability, nonemptiness or finiteness assumption is added.
- A quasi-compact space has a quasi-compact scheme atlas: the first conclusion contains
  `∃ (U : Over S) (a : yoneda.obj U ⟶ Limits.pullback f.hom.hom h),
  CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a`. The source of `a` is the represented
  scheme and its target is exactly the presheaf fibre product. Thus no new topological
  substitute for the atlas definition is introduced.
- The node defines quasi-compactness by *every quasi-compact scheme* test. The first
  theorem explicitly quantifies `∀ (T : Over S), CompactSpace T.left →
  ∀ h : yoneda.obj T ⟶ Y.obj.obj` followed by precisely that atlas condition.
- Its affine-test equivalent is the already existing `IsQuasiCompactPresheafMap
  f.hom.hom`, not a new definition. Reading that definition shows that it quantifies all
  affine `Z`, all test maps, and compatible `p,q`, and requires the induced map to the
  actual pullback to be étale and surjective with quasi-compact scheme source.
  Pullback universality identifies those pairs with the atlas maps in the first theorem.
- The open-cover clause is `quasiCompact_iff_exists_open_subspace_cover`: an index
  `I : Type (u + 1)`, existing `OpenSubspace Y` members, and existing
  `IsJointlySurjective (fun i ↦ (U i).val.ι)`. The latter is surjectivity on field-valued
  point classes, not surjectivity on sections over every scheme. Each restriction is
  `Limits.pullback.snd f.hom.hom (U i).val.ι` and has the same quasi-compact predicate.
  OpenSubspace means a literal subfunctor with representable open-immersion inclusion;
  it is automatically an algebraic space. The bound u+1 allows the entire set of open
  subspaces and does not require a finite or nonempty covering index.
- `quasiCompact_presheafMap_baseChange` quantifies arbitrary `Y' : AlgebraicSpace S`
  and arbitrary `g : Y' ⟶ Y`; its only premise is quasi-compactness of `f`. The result
  is quasi-compactness of the actual second projection of the presheaf pullback.
- `quasiCompact_iff_representableWith_quasiCompact` has exactly the additional premise
  `IsRepresentable f.hom.hom` and identifies quasi-compactness with
  `IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left) f.hom.hom`.
  Reading IsRepresentableWith shows that this tests every scheme and every map to Y,
  supplying a representing pullback square and its quasi-compact scheme projection.
  Uniqueness of representing objects and isomorphism invariance mean this says the
  scheme condition for every base change, rather than selecting a weaker property.
  Mathlib's scheme QuasiCompact is equivalent to the affine-open inverse-image criterion
  (`quasiCompact_iff_forall_isAffineOpen`).

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  including their locally ringed space construction and scheme morphism signatures.
- `def-weil-size-convention`: metatheoretic convention with no module/declaration;
  implemented by the explicit universe and tests within Scheme.{u}.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsRepresentable`, `IsEtale`, `IsSurjective`. All signatures
  and docstrings were read; the predicates concern real representing scheme squares.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`.
  These identify sheaf pullbacks with algebraic-space pullbacks; their full signatures
  and proof docstrings were read.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`; on `T.left` this is precisely the
  quasi-compact scheme notion without Hausdorff assumptions.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`: `IsQuasiCompactPresheafMap`.
  Its existing definition is now owned by the new definition node
  `def-sfb-space-quasi-compact-presheaf-map`, cited in stmt_deps. The theorem node
  `lem-trf-space-qc-separated-etale-local` is not a statement dependency.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`; its recorded
  node `def-a1-space-open-subspace` is added to stmt_deps to cite the existing notion.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity` is imported directly for
  `IsJointlySurjective`; its owning definition node
  `def-trf-algebraic-space-jointly-surjective-family` is cited in stmt_deps. Its entire
  signature and field-extension interpretation were read.
- Proof imports retain the recorded Mathlib affine/quasi-separated, étale, finite-type
  and scheme quasi-compactness results, and the recorded algebraic-space étale-image
  and point-topology modules. Two proof-only nodes have no recorded module locally:
  `lem-trf-space-finite-qc-atlas-assembly` and `lem-a1-space-point-open-calculus`.
  They are cited in the proof docstrings; they supply no object needed to type these
  statements and their nonexistent modules cannot be imported.

Edge cases checked before writing: empty schemes and empty spaces use the empty atlas;
empty open covering indices are permitted and force the target empty. The identity of
an infinite disjoint union is quasi-compact although its whole source is not; the
statements test relative pullbacks and do not assert compactness of X. Conversely an
infinite disjoint union of points mapping to a point fails the affine test. Arbitrary
nonrepresentable f and arbitrary g are allowed in the base-change theorem. The
representable theorem tests arbitrary, possibly nonaffine or nonseparated T. No
quasi-compactness or affineness of intersections of affine opens is assumed.

Searches performed on 2026-10-23:

- msearch leanfinder: "A morphism of algebraic spaces is quasi compact if and only if
  every affine scheme base change is quasi compact; Zariski local and stable under base
  change". Eight hits, all scheme results: quasiCompact_isStableUnderBaseChange,
  quasiCompact_iff_forall_affine, quasiCompact_over_affine_iff, multiplicativity,
  quasiCompact_iff_forall_isAffineOpen, QuasiCompact, affine-hom instance, postcomposition.
  None states the algebraic-space theorem.
- msearch loogle: `"QuasiCompact", "IsStableUnderBaseChange"`. One hit:
  AlgebraicGeometry.quasiCompact_isStableUnderBaseChange, for schemes only.
- msearch leansearch: "Quasi compactness of morphisms of algebraic spaces is local
  for open covers of the target". Eight hits: scheme QuasiCompactCover instance,
  IsLocalAtTarget.of_openCover, quasiCompact_iff_compactSpace, both
  IsZariskiLocalAtTarget open-cover lemmas, QuasiCompact, QuasiCompact.mk,
  Scheme.Hom.isCompact_preimage. None is the algebraic-space assertion.
- msearch grep: `AlgebraicSpace|quasiCompact_iff_forall_affine|
  quasiCompact_isStableUnderBaseChange`, AlgebraicGeometry/Morphisms. One reported hit:
  Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean:165, scheme base-change stability.
- rg of the live WeilConjectures and Sheaf trees for the item id and quasiCompact
  affine/Zariski names found scheme lemmas and no existing full statement. Searches
  for QuasiCompact presheaf/space definitions found the reused IsQuasiCompactPresheafMap
  and ProperCurveModuli.MapIsQuasiCompact (the latter uses point-topological compactness).
  OpenSubspace and joint-surjectivity sources were searched and read. DAG records and
  upstream declaration-name index were checked; the item has no upstream declaration.

Source checked directly: literature/stacks-project/spaces-morphisms.tex,
lemma-characterize-representable-quasi-compact (03HD),
lemma-base-change-quasi-compact (03HF), lemma-quasi-compact-local (03KG), including
all six conditions and its finite affine-refinement argument. No statement fault found.
The repair adds the definition node described below with an existing:true record.
Every proof is postponed; no definitions use sorry.

Validation: scompile.py compiled this file separately in sandbox and library mode,
with no errors or warnings (6.7 s and 10.5 s). Dry-run and delivery results follow below.

## Second reading by Q97

Re-read the completed module against the full node and each recorded dependency, in
this worker session; the dispatcher expressly forbids starting another agent. The
maintainer supplies the independent review. Verified the four theorem signatures in
order: qc scheme tests with explicit atlas, affine predicate; open-subfunctor covering
with pointwise joint surjectivity; arbitrary algebraic-space base change; representable
scheme tests. The first equivalence is needed because the reused predicate is affine
rather than the node's all-quasi-compact-schemes definition. It is included explicitly,
so no implication of the node is silently assumed. The cover index has u+1, the size of
all open subspaces, and permits emptiness. IsRepresentableWith supplies all representing
scheme tests and its property is isomorphism invariant. All variables/universes are
explicitly bound, and autoImplicit is false. Each proof docstring includes the relevant
steps of the four accepted proof paragraphs. The item changes only lean and stmt_deps: the added dependencies name the
quasi-compactness predicate, open subspaces, and joint surjectivity. The theorem
dependency previously added just for a definition has been removed. No correction to the accepted statement
or proof was needed. No mismatch found in this second pass.

## New nodes

`def-sfb-space-quasi-compact-presheaf-map` records the existing declaration
`AlgebraicGeometry.AlgebraicSpace.IsQuasiCompactPresheafMap` in
`Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`, with `existing: true` and no new
Lean module. Its statement expands every binder: schemes and presheaves over S; all
affine tests Z and maps h; U, p, q and their compatibility; compactness of U; and
etaleness and surjectivity of the pullback lift. These are exactly the definition's
quantifiers and conjunctions. The compatible pair gives precisely an atlas of the
presheaf pullback by its universal property. Sources: Stacks 03E3 for the atlas
condition, 03HE and 03KG(3) for the affine-test predicate on space morphisms.
LeanSearch returned eight scheme-only results, Loogle twelve scheme-only results,
and Mathlib grep no hits. Project grep found the defining declaration and its
consumers but no owning definition node; blueprint_refs search found zero matches
and the ancestor command returned None. The raw search records are retained in
mathlib_searches. The def-sfb prefix and sec-six-functors-basics location follow
the item's chapter, as required by brief-stage2 section 5.

## Repair of independent return L (fb3e6e9ab270)

H2 is repaired: the item cites the new definition node for the plain predicate,
rather than the etale-local theorem. It also explicitly cites
`def-trf-algebraic-space-jointly-surjective-family` and publicly imports
`Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity` directly. The existing
quasi-compactness definition remains imported from its original module;
no theorem conclusion, choice or assumed proof is needed to state the item.
The four theorem signatures, their docstrings and sorry proofs are unchanged.
Compared the saved packet with current main: all fields besides lean and the
authorized stmt_deps additions match main verbatim. The repair modifies the
saved packet identified by the returned immutable head.

Second reading of the repair by Q97: read the new node against the actual complete
definition, including its inherited explicit S binder and universe u. The node
uses the same presheaf universe and affine tests, does not assume representability
of g, and does not require sections to lift globally. Empty U and empty affine Z
are permitted. On algebraic spaces, its interpretation is the affine criterion
03KG(3). Read the joint-surjectivity definition directly: its field-extension
condition covers the same open covering clause as before. The explicit import
changes no theorem signature. No mathematical statement correction is needed.

Repair validation: scompile.py compiled the repaired module cleanly in sandbox
mode (8.3 s) and library mode (7.8 s), without errors or warnings. The packet
self-check verified exact signature text, definition-node citation coverage,
four postponed proofs, and Lean line width.

Dry-run preflight required the current schema key `import_flags`; added the
empty list to the new definition node and repeated validation.
