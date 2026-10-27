## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteTypeStackAffineSmoothAtlas` states
`CategoryTheory.finiteType_stack_affine_smooth_atlas`, with its proof postponed by
one `sorry`. No Lean definition is introduced or repaired; a new definition node
registers the existing `IsOpenModuliCover` predicate, without copying it. The natural-language
five-step proof in its docstring follows the node's proof verbatim in substance.

Sources read: Stacks `stacks-properties.tex`, Tag 04YC,
`lemma-quasi-compact-stack` (lines 1171–1216), including the finite affine
subcover argument; `stacks-morphisms.tex`, Tag 06FS,
`definition-locally-finite-type` (3261ff), and Tag 075U,
`definition-smooth` (7380ff). These sources are present locally.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`. `F` is a category over
  `Over (Spec (.of k))`, with independent hom and object universes `v`, `w`.
- `hF : IsAlgebraicModuliStack F` is exactly the étale stack condition,
  algebraic-space diagonal, and existence of a representable smooth surjective
  scheme atlas. It uses the recorded fibred-groupoid and 2-fibre-product notions,
  not isomorphism classes or an arbitrary set-valued replacement.
- Local finite type tested on smooth atlases is `hlft`: every `U` and every
  `a : BasedFunctor (discreteModuli (yoneda.obj U)) F` satisfying
  `IsSmoothModuliAtlas F U a` has `LocallyOfFiniteType U.hom`.
  This uses smooth atlases, not étale atlases (which would omit non-DM stacks).
- Quasi-compactness by open-substack covers is `hqc`. `C` is a set of the
  existing `OpenModuliSubstack F`, whose full subcategory is pullback-stable and
  whose scheme inverse images are open subschemes. `IsOpenModuliCover` means
  pointwise covering on every scheme inverse image. `D.Finite`, `D ⊆ C`, and
  the same covering condition express precisely a finite subcover.
  Indexing by a set of substacks loses no covers: repetitions have no effect,
  and every family has its image set. This avoids a restriction on the universe
  of an arbitrary cover index. This is not a test that every family lies wholly
  in one member of the cover; that incorrect test would miss families meeting
  several open charts.
- The conclusion's `A : Over (Spec (.of k))` is the requested scheme over k,
  and `a` is its actual map to the same stack. `IsAffine A.left` is affineness.
- `LocallyOfFiniteType A.hom ∧ QuasiCompact A.hom` is exactly finite type in
  the dependency's recorded scheme convention (there is no new bundled notion).
- `IsSmoothModuliAtlas F A a` combines representability, smoothness and
  surjectivity after every scheme base change, using actual algebraic-space
  projections, with smoothness on étale scheme charts. There is no additional
  representability hypothesis on F beyond its diagonal.
- `(IsSmoothModuliStack F → Smooth A.hom)` applies to this same chosen atlas,
  not to a separate existence witness. The existing predicate tests smoothness
  using existence of a smooth atlas with smooth structural composite, equivalent
  to the smooth-atlas test of the node (Stacks 075U).
- Neither the hypotheses nor the conclusion require a nonempty stack or scheme.
  There is no perfectness, characteristic, separatedness or DM hypothesis.

Dependency declarations used, with full definitions/signatures and docstrings read:

- `Mathlib.Algebra.Field.Defs`: `Field` (inherited by the scheme imports).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, with its
  locally ringed space and local affine charts, and scheme morphisms.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `discreteModuli`, `BasedFunctor` conventions, `IsModuliStack`,
  `HasAlgebraicSpaceDiagonal`, `HasSpaceBaseChange`,
  `IsRepresentableByAlgebraicSpaces`, `SpaceMapIsSurjective`,
  `moduliTwoFiberProduct`, `ModuliTwoIso`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`:
  `AlgebraicGeometry.AlgebraicSpace`, its fppf sheaf, representable diagonal
  and étale atlas; scheme test maps and representability predicates.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `IsAlgebraicModuliStack`, `IsSmoothModuliAtlas`, `IsSmoothModuliStack`,
  `SpaceMapIsSmooth`. Its owning landed node
  `def-sfb-algebraic-moduli-stack` is added to `stmt_deps`.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`: `OpenModuliSubstack`;
  its owning landed node `def-sfb-open-moduli-substack` is added to `stmt_deps`.
- `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`:
  `IsOpenModuliCover`. The new `existing: true` definition node
  `def-sfb-open-moduli-cover` records this unchanged plain definition and is
  added to `stmt_deps`. The calculus theorem remains in `proof_deps` only.
  Its module is public because the covering predicate occurs in the signature.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffine`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
  The node's old name `IsSmooth` is deprecated; the current recorded dependency
  uses `Smooth` and is followed.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact`.
- Scheme coproduct and fibre-product declarations from the recorded Mathlib
  matches were read for the proof plan. The unused private imports
  `Mathlib.AlgebraicGeometry.Limits` and
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` have been removed
  in response to H9; no signature declaration relies on these direct imports.

The proof dependency `lem-sfb-smooth-atlas-open-image` has no Lean record,
Mathlib match or closed upstream declaration. Its module is therefore not
imported; it is used only in the documented future proof, not to type the
statement. No missing statement prerequisite or helper remains.

Edge cases checked before writing: empty stack and Spec of the zero ring
(the empty open cover is permitted since scheme-test covering is pointwise);
empty and singleton finite affine families; overlapping open images; schemes
viewed as stacks; general algebraic stacks such as BG_m, for which étale scheme
atlases are unavailable; arbitrary and imperfect fields and positive
characteristic; a nonsmooth finite-type stack (the conditional smoothness clause
is then vacuous). Finite-type source need not be proper or separated over k.
Independent stack universes are retained; no extra smallness equality is assumed.

Searches actually run through msearch.py for this item:

- LeanFinder: `An algebraic stack of finite type over a field admits an affine
  finite type smooth surjective atlas` — 8 hits: scheme affine-surjection and
  affine-space/finite morphism results, none the stack statement.
- Loogle: `AlgebraicGeometry.Scheme, AlgebraicGeometry.IsAffine` — 12 hits:
  affine scheme definitions and properties, reused for `IsAffine`; no theorem
  about stack atlases.
- Mathlib grep: `AlgebraicStack|SmoothAtlas|affine.*atlas|atlas.*affine` — 0 hits.
- LeanSearch: `A finite type algebraic stack over a field has a smooth
  surjective atlas from an affine scheme of finite type` — 8 hits, on scheme
  smoothness and finite presentation, none the stack statement.
- Local rg of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id, affine/smooth atlas phrases,
  `IsAlgebraicModuliStack`, `IsOpenModuliCover`, and the finite-type/smooth
  stack predicates. No upstream theorem matches. The landed
  `algebraic_stack_quasicompact_surjection` supplies an affine atlas without
  finite-type or conditional smoothness conclusions, so is not the item.
  Existing definitions were reused. The repair registers the existing open-cover
  predicate in its own definition node, as requested by the maintainer.

No statement correction or disputed mathematical assertion was identified.
The original item is changed only in `lean` and `stmt_deps`: two added landed
definition nodes and the new existing-declaration definition node. The theorem
`lem-sfb-stack-chartwise-smooth-etale-calculus` stays in `proof_deps`, not
`stmt_deps`. The natural-language statement and proof are unchanged.

## Second reading by Q09

This is a second pass by the same worker; no independent reader was started,
as the dispatch brief prohibits other agents and assigns independent review to
the maintainer. Reopened the completed module and the node and checked all
hypotheses and clauses against the correspondence above. In particular hqc
uses points of every scheme inverse image, not global object membership in
one open; hlft quantifies over smooth atlases, not the DM-only finite-type-map
API; the finite-type conclusion contains both local finite type and
quasi-compactness; the atlas predicate includes representability and
surjectivity; the conditional smoothness conclusion is inside the same
existential. No new definitions, data choices, universe equalities or extra
hypotheses were added. No mismatch was found in this second pass.

## Validation

The first standalone scompile.py invocation timed out on both compiler paths.
The prescribed deliver2.py --no-push then completed successfully, printing
`OK (dry run): commit f4611c114a1 passes the preflight and compiles; nothing pushed`.
No timeout limit was raised and no live source or tool was modified.
The final signature matches lean.statement verbatim; every Lean line is at most
100 characters.

## New nodes

`def-sfb-open-moduli-cover` registers the existing plain definition
`CategoryTheory.IsOpenModuliCover` in
`Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`, at line 86.
Its `lean.existing` is true and there is no new module, copy, choice, or theorem
interface. Its statement spells out the actual definition: for every scheme
`T`, map `t:h_T → F`, and point `x:T`, choose an index `i`, an open immersion
`j:W → T`, an equivalence representing the inverse image of this particular
full open substack over `T`, and `w:W` mapping to `x`. The independent index,
object and morphism universes in the existing signature are preserved. Sources:
Stacks 04YM (open substacks) and 04YC (open-cover finite-subcover argument).

Searches rerun for this new node: LeanSearch query `An open family of substacks
covers if its inverse images cover every scheme test` returned eight scheme
covering results, including Scheme.OpenCover; LeanFinder query `Covering family
of open substacks of a fibred groupoid tested by scheme pullbacks` returned
eight scheme cover/precoverage results. Neither defines stack covers. Mathlib
grep `IsOpenModuliCover|OpenModuliSubstack|open.*substack.*cover` returned zero
hits. Local project search finds this existing definition in the calculus
module and none in WeilConjectures. Definition-node search finds only the
unrelated space-cover descent-category node; the existing open-substack node
owns individual substacks, not covers. `tools/blueprint_refs.py search
'open substack cover'` returned zero matches; `ancestor` returned None, which is
recorded in the new node's `blueprint.from.node`. All actual search outputs are
recorded in its `mathlib_searches`; the first three queries are in the search log.

Edge cases for the registered notion: an empty index can cover only when all
scheme tests have empty underlying space; an empty scheme test is vacuous;
a singleton whole-substack cover covers; a family meeting several opens is
tested pointwise, so it need not factor globally through one member.

## Repair of returned head 0623bfc7902d

H2: replaced `lem-sfb-stack-chartwise-smooth-etale-calculus` in `stmt_deps` by
`def-sfb-open-moduli-cover`. The new node is `existing: true` on the unchanged
plain definition, rather than a second definition or a theorem-dependent choice.
The calculus theorem is retained in `proof_deps`. The current main item still
has no Lean attachment, and the retained sandbox differs from it only in the
allowed `stmt_deps` and `lean` fields. The delivery tool rebases the repaired
files on current main through its authorized worktree bookkeeping.

H9: removed exactly the two unused private import lines named in the return.
The Lean theorem signature and its proof docstring are unchanged.

Second repair reading by Q09: opened the new node and the existing definition
and checked each quantifier and witness (T, t, x, i, W, j, representing
equivalence, compatibility with the first projection, w and j(w)=x). Confirmed
the new node cites only definition nodes and makes no algebraicity, finite-type
or nonemptiness assumption. Confirmed the consumer's recorded signature is
still verbatim and its sole proof is sorry. The maintainer's independent return
already validated the substantive statement against 04YC/06FS/075U; this repair
changes its DAG ownership record and removes unused imports only.

Repair validation: scompile.py compiled the repaired module cleanly in both
sandbox and library mode (3.9 s and 14.0 s). Only the expected postponed theorem
is present. The item changes only lean and stmt_deps against current main;
proof_deps is identical, the recorded signature is exact, and no Lean line
exceeds 100 characters.
