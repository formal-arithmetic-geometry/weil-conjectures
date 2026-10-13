## What changed

Replaced the single sorry in `AlgebraicGeometry.Scheme.localZeroBottomModel_pullback`
with a compiling reduction through a global bottom truncation arrow. The original
statement, docstring and public imports are unchanged. Added two modules:
`Sheaf.AlgebraicGeometry.LocalZeroBottomTruncation`, fully proved, and
`Sheaf.AlgebraicGeometry.ZeroBottomArrowPullbackLocal`, containing the remaining local
pullback obligation. Added a proved private flat-single computation in the item.

The truncation module computes bottom homology using `HomologyData.ofZeros`, proves
finite local freeness and flatness, checks lower cohomology vanishing on an open cover,
and constructs the single-sheaf arrow by smart truncation. The item fixes this arrow
before checking its pulled-back homology locally, applies the open-cover isomorphism
criterion, and composes the flat-single and homology comparisons. This avoids needing
to glue separately chosen object isomorphisms on overlaps. All three modules compile
with `lcompile.py --all`; no declaration signatures were changed.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.localZeroBottomModel_pullback`
(node `lem-sc-local-zero-bottom-model-pullback`). This is a decomposition, not a complete
axiom-free proof: one lower hole was added, so the net hole reduction is zero.

Fully proved `AlgebraicGeometry.Scheme.localZeroBottomModel_truncation`
(node `lem-sc-local-zero-bottom-truncation`) and the private
`AlgebraicGeometry.Scheme.flat_single_pullback_iso`. Neither contains sorry.

The only sorry left in this delivery is
`AlgebraicGeometry.Scheme.zeroBottomArrow_pullback_local`
(node `lem-sc-zero-bottom-arrow-pullback-local`). It states invertibility locally on
one chart for a specified arrow, rather than the global object-isomorphism conclusion.
Its docstring gives the affine chain-map representation, bottom-component calculation,
counit naturality, and exact restriction/derived-composition argument in full.
The existing dependencies may still have transitive sorries; no new hole was added to
a definition, private helper, or existing dependency module.

## No longer needed

No library module or DAG node is claimed pruned. The second reader removed the redundant
proof import `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` from
`LocalZeroBottomTruncation`; compilation without it succeeds. The item no longer directly imports
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition`,
`Sheaf.AlgebraicGeometry.DerivedOpenPullbackHomology`, or
`Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative`; these remain needed inside
the new local-arrow obligation, which imports them. Their direct proof-dependency
edges were replaced by the two new nodes and the open-cover criterion. The overlap
gluing of independently chosen isomorphisms in the old proof plan is no longer needed:
the proof checks the restriction of one fixed global arrow.

## Where the brief, the DAG or earlier work was wrong

The existing proof plan does not expose a ready-to-apply Lean theorem for the overlap
comparison or the localized-site transport. The new local-arrow node isolates the
termwise pullback/naturality part instead of treating chosen local object isomorphisms
as automatically compatible. The parent statement remains unchanged and is not disputed.
No forced adaptations, interface changes, or changes to targets were needed.

LeanFinder found generic cohomology and flatness results, Loogle found the single
functor and single-homology comparison, and Mathlib grep found the zero-differential
homology data and truncation primitives. LeanSearch returned Internal Server Error
and is recorded as unavailable. Blueprint searches for bottom cohomology, truncation,
and zero differential gave no existing blueprint realization of either new statement.
The unit `sk-prop-av-cube` has empty realized statement/step lists; its route is retained.

Edge cases checked mathematically: a may be negative; finite-free rank zero yields
zero terms; a scheme with no points is covered by the empty point-indexed family.
For the local lemma, y and its membership hypothesis ensure the chart inverse image
contains y; an empty source makes this pointwise condition vacuous. No separatedness,
common rank, reducedness, or global perfection hypothesis is used.

## New nodes

`lem-sc-local-zero-bottom-truncation` records the proved flatness and truncation-arrow
part of the argument, in `LocalZeroBottomTruncation.lean`. Its statement has no pullback
morphism or pullback conclusion. Its proof uses exact open restriction, the existing
finite-locally-free tensor exactness theorem, and Mathlib homology/truncation primitives.

`lem-sc-zero-bottom-arrow-pullback-local` records the remaining specified-arrow
calculation on a single model chart, in `ZeroBottomArrowPullbackLocal.lean`. It needs
no cover of the whole base and concludes only local invertibility on the source.
It uses the already stated flat-complex comparison, derived composition, exact open
restriction, and affine perfect-map representative. The parent performs the actual
cover construction, global isomorphism deduction and flat-single comparison in Lean.

No change records are required: all existing statement signatures and visibility remain
identical, and the new imports in existing code are proof-only imports.

## Second reading by M1

1. Compared the only existing delivered module against its repository version.
   The existing theorem signature is byte-for-byte identical; public imports and
   visibility are unchanged. No definitions or target interfaces are changed.
   Restored the existing theorem's original docstring, which the first worker had
   rewritten. New theorem signatures agree verbatim with their node Lean records.
2. Compiled all three modules with lcompile.py. The only textual sorry is the named
   zeroBottomArrow_pullback_local theorem. Scratch #print axioms checks show only
   propext, Classical.choice, Quot.sound for localZeroBottomModel_truncation and
   flat_single_pullback_iso; the parent and the local lemma additionally use sorryAx.
   There are no forbidden declarations and no definitions in this delivery. The
   flat-single helper chooses F from the pinned tensor-pullback specification;
   its objects and maps are determined, rather than arbitrary existence data.
3. Read the local lemma's statement and complete docstring proof against the zero
   matrix argument in Stacks 0BDL and the chain-representative argument in 08CR.
   Exact restriction identifies M locally with the finite-free bottom term. After
   affine refinement a chain representative has invertible bottom component;
   counit naturality and derived composition preserve this specified arrow's
   bottom isomorphism. Zero ranks, a<0 and empty schemes cause no exception;
   the point hypothesis excludes a nontrivial empty-chart case. This is a genuine
   local step, not the parent's global object-isomorphism statement. Repeated
   LeanFinder, Loogle and grep searches with different queries; no exact existing
   theorem was found. Existing degree-zero chain-model lemmas require additional
   model/site data. Closing the remaining arbitrary-degree transport obligation
   would require a substantial site-transport formalization, not a brief repair.
4. Read the proof from its conclusion back through the cover criterion,
   flat-single computation and truncation construction. Mathlib homology and
   truncation primitives are used directly. Public imports serve signatures;
   proof imports serve the indicated steps. Removed one redundant proof import
   from the truncation module and compiled the scratch variant successfully.
   The report names all former direct proof dependencies: derived composition,
   derived-open homology and affine map representation move to the new local
   node, while def-pc-derived-pullback remains a statement dependency and public
   import. Thus no old dependency module is globally pruned. The unchanged
   sk-prop-av-cube realized fields contain no nodes bypassed by this reduction.
5. Checked each node's proof_deps against the union of proof-step uses (equal),
   each new node's statement and Lean record against its module, and the parent
   node's changes (only proof, proof_deps, proof_origin). Required provenance,
   source, blueprint, chapter/unit and search fields are present. The DAG agrees
   with the fixed-arrow reduction and retains the unit route.

Changes by this reading: restored the original parent docstring; removed the
redundant QuasicoherentKernel proof import; added independent search results to
both new nodes and this review. No theorem statement or proof body changed.
This closes one original hole and adds one strictly local hole: decomposition,
net zero, with the new truncation theorem and private flat-single helper proved
without sorryAx.
