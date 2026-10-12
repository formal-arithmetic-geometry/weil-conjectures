## What changed

The statement and all binders of AlgebraicGeometry.Scheme.affineEtale_descent_data are
unchanged. Its proof now combines finite affine étale diagram descent with eventual
covering, and proves covering transport across source and target isomorphisms directly.
The object clause is the empty-source case of finite diagram descent. Naturality of delta
supplies the comparison equations after moving to the eventual covering stage.

Added AffineEtaleFiniteDiagramDescent and AffineEtaleCoveringEventually. The latter is
proved: finite unions of constructible arrow images, the canonical base-change diagram,
and exists_eventually_range_subset_of_isConstructible replace the coproduct argument.
Pullback cancellation and Scheme.exists_preimage_of_isPullback lift the necessary points.
Its private constructible-base-change helper adapts the already proved local helper in
DescendSurjective, using the original library declarations for the base-change limit.
All three delivered modules compile without warnings. No existing public import was changed. The new modules use only FullAffineEtaleSite
for their public signatures; redundant Category.Cat and Sites.Pullback imports were removed.

## Proved and sorry left

Closed the original hole AlgebraicGeometry.Scheme.affineEtale_descent_data
(lem-weil-pbc-affine-etale-descent-data).

Added and proved AlgebraicGeometry.Scheme.affineEtale_covering_eventually
(lem-weil-pbc-affine-etale-covering-eventually), from the existing named constructible
limit theorem. Its helper constructible_baseChange_eventually is fully proved.
The two covering helpers in the original module are fully proved.

One new hole remains: AlgebraicGeometry.Scheme.affineEtale_finite_diagram_descent
(lem-weil-pbc-affine-etale-finite-diagram-descent). This asserts descent of a finite
star-shaped diagram, with no covering assumption or conclusion. Its docstring records
object descent, eventual affineness and étaleness, common upper bounds, and arrow descent.
It needs only v and its natural pullback projections q, rather than the entire coherent
system or preservation of covers.

This is a decomposition: one original hole closed, one strictly intermediate hole added,
net zero holes. The covering-reflection argument and both directions of covering transport
are now actual Lean proofs; the geometric finite diagram descent remains open. Existing
imported declarations may still depend on sorry; no claim of target axiom closure is made.

## No longer needed

Removed private proof imports from the original module:
Sheaf.AlgebraicGeometry.DescendSurjective,
Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent,
Sheaf.AlgebraicGeometry.FullAffineEtaleSite,
Sheaf.AlgebraicGeometry.LimitAffineTransition, and
WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit.
FullAffineEtaleSite remains available through the unchanged public import of
FullAffineEtaleTopos, and through the new modules. The upstream AffineTransitionLimit
is imported by the proved eventual-cover module because its base-change diagram is used.

The original node's immediate proof dependencies are replaced by the two new nodes and
def-weil-pbc-full-affine-etale-site. The old immediate dependencies no longer used directly are
thm-pd-spreading-out, lem-weil-pbc-scheme-over-limit, lem-weil-pbc-limit-affine-stage,
lem-weil-pbc-descend-etale, lem-weil-pbc-qcqs-morphism-permanence,
lem-weil-pbc-limit-affine-transition, def-pc-fibre-product, lem-weil-pbc-descend-surjective,
lem-weil-pbc-affine-morphism-permanence, and lem-weil-pbc-etale-composition-cancellation.
All except descend-surjective remain in the helper proof plans or actual helper proofs. Spreading out, scheme-over-limit, limit-affine-stage,
descend-etale, qcqs permanence and limit-affine-transition remain in the finite-diagram
proof plan, so they are not mathematically pruned.

lem-weil-pbc-descend-surjective and its module are unnecessary on this route: the finite
union of constructible images replaces surjectivity descent of a coproduct. The finite
coproduct step and its affineness instance are unnecessary. Affine permanence,
etale composition cancellation, fibre products, Chevalley, base-change point lifting,
and limit-contained-in-constructible remain needed by the new proved covering argument.
No assertion is made that a removed direct import is globally unreachable: public imports
and other targets may still reach it.

## Where the brief, the DAG or earlier work was wrong

No false statement was found and no target or existing statement was changed. The planned
coproduct step is replaceable below the unit level by the same constructible-image argument
underlying 07RR. The unit sk-thm-p1 route and its realized nodes are unchanged.

The original gamma, h7 and h10 hypotheses are stronger than this proof uses; they remain
in its signature exactly as supplied, and are explicitly acknowledged in its proof to
avoid unused-variable warnings. The finite-diagram helper does not need U, p, gamma,
delta or cover preservation. The eventual-cover helper does not need gamma, delta or
cover preservation. This avoids hiding the original theorem inside a repackaged hypothesis.

LeanFinder and source grep found the existing geometric tools but no direct chosen-functor
result. Loogle does not know the project-local FullAffineEtale identifier. LeanSearch
returned Internal Server Error; the unavailable search is recorded without an absence
verdict. The repository's literature source files are absent on this machine, so the
Stacks proofs 0EYL, 07RR and 01ZM were read online. Existing proofs and the pinned Mathlib
sources were read locally. The finite-diagram statement was checked for empty sources,
empty schemes, a constant diagram, and arbitrary choices of pullback functors.

## New nodes

lem-weil-pbc-affine-etale-finite-diagram-descent: the unproved descent of target, finitely
many sources and arrows, without any assertion about a covering. Module
Sheaf.AlgebraicGeometry.AffineEtaleFiniteDiagramDescent.

lem-weil-pbc-affine-etale-covering-eventually: proved eventual joint surjectivity of an
already staged finite family, using constructible images and point lifting. Module
Sheaf.AlgebraicGeometry.AffineEtaleCoveringEventually. Its node follows the actual
constructible-image proof, rather than the abandoned coproduct route. No change records
are required: existing statements and public imports are unchanged.

## Second reading by H1

1. I compared the delivered `AffineEtaleDescentData` module with the repository version.
All existing declaration signatures are unchanged byte-for-byte. The changes are proofs,
proof-only imports, and the two explicitly recorded new modules and nodes.

2. I compiled all three delivered modules with `lcompile.py --all`; each compiled without
errors or warnings. Scratch copies with `#print axioms` for every theorem (including private
helpers) show only propext, Classical.choice, Quot.sound and sorryAx. The two original-module
covering helpers have no sorryAx; the eventual-cover proof inherits sorryAx from the existing
limit-contained-in-constructible dependency. Static inspection found no forbidden declarations. The sole remaining
`sorry` is the named, documented split theorem
`affineEtale_finite_diagram_descent`.

3. I checked the two split-off statements against their DAG nodes and searched the local
library and Mathlib for duplicates. The eventual-cover theorem is proved. The
finite-diagram theorem is strictly simpler than the original target because it has no
covering hypothesis or conclusion. Both nodes contain sources, proof plans, and Lean
metadata matching the files.

4. I verified that the unit route is preserved: finite diagram descent is used first,
then eventual covering, then transport of covering families. The removed imports and
pruned dependencies are listed above, and the main node's proof dependencies match the
actual declarations used by the proof.

5. I checked edge cases including `n = 0`, empty schemes, identity comparisons, and the
pointwise covering transport equations. The empty-family case is handled by the same
joint-surjectivity argument, and no target statement or definition was changed.

The second reading changed this report: added the review and axiom audit and clarified the
complete immediate-dependency pruning list; no Lean code or DAG statement needed repair.
