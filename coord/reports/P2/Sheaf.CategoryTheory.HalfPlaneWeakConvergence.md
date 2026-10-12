## What changed

Repair of the landing refusal at cac60b104: all three duplicate private
statements have been replaced by genuine generalizations in the owned module.
`page_zero` now assumes only `IsZero (X.E p q)` at one bidegree, with no
half-plane or global support hypothesis. `tower_stationary` now takes an
arbitrary `CycleBoundaryTower X`, rather than only `X.cycleBoundaryTower`.
`pullback_bot_kernel` is replaced by `pullback_kernel`, proving
`pullback f (kernelSubobject g) = kernelSubobject (f ≫ g)` for arbitrary
composable morphisms in categories with zero morphisms, kernels and pullbacks. The bottom formula follows locally by specializing g
to the identity. Both callers use the generalized helpers. All three are
private and fully proved, with no new public signature or additional sorry.
The existing DAG proof step and proof origin record these generalizations.


Replaced the sorry in `CategoryTheory.BigradedExactCouple.halfPlane_weak_convergence`
with a compiled reduction, preserving its full signature and visibility.
Added `Sheaf.CategoryTheory.FinitePageImageQuotient`, stating just the finite-page
successive-image quotient and its canonical projection equation. Updated both DAG
records to match the argument.

The original module now proves the graded map is epi directly, handles both
vanishing regions, proves negative diagonal maps and normalized cocone maps invertible,
proves differential and cycle/boundary stationarity, identifies the given GLB/LUB
with the stationary subobjects, proves the following derived D term is zero using
`pageCouple_image`, constructs the infinite-page/finite-page cokernel isomorphism,
and derives the two epimorphisms and equality of kernels by composing comparisons.
All local helpers are private and fully proved. The remaining finite lemma does
not mention the infinite page, limiting subobjects, weak convergence, or a global
lower D bound. It assumes a single following finite D term is zero; the caller
proves this hypothesis. Its proof in words includes the image-epimorphism induction
and the derived-g/tower-projection compatibility induction.

Both delivered files compile cleanly with lcompile.py. No definitions, existing
statements, universes, or public imports changed. No forced adaptations.

## Proved and sorry left

Closed: `CategoryTheory.BigradedExactCouple.halfPlane_weak_convergence`
(node `lem-sp-half-plane-weak-convergence`), 1 of 1 original holes.
Its module contains no remaining sorry.

Added: `CategoryTheory.BigradedExactCouple.finitePage_image_quotient`
(node `lem-sp-finite-page-image-quotient`), exactly one public named theorem whose
entire proof is sorry, in its own new module.

This is a decomposition, not an axiom-free proof: 1 upper hole closed and 1 lower
hole added, net zero new-hole reduction. The existing `pageCouple_image` is used
from `Sheaf.CategoryTheory.DerivedCoupleExact`; its existing sorry is not changed
or copied. The finite lemma is strictly one step of the argument; the stabilization,
GLB/LUB identification, vanishing cases and cokernel assembly are actual Lean proofs.

## No longer needed

Removed the redundant direct proof imports `Sheaf.CategoryTheory.ExactCouple`
and `Sheaf.CategoryTheory.Filtration`. Both remain available through the unchanged
public import of `Sheaf.CategoryTheory.ExactCoupleConvergence`. Their definitions
and DAG nodes remain needed; no module becomes unreachable from this delivery.
`Sheaf.CategoryTheory.DerivedCoupleExact` remains needed for `pageCouple_image`.
The separate large theorem `derived_couple_exact` is not applied by the delivered
proof; it shares a module and node with the needed image theorem, so its module
cannot be pruned here. No other node or module has been pruned. The second reader also removed the
unused proof-only import `Sheaf.CategoryTheory.DerivedCoupleExact` from the new
`FinitePageImageQuotient` module: the statement does not use its declarations.
Its node retains that dependency for the documented future proof; the main
module still imports and applies `pageCouple_image`.

## Where the brief, the DAG or earlier work was wrong

The returned delivery repeated three private helpers word for word from
`HalfPlaneConvergence`. That module imports this item, so importing it back
would create a cycle; its private helpers are also unavailable to importers.
The repair takes the return's permitted generalization route, with strictly
more general mathematical statements, rather than merely changing names or
binder spelling. The earlier second reading below predates this repair and
did not catch the duplicate-helper check.


No statement error found. The original node compressed the entire finite-image
quotient and canonical-g compatibility into one prose paragraph; its existing
`pageCouple_image` dependency gives the iterated D image data but not the finite
page/graded quotient comparison. That missing finite step is isolated as the new
node instead of leaving an anonymous hole inside the theorem.

`HalfPlaneConvergence`, `HalfPlaneSharpBounds`, and `HalfPlaneGradedCanonical`
are downstream of this item and cannot supply a shorter proof without a cycle.
The unit record `sk-prop-av-pqf-finite` was read and its route was preserved.
The already-listed derived-couple node is an off-unit generic tool, retained in
exactly the same role as the original plan.

The offline literature directory contains lists but not the blueprint text.
WANTED: the original blueprint `thm-sp-half-plane-convergence`, proof paragraph 2,
for `lem-sp-finite-page-image-quotient`. The existing node/docstring proof was read;
the Stacks sources were read online at Tags 011R, 011T, 0AMJ and 012F.
[011R](https://stacks.math.columbia.edu/tag/011R),
[011T](https://stacks.math.columbia.edu/tag/011T), and
[0AMJ](https://stacks.math.columbia.edu/tag/0AMJ) describe the exact-couple recursion
and derived-g construction; their omitted proofs are expanded in the new node.
[012F](https://stacks.math.columbia.edu/tag/012F) concerns filtered differential
objects, so it is not used as a standalone finite exact-couple quotient theorem.
The new proof is marked agent-written, retaining the blueprint paragraph as source.

## New nodes

`lem-sp-finite-page-image-quotient`: `Sheaf.CategoryTheory.FinitePageImageQuotient`,
`CategoryTheory.BigradedExactCouple.finitePage_image_quotient`. It supplies the
finite-page/image-filtration comparison with its prescribed projection equation.
The hypothesis that the next finite D term is zero replaces any global lower bound;
the caller verifies it independently. Checks: r=0 gives the original exact-couple
cokernel when its following D term vanishes; p<0 gives zero E and equal top image
steps; a zero couple gives two zero quotients. No positivity of q or existence of
extra infinite limits is assumed. Every use of a chosen map is determined by an
epi projection equation or mono inclusion equation, and no data is defined here.

Searches were run through msearch.py and are recorded in searches.jsonl. LeanSearch
returned Internal Server Error (recorded unavailable). LeanFinder returned exact
short-complex cokernel/colimit lemmas, not the finite derived-couple comparison;
Mathlib grep for `ExactCouple|exact couple` returned no hits. Blueprint searches
for half-plane, consecutive images, and derived couple found no independent
statement of this finite step. The existing canonical-image-filtration lemma
concerns a different spectral-object/Grothendieck functor construction.
The second reader also inspected `CategoryTheory.finitePage_image_lift` and
`CategoryTheory.finitePage_graded_quotient` in the current library. The former is
proved and identifies a specified incoming-alpha filtration step with a derived D
term. The latter remains sorry and compares its graded quotient to the finite E
term through derived g. Their hypotheses fix a global D lower bound, p>=0, a
particular max-based page, a filtration expressed by incoming iterates, and an
explicit lift. Neither provides the original-g/tower-projection equation needed
here. The new statement instead uses an arbitrary finite r, the actual colimit
image filtration, local vanishing of the following D term, and that equation.
It is not a duplicate of either declaration. `AbutmentFinitePageComparison`
combines those results with `HalfPlaneSharpBounds`, which imports
`HalfPlaneConvergence`, which uses this item; importing that assembly would cycle.
No change record is needed: no existing interface changed.


## Earlier second reading (a previous round; superseded)

1. **Visible interfaces: pass.** Compared the delivered main module with the
   repository using diff. The existing theorem signature, universes, variables,
   visibility, definitions and public import are byte-for-byte unchanged. Only
   private proved helpers, the theorem body and proof-only imports differ. The
   second module is new and has its own matching node; no forced adaptations or
   interface change records are required.
2. **Kernel-checked proof: pass as a decomposition.** Both modules compile through
   lcompile.py in import order, including after the import repair. The main module
   has no sorry. The sole added sorry is the complete body of the public named
   finitePage_image_quotient theorem. No axiom, unsafe, opaque, implemented_by,
   extern or holed definition occurs. A scratch copy with #print axioms for both
   public theorems reports only propext, Classical.choice, Quot.sound and sorryAx.
   The latter is expected: this reduction uses the new finite lemma and the
   existing pageCouple_image. It is not claimed as an axiom-free proof.
3. **Split-off statement: pass.** Read the whole finite-page theorem, its complete
   docstring argument, its DAG node, and the actual derivedD/DerivedMaps and
   cycle-tower recurrences. At r=0, p<=0, exactness gives the original g cokernel
   when D(p+2,q-1)=0; the cocone equation identifies its kernel with the next
   image. For p<0 both consecutive images are top and the E term is zero, so both
   sides vanish. For p=r the anchoring index u is zero: the normalization suffices,
   and the next image is computed by alpha_r from u+1, without assuming its
   cocone map invertible. The zero couple also satisfies the statement. The
   projection equation follows from the specified g_comm and projection_succ
   recurrences, not from an arbitrary choice of isomorphism. No data is chosen
   from mere existence in this delivery. This is a strictly finite quotient and
   compatibility step; it contains neither limits nor weak convergence nor the
   global D bound. Independently searched with LeanFinder, Loogle and Mathlib
   grep using different terms, and searched both library roots. The generic
   cokernel results do not supply the iterated-image and original-g compatibility
   calculation. The nearby finitePage_image_lift and finitePage_graded_quotient
   were inspected and compared explicitly above. Completing that induction is
   not a short routine closure; its named hole is retained.
4. **Top-down reduction and pruning: pass.** Read all private helpers and the main
   proof: support vanishing, invertible left cocone maps, finite differential
   stationarity, GLB/LUB identification, finite D vanishing and explicit cokernel
   assembly are proved before invoking the finite comparison. The comparison
   equation then gives both epimorphicity and equality of kernels. The main
   import of DerivedCoupleExact is necessary for pageCouple_image; its two
   redundant direct imports are correctly listed as removed, without claiming
   their nodes or modules pruned. Removed one unused proof import in the new
   module. Read dag/units/sk-prop-av-pqf-finite.json: this imported unit has empty
   realized statement/step lists, and no realized route node is bypassed here.
   No old proof_deps node has been removed; none is missing from the report.
5. **DAG agreement: pass.** Diffed the existing node: only proof, proof_deps and
   proof_origin change, as permitted. Its four steps match the Lean reduction
   and the union of their uses equals proof_deps. The new node has a self-contained
   statement, statement dependencies, source, agent proof origin, all search
   records, split status, creator/item/group/date, blueprint ancestry, chapter,
   unit and a Lean record whose statement matches its theorem signature. Its
   proof records the remaining image induction and canonical projection induction.
   Added the second reader's independent search evidence to this new node.

Second reading changed: removed the unused DerivedCoupleExact proof import from
FinitePageImageQuotient; corrected the report's omission of the existing related
finite-page lemmas; added independent search evidence and this review. No proof
body or statement needed repair. Closed 1 original hole, added 1 strictly smaller
hole, net 0: decomposition, with no module pruned.


## Second reading by P2

1. **Interfaces: pass.** Diffed both delivered modules against the repository.
   The only existing public declaration, halfPlane_weak_convergence, retains
   its complete signature byte for byte. Universes, section variables, its
   docstring, and the public ExactCoupleConvergence import are unchanged.
   The added module states the reported finite theorem; there are no definitions
   or forced adaptations and no interface change requiring a change record.
2. **Proof and axioms: pass as a decomposition.** Compiled both modules in
   import order with lcompile.py, and recompiled after the repair below.
   The main module has no sorry; the new module has exactly the named
   finitePage_image_quotient sorry. Scanned for forbidden declarations and
   holed definitions: none. A scratch copy prints axioms for both public
   theorems: propext, Classical.choice, Quot.sound and sorryAx only. The
   remaining axiom is accounted for by the finite lemma and pageCouple_image.
3. **Finite statement: pass.** Read the new Lean statement and all four node
   steps against ExactCouple's derivedD, DerivedMaps.g_comm and the tower's
   projection_zero, cycleLift_comm and projection_succ. Read Stacks Tags
   [011R](https://stacks.math.columbia.edu/tag/011R),
   [011T](https://stacks.math.columbia.edu/tag/011T) and
   [0AMJ](https://stacks.math.columbia.edu/tag/0AMJ): these provide the
   exact-couple construction, not a ready-made finite quotient theorem.
   The original blueprint remains unavailable locally as already reported.
   At r=0 and p<=0, the normalized cocone is invertible and hnext makes g
   epi; exactness identifies its kernel with the next alpha image. At p=r,
   the anchoring index is zero, so no invertibility of the cocone at index
   one is assumed: its image is obtained by the incoming derived alpha.
   For p<0 the finite E object vanishes and both colimit image steps are
   top. The zero couple gives zero on both sides. The image-epi induction
   and g_comm/projection_succ induction specify the comparison equation;
   no arbitrary witness supplies data. This is strictly the finite quotient
   step, with no limiting subobjects, global D bound or convergence claim.
   Independently ran LeanFinder, Loogle and grep with new queries (logged
   in searches.jsonl), and searched both library roots. Read
   finitePage_image_lift and finitePage_graded_quotient: the latter has a
   fixed max-based page and global lower bound and lacks the original-g
   tower equation. It cannot replace this statement outright. Closing the
   remaining two inductions is not a routine few-minute repair.
4. **Reduction and pruning: pass after repair.** Checked every main-proof
   branch: q<a uses zero source D; p<0 uses two top filtration steps;
   the remaining branch chooses r with p<=r and q-a<r, proves both
   differentials vanish throughout the tail, and identifies the GLB/LUB
   with that tail. pageCouple_image proves the next D term zero before
   the finite comparison is invoked. The two explicit cokernel comparisons
   then give the canonical equation, epimorphicity and equal kernels.
   Direct ExactCouple and Filtration imports are redundant through the
   unchanged public import; DerivedCoupleExact is needed for pageCouple_image.
   Every old proof_deps node remains used, so no node or module is pruned.
   Read the unit sk-prop-av-pqf-finite: its realized lists are empty, and
   the imported unit route is unchanged. The repaired page_zero and arbitrary
   tower_stationary are broader than the downstream HalfPlaneConvergence
   copies. However, the purportedly generalized pullback_kernel was still
   identical to private helpers in SubobjectHomologyStep and
   FilteredComplexPageHomology. Repaired it by removing the abelian assumption:
   it now works with zero morphisms, kernels and pullbacks only.
   Loogle found Subobject.pullback_kernelSubobject in its newer Mathlib index,
   but rg finds no such declaration in the pinned source and #check reports
   Unknown constant. Thus it is unavailable in this build; the fully proved
   broader local helper is retained. The first Loogle query used an invalid
   namespace and was not treated as evidence of absence; the corrected query
   produced this candidate.
5. **Nodes: pass.** Diffed the existing JSON: only proof, proof_deps and
   proof_origin differ. Its steps follow the actual Lean reduction, and their
   uses union equals proof_deps. The new node's Lean signature matches its
   module, and its source, proof, dependencies, search records, status,
   creation record, blueprint ancestry, chapter and unit are present.
   Updated the existing proof and proof_origin to describe the further
   categorical generalization. The new statement and its node are unchanged.

Second reading changed: generalized pullback_kernel from abelian categories to
categories with zero morphisms, kernels and pullbacks, removing a remaining
private-statement duplicate; updated its DAG description and this report.
Closed 1 original hole and added 1 finite hole: decomposition, net 0; no module pruned.
