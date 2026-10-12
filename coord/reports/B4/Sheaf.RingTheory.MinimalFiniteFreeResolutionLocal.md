## What changed

`Sheaf.RingTheory.MinimalFiniteFreeResolutionLocal` closes its original hole by first
obtaining a bounded finite free resolution and then minimizing that resolution. The two
parts are isolated in new proof-only imports `Sheaf.RingTheory.BoundedFiniteFreeResolution`
and `Sheaf.RingTheory.MinimalizeBoundedFiniteFreeResolution`. The original statement and
public imports are unchanged. All three modules compile through lcompile.py. The second
reader restored the planned proof-dependency imports in the two new modules.

The retained attempt was repaired: both new modules now have complete proof descriptions;
their DAG statements introduce their own hypotheses, and their proof steps follow the
original node's construction and cancellation steps. The main node records the composition.
The worker-written placeholder second-reading section was removed for the independent reader.

## Proved and sorry left

Closed: `ModuleCat.exists_minimal_finite_free_resolution`
(node `lem-weil-pbc-minimal-finite-free-resolution-local`).

Added holes: `ModuleCat.exists_bounded_finite_free_resolution`
(node `stage3-b4-bounded-finite-free-resolution`) and
`ModuleCat.minimalize_bounded_finite_free_resolution`
(node `stage3-b4-minimalize-bounded-finite-free-resolution`).

This is a decomposition: one upper hole closed, two lower holes added, net minus one.
No hole remains in the original module. The bounded construction omits minimality;
the cancellation theorem starts from an already constructed finite free resolution and
has no finite-projective-dimension hypothesis. Neither repeats the original argument.

Edge cases: for `d = 0`, construction is the identity augmentation of the finite free
module `M`, and minimalization is vacuous. For `M = 0`, the zero resolution works.
Zero terms have empty bases, hence cannot supply a unit pivot. Cancellation involving
degree zero preserves the augmentation because it kills the degree-one image. The
Noetherian local assumptions exclude a degenerate local-ring counterexample.

## No longer needed

Removed from the original module four unused proof imports:
`Sheaf.Algebra.Homology.UnitEntrySplits`, `Sheaf.RingTheory.FiniteFreeResolution`,
`Sheaf.RingTheory.FiniteProjectivePrimeLocalFree`, and
`Sheaf.RingTheory.ProjectiveResolutionKernelProjective`.

These remain mathematical dependencies of the two new nodes and are now imported there
as proof-only imports. No module is pruned from the import closure. The original node now
directly depends only on the two intermediate nodes. Its old definition dependencies
(`def-weil-pbc-finite-global-dimension`, `def-weil-finitely-generated-module`, and
`def-weil-pbc-exact-sequence`) remain in the intermediate plans; the Mathlib leaf
`lem-weil-pbc-noetherian-submodule-finite` is retained through
`Mathlib.RingTheory.Noetherian.Basic`. Thus every old proof dependency is retained
below the reduction, and none is declared globally unnecessary. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous delivery attempt failed because deliver3.py could not import
`import_cycles.refuse_missing`. The installed tool now provides this function, and its
initial dry run succeeded without any tool edits by this worker.

The retained new-node statements were not self-contained, the minimalization node's proof
incorrectly described syzygy truncation, and both docstrings omitted substantial steps.
These records have been corrected, preserving every existing Lean signature. The retained
report also called the result a proof without accounting for the two added holes; the
account above explicitly records a decomposition. LeanSearch was retried but returned Internal Server Error; the node records this as
unavailable, along with the original node's earlier LeanSearch results and fresh
LeanFinder, Loogle and source searches. No exact existing theorem was found.

The five original mathematical steps
remain divided into bounded construction (steps 1–3) and cancellation (steps 4–5).

## New nodes

`stage3-b4-bounded-finite-free-resolution`, module
`Sheaf.RingTheory.BoundedFiniteFreeResolution`, isolates the bounded finite-free
construction using Tags 0CXF, 00LP, 00O5, 00IK and 00NX.

`stage3-b4-minimalize-bounded-finite-free-resolution`, module
`Sheaf.RingTheory.MinimalizeBoundedFiniteFreeResolution`, isolates cancellation of unit
entries using Tag 00MT as applied in Tag 00OA. Both new statements are public named
theorems with whole-proof sorries, and neither chooses data in a definition.


## Second reading by B4

1. **Visible declarations: pass.** Read all three delivered modules and diffed the
   original module against the repository. The only original Lean edits are four
   proof-only imports replaced by two proof-only imports, and the theorem body.
   Its full signature, universes, public imports, visibility and docstring are
   byte-for-byte unchanged. No definition or target is altered; no change record
   or forced adaptation is required. The existing node differs only in `proof`,
   `proof_deps` and `proof_origin`.
2. **Kernel and holes: pass as a decomposition.** Compiled all three files in import
   order using lcompile.py after the repairs, with no errors or warnings. In a
   scratch copy, `#print axioms` on all three declarations returned exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The only two sorries
   are the entire proofs of the two named, documented intermediate theorems listed
   above. There are no new definitions, arbitrary witness definitions, or forbidden
   declarations. The main proof obtains the bounded resolution and passes precisely
   its zero-bound and finite-free clauses to the cancellation theorem. One upper
   hole is closed and two lower holes are added: this is not a completed proof of
   the target and has net minus one hole.
3. **Split statements: pass.** Read Stacks Tags
   [0CXF](https://stacks.math.columbia.edu/tag/0CXF)
   (`lemma-what-kind-of-resolutions-Noetherian-local`),
   [00MT](https://stacks.math.columbia.edu/tag/00MT)
   (`lemma-add-trivial-complex`), and the cancellation paragraph in
   [00OA](https://stacks.math.columbia.edu/tag/00OA)
   (`lemma-length-resolution-residue-field`); the local algebra.tex is absent here.
   Construction has exactly the original hypotheses and only the bounded finite-free
   conclusion. Cancellation assumes that construction is already supplied, and has
   no projective-dimension or finiteness hypothesis on M. Both are true and strictly
   parts of the original argument. Checked d=0, M=0, empty bases, and a unit pivot
   in the differential from degree one to zero. For the latter, augmentation kills
   the removed degree-zero summand, so the complementary augmentation still has
   kernel equal to the degree-one image. Over a field all nonzero coefficients are
   units; cancellation leaves a degree-zero resolution, as required.
   Fresh searches used Loogle `"ProjectiveResolution", "Free"` (zero hits), LeanFinder
   for bounded finite-projective resolutions with radical differentials (only generic
   projective-resolution/local-projectivity ingredients), and grep for
   `minimalize|bounded_finite_free|exists_splitting_of_isUnit_entry` (zero Mathlib hits).
   Also searched lean/Sheaf, lean/WeilConjectures, and Mathlib's homology, ModuleCat,
   and ring-theory sources with alternate terms. Read the nearby finite-free
   sequence construction and stalk minimal-complex theorem: they respectively leave
   an unrestricted left kernel and concern sheaves over scheme stalks, not these
   module resolutions. Neither replaces either intermediate theorem in a few lines.
   Read all four old dependency modules; the already proved infinite finite-free
   resolution and unit-entry splitting are ingredients, not duplicate results.
4. **Route and pruning: pass after repair.** Construction keeps original steps 1–3:
   finite-free surjections, projective syzygy, Noetherian finiteness and local freeness.
   Cancellation keeps steps 4–5: split the identity summand and induct on the finite
   rank sum. The two new holes are not mere renamings of the item. Read
   dag/units/sk-thm-p1.json: this auxiliary node is not among its `realized` statement
   or step nodes, and none of those nodes or routes changes. No global pruning is
   claimed. Restored the three construction imports plus Noetherian.Basic to the
   bounded module and UnitEntrySplits to the cancellation module, because their
   still-open proof plans use those declarations. All added imports are proof-only.
5. **DAG: pass.** Matched each node's lean.statement verbatim against its declaration,
   and matched the original node's two dependencies to the two calls in the Lean
   proof. Each new node has its own complete hypotheses, docstring argument, source,
   creation/blueprint fields, chapter/unit and Lean record. Its proof_deps is exactly
   the union of its steps' uses. The construction uses the existing finite-free,
   syzygy, finiteness and local-freeness statements; cancellation uses the existing
   rank-reducing unit-entry split and exactness. The new nodes retain the old proof
   route rather than claiming these lower holes are proved. Corrected the unavailable
   LeanSearch entries to include the explicit `unavailable` verdict.

Second reading changed: restored planned proof-only dependency imports in both new
modules; corrected unavailable-search verdicts; expanded the dependency accounting and
recorded this independent review. Existing theorem signatures and both split statements
were preserved. Neither large remaining construction was closable in a few minutes.
