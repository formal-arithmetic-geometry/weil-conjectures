## What changed

`Sheaf.Algebra.Homology.FilteredFreeKProjective` now proves
`CochainComplex.isKProjective_of_filtered_free_stage` by induction. Its zero case directly
constructs a null homotopy from `IsZero.eq_of_src` and `Homotopy.ofEq`. Its successor case
uses the new proof-only import `Sheaf.Algebra.Homology.FilteredFreeKProjectiveStep`, whose
single statement concerns one split extension, independently of any filtration.

The existing telescope theorem was missing the degreewise splitting hypothesis required
by its node and source. Added `hsplit` and passed the final theorem's existing argument.
No target, definition, or finite-stage/final theorem signature changes. The two remaining
holes have complete proof descriptions, and the delivered DAG copies match the Lean.

Validation: `lcompile.py --all` compiles both modules without warnings. Edge cases of the
new extension statement include empty free bases, zero rings, a zero preceding complex,
and unbounded degrees: the coproduct argument covers all of them.

## Proved and sorry left

Closed one of the two original holes:
`CochainComplex.isKProjective_of_filtered_free_stage`
(node `lem-pc-filtered-free-kprojective-stage`). This is a decomposition into a proved base
case and one new strict successor subproblem; it is not a complete sorry-free proof.

Added one hole:
`CochainComplex.isKProjective_of_filtered_free_step`
(node `lem-pc-filtered-free-kprojective-step`) in its new module.

Remaining original hole:
`CochainComplex.isKProjective_of_filtered_free_telescope`
(node `lem-pc-filtered-free-kprojective-telescope`), with the corrected split hypothesis.

`CochainComplex.isKProjective_of_filtered_free` was already proved and remains proved
from the finite-stage result and corrected telescope result. It is not counted as a newly
closed hole. Net holes closed minus holes added: zero. Neither delivered module contains
a definition or a private/anonymous hole.

## No longer needed

No existing library import, node, or module is pruned. The finite-stage and telescope nodes
remain necessary to the final theorem, and the successor node is needed by induction.

Removed the earlier sandbox's proposed `FilteredFreeKProjectiveZero` module and
`lem-pc-filtered-free-kprojective-zero` node, neither of which exists in the repository:
the direct zero-case proof avoids that proposed hole and its proof import. This is not
claimed as pruning an existing library module. The telescope node no longer incorrectly
lists the finite-stage theorem as its own proof dependency: it takes `hstage` as a hypothesis.

## Where the brief, the DAG or earlier work was wrong

Retry validation (2026-10-13): both saved modules compile successfully with
`lcompile.py --all` (exit code 0). The launcher source-import check no longer rejects the
installed Mathlib imports. `deliver3.py --no-push` now prints OK and classifies this
statement repair and decomposition as CODEX. No launcher or project tool was changed
by this worker, and nothing was pushed.

The earlier attempt left a trivial zero-complex assertion as a new hole, had an overlong
comment, and included a second-reading section. That section was removed so that the
independent second reader can assess this revised delivery.

The original telescope Lean statement was false without splitting. The counterexample
is the degree-zero filtration 0, Z, (1/2)Z, (1/4)Z, ... of Z[1/2]. Each stage is
K-projective, while the union is not. The source explicitly needs graded retractions:
[Stacks Tag 09KL](https://stacks.math.columbia.edu/tag/09KL), with the Hom-vanishing
argument in [Tag 09KM](https://stacks.math.columbia.edu/tag/09KM). The node's words
already include splitting; the delivery repairs its Lean statement rather than weakening
the final filtered-free theorem. Only this module calls the repaired intermediate theorem.

The change record is `coord/changes/filtered-free-telescope-splitting.md`. No external
forced adaptations are needed. The unit `sk-thm-picard-duality` has empty `realized` node
lists; none of its protected statements or steps is bypassed by the finite-stage induction.

## New nodes

`lem-pc-filtered-free-kprojective-step`, in
`dag/nodes/sec-picard-framework/lem-pc-filtered-free-kprojective-step.json`, states that one
degreewise split extension by a coproduct of shifted rank-one free complexes preserves
K-projectivity. It is strictly a successor step, with no filtration, exhaustion, initial
stage, or conclusion for all stages. Its module is
`Sheaf.Algebra.Homology.FilteredFreeKProjectiveStep`. The docstring and node record the
admissible-triangle and generator-wise null-homotopy argument from Stacks Tag 09KM.
Mathlib searches found the bounded-above theorem and split-triangle infrastructure, but
no theorem for this arbitrary unbounded extension. LeanSearch was unavailable; this is
recorded honestly, alongside successful LeanFinder and source searches.

## Second reading by F1

1. Compared the delivered main module against the repository using `diff` and the
   declaration parser. The stage and final theorem signatures are byte-for-byte unchanged.
   The only existing signature change is the telescope's added `hsplit`, explicitly recorded
   in `coord/changes/filtered-free-telescope-splitting.md`. The counterexample there is valid:
   the nonsplit exhaustive union of the free groups 2^{-n} Z is Z[1/2], which is not projective.
   The existing final theorem already assumes the retractions and now passes them through.
   A fresh downstream check lists 768 import descendants and only this module as a user
   of the telescope declaration; the source-name search confirms it. No definition changes,
   target changes, or forced adaptations. Verdict: the declared repair is necessary and
   does not make the final result easier.

2. Compiled both modules in import order with `lcompile.py --all`; no errors or warnings.
   Compiled independent scratch copies with `#print axioms` for all four declarations:
   each uses only propext, Classical.choice, Quot.sound, and sorryAx. The latter is accounted
   for by exactly the two named holes listed above. There are no definitions, private holes,
   axioms, unsafe/opaque declarations, or foreign implementation attributes in this delivery.
   Read the induction: `IsZero.eq_of_src` proves the base map equals zero, `Homotopy.ofEq`
   provides its null homotopy, and the successor passes precisely hsplit n and hquot n to
   the extension lemma. Verdict: correct decomposition, not a sorry-free proof; net zero.

3. Read the new step's full signature, proof docstring and node, and Stacks Tags
   [09KM](https://stacks.math.columbia.edu/tag/09KM),
   [09KL](https://stacks.math.columbia.edu/tag/09KL), and
   [09KJ](https://stacks.math.columbia.edu/tag/09KJ) online, since the local tex is absent.
   A componentwise left inverse makes f monic, so its cokernel gives a degreewise split
   exact sequence. The free-single generators give cycles in the acyclic target; choosing
   their primitives gives null homotopies, and coproducts assemble them without a bound
   on degrees. The exact Hom sequence for the admissible triangle then proves the extension
   assertion. Empty I reduces to a zero quotient, K = 0 reduces to the free-single sum,
   and the zero ring reduces to zero complexes. Arbitrarily many generators in arbitrary
   integer degrees cause no finite-support restriction on maps out of the coproduct.
   The step has no filtration or conclusion for every n: it is strictly the successor part.
   Independently searched LeanFinder for "K-projective complexes closed under coproducts
   and degreewise split short exact extensions", and grep for orthogonal extensions,
   K-projective coproducts and degreewise splitting; also searched both project roots.
   Read Mathlib's KProjective file, especially isKProjective_of_projective: its common
   upper bound excludes the unbounded free-single sum here. No exact existing replacement
   was found. The coproduct/triangle formalization is not a few-minute closure.
   Verdict: true and needed, with an adequate source and complete mathematical argument.

4. The proof opens the original stage hole and closes its base directly, before importing
   a new successor hole. The new import is correctly plain `import`: only the proof uses it.
   The three public Mathlib imports provide the ModuleCat abelian/cokernel instances,
   arbitrary coproducts, and K-projectivity appearing in signatures. No original library
   module becomes unused; the removed proposed zero lemma was never in the repository.
   Checked every old proof_deps entry: only the telescope's stage dependency is removed,
   correctly, since hstage is now its input rather than a theorem it invokes. The report
   already records that removal. Read sk-thm-picard-duality.json: its realized statement
   list and single step list are empty; this induction retains the finite-stage/telescope
   route. Verdict: no protected unit route bypassed and no missing pruning claim.

5. All four node lean.statement fields match the actual Lean declarations verbatim.
   Existing node changes are confined to lean/proof/proof_deps/proof_origin. The stage
   proof_deps names the successor node used in Lean; the final node names the stage and
   telescope results; telescope uses its supplied hstage and has no theorem dependency
   on stage. The new node has its source, searches, creation record, blueprint ancestry,
   chapter, unit and complete Lean record. Verdict: the nodes agree with the delivered
   code and retain all statements except the expressly recorded Lean telescope repair.

Second-reader changes: clarified the telescope docstring and matching node with the
explicit negative retraction components and checked l a = id by cancellation. With the
identity-minus-successor convention, the positive formula printed in Tag 09KL gives
minus identity; the negative components fix that sign. Also distinguished the admissible
sequence source 09KL from the triangulated-category source 09KJ, and refreshed the change
record's downstream count. No Lean proof, signature, hole count, or import changed during
this second reading.
