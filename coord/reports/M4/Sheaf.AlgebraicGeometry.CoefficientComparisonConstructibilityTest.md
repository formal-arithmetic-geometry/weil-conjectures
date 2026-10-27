## What changed

Proved `AlgebraicGeometry.ProEtale.coefficientComparison_constructibilityTest`
from the recorded stratum comparison interfaces. Each implication retains the
original affine-open partition, stratum schemes, and immersion maps. The forward
implication pulls back the finite local models and uses Noetherianity to give them
finite presentation. The converse forgets finite presentation to finite generation
and applies single-stratum reflection. There is no gluing step across affine opens.

Restored the absent modules `CoefficientComparisonFixedPullback` and
`CoefficientComparisonFiniteReflection`, whose Lean attachments and nodes remain
in the current DAG after the preceding delivery was taken out. Neither has a row
in the current rework table or a current local claim. The compatibility lemma is
reconstructed with a complete proof: scalar restriction is an equivalence, the
canonical ring map respects constant scalars, and uniqueness of adjoints turns the
sectionwise direct-image square and the base-change square into pullback isomorphisms.
All helpers are private and proved. Existing theorem signatures, public imports,
and definitions are unchanged. All added imports of the item are private proof imports. The restored node copies
retain their identities and statements, with Lean restoration provenance updated.
The change record is `coord/changes/M4-coefficient-comparison-interface-restoration.md`.

Also checked the unchanged `Sheaf.Paper.FiniteComparisonPresentation`, named in
the old return. Its current source has no universe or missing-argument error
against this packet. The diagnostic compile type-checked the file but exceeded
the single-file time limit (85.5 seconds). Private elaboration experiments did not
improve its timing and are excluded from this packet. No consumer source is changed.

## Proved and sorry left

Closed the one original direct hole:
`AlgebraicGeometry.ProEtale.coefficientComparison_constructibilityTest`
(node `lem-pe-coefficient-comparison-constructibility-test`).

Restored and proved
`AlgebraicGeometry.ProEtale.coefficientComparison_fixedPullback`
(node `lem-pe-coefficient-comparison-fixed-pullback`).

One hole is left in the restored module:
`AlgebraicGeometry.ProEtale.coefficientComparison_finite_reflect`
(node `lem-pe-coefficient-comparison-finite-reflection`). Its statement is the
existing single-stratum finite-local-system reflection interface, with its source
and full proof in words. No new mathematical statement or node is introduced.
Within the delivered files this is a decomposition: one direct hole closed,
one restored lower hole added, for a net change of zero direct holes. The item has zero direct holes; the
packet has one direct hole. No definition contains a hole.

The item compiles without warnings through `lcompile.py` (4.6 seconds), and
the reconstructed compatibility module compiles without warnings (36.3 seconds).
The final delivery runs the compiler and axiom probes for all delivered modules.
The unchanged downstream presentation file has the timing limitation recorded above.

## No longer needed

No existing import line is removed, and no existing module is withdrawn.
The sole original public import is required by the theorem statement.
The four recorded proof dependencies remain used. The proved isomorphism-transport
helper of `lem-pe-coefficient-finite-local-model-pullback` is also used.
The general local-system pullback theorem is imported directly, since that helper
module imports it privately for its own proofs.
The item node is updated to record this additional explicit proof dependency.

No derived direct-image comparison or global gluing of partitions is used by this
property test. No whole-library pruning is claimed. The unit's finite-local-system
comparison route on each stratum is preserved; its classicality, essential-image,
and derived claims remain separate items.

## Where the brief, the DAG or earlier work was wrong

The DAG records two interfaces whose files are absent from the current Lean tree.
The prior D8 report and return identify them as part of a delivery taken out after
a downstream global-build failure. Their absence does not authorize withdrawal:
this delivery restores the mathematical interfaces and reconstructs the proved one.

The old return cites failures in `Sheaf.Paper.FiniteComparisonPresentation` caused
by changes of instance behavior. This delivery exports no instance declaration or
attribute change, removes no exported instance, changes no definition body, and
introduces no public proof dependency into the item. The scalar equivalence is a private theorem;
its instances are installed only inside its proof and the compatibility proof.

The recorded finite-local-system twist interface takes a ring in `Type u`
and works with its `ULift` in module universe `u+1`; the classical-module
comparison interface also fixes the module universe to `u+1`. Neither can
be specialized to arbitrary independently sized Noetherian A. The existing reflection
interface is retained with the Stacks Tag 099Y proof; it is strictly a single-stratum
step and is not the constructibility theorem under a different name.

Edge cases: the two directions preserve empty partitions and covering sieves,
zero models and zero coefficient rings. No nonempty chart or finite underlying
coefficient set is assumed. The affine-open quantifier is retained, so no global
quasi-compactness hypothesis is added.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
