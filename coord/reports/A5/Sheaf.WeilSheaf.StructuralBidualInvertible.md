## What changed

Proved `WeilConjectures.NativeBidualRealization.isIso_commonBidual` without changing its
statement. The proof first obtains full faithfulness of the actual common-stage Hom dual,
then proves that postcomposition with the actual evaluation transpose is bijective on every
Hom set. Yoneda concludes invertibility. Realization compatibility retains the signed
symmetry and the actual tensor-Hom transpose throughout.

Added the proved module `Sheaf.WeilSheaf.StructuralDualizingIdentification`. Its theorem
identifies the specified structural exceptional image with the Verdier dualizing object,
using rational left normalization, uniqueness of right adjoints, common coefficient
comparison, compactification refinement, and fully faithful coherent reduction of the unit.
Both modules use private proof imports where appropriate. Single-file compilation passed
without warnings (16.8 seconds for the identification, 23.7 seconds for the item), in
import order against the current dependency overlay. Updated the item node to match
this proof and supplied the new proved node.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.NativeBidualRealization.isIso_commonBidual`
(`lem-sf-structural-evaluation-bidual-invertible`).

Also proved `WeilConjectures.NativeBidualRealization.structural_dualizing_identification`
(`lem-sf-structural-dualizing-identification`). No holes were added. No `sorry` remains in
either delivered module. The proof uses the existing project declarations with their
current proofs; this is not a claim that their transitive axioms are already closed.

## No longer needed

No original import is removed: `NativeBidualEvaluationRealization` defines the arrow in the
unchanged statement. No existing module is withdrawn.

The former plan to conjugate the separately chosen coefficient biduality map through two
Hom comparisons is unnecessary. Full faithfulness of the actual dual functor and its
representing evaluation bijections prove the canonical arrow invertible directly. The
native exceptional-forgetful theorem is no longer an explicit proof dependency of this
node; its existing data and interfaces remain statement dependencies and imports. The
new identification uses only ordinary exceptional coefficient systems, with no appeal
to a native right adjoint or its comparison.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The old proof plan required more biduality-normalization
bookkeeping than necessary. The replacement preserves both the exceptional origin of the
dualizing object and the specified evaluation arrow. Zero objects and empty schemes require
no separate cases: all arguments use isomorphisms or Hom-set bijections valid in those cases.

The current server queue classifies the item as stage-3 proof/route. Its archived rework
record names `CommonStagePullbackRepresentativeLinearity`; the compile service rebuilt this
unpublished dependency in its private overlay, so verification did not rely solely on its
older published artifact. No dependency source was changed by this delivery.

## New nodes

`lem-sf-structural-dualizing-identification`, in the same chapter and unit as the item,
records the proved identification of the geometric dualizing object for the specified
exceptional system and compactification. Its conclusion concerns only objects and their
isomorphism, with no bidual arrow or native adjunction assumption. It is fully proved from
existing declarations and introduces zero holes. No change record is needed: all existing
signatures, definitions, attributes and public imports are unchanged.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
