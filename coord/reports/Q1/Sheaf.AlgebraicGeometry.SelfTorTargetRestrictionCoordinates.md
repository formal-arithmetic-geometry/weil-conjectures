## What changed

Proved the reduction of AlgebraicGeometry.exists_selfTor_target_restriction_coordinates without
changing its statement. The geometric chart construction is isolated in
Sheaf.AlgebraicGeometry.SelfTorChosenResolutionCharts, using only the fixed Mathlib projective
quotient resolutions. The assigned theorem extracts its explicit quotient map, augmented
comparison and tensor comparison, constructs q explicitly by homology, proves its cycle
formula, then applies the new, fully proved
AlgebraicGeometry.selfTor_restriction_certificate_of_resolution.

The algebraic theorem in Sheaf.RingTheory.SelfTorRestrictionResolutionIndependence is proved
from Mathlib. It composes the given comparison with same-ring lifts of the quotient identities.
Exact restriction of scalars transports cycles; naturality of homologyπ and isoLeftDerivedObj
identifies the transported Tor classes. Both private helpers are proved. It needs no flatness
assumption on the ring homomorphism, no geometric input and no new sorry. A scratch axiom check
reports only propext, Classical.choice and Quot.sound.

The DAG now records this separation. The original proof import of
AffineQuotientResolutionSheafification moves to the new geometric module; the assigned module
imports the two new modules as proof imports. Existing public imports and signatures remain
unchanged.

## Proved and sorry left

Closed: AlgebraicGeometry.exists_selfTor_target_restriction_coordinates
(new-t2-self-tor-target-restriction-coordinates), the only original hole.

New fully proved theorem: AlgebraicGeometry.selfTor_restriction_certificate_of_resolution
(new-q1-self-tor-restriction-resolution-independence). Its private helpers restrict_cycles_lift
and resolution_lift_cycle_class contain no sorry.

Added hole: AlgebraicGeometry.exists_selfTor_chosen_resolution_charts
(new-q1-self-tor-chosen-resolution-charts), in its own module, with the complete augmentation
and K-flat comparison argument in its docstring. This is the only sorry left in the delivered
files. It asserts only the augmented tensor chain comparisons and their geometric section
square for fixed projective resolutions. The Tor map is an explicit homology construction;
neither its cycle formula nor the all-resolution certificate is assumed. The
resolution-independence part of the original argument is actually proved, not moved into
another hole. This delivery is a decomposition: one original hole closed, one lower geometric
hole added, net zero holes. The assigned module has no remaining sorry. Its two proved private
helpers restrict_homologyπ and tensorComparison_cycle_formula establish the algebraic cycle
formula for the explicitly constructed q; that formula is not part of the new geometric hole.

Edge cases checked against the construction: degree zero uses the quotient augmentation; a zero
quotient gives a zero tensor complex; the basic open D(0) gives the zero localized ring. The
algebraic proof makes no nonzero, positive-degree, finite-generation, characteristic or
flatness assumptions.

## No longer needed

Removed direct proof import: Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification. It
remains needed by the geometric subproblem and is imported there, so this is no pruning of the
targets' import closure. No existing node or module is claimed pruned. The sheafification,
K-flatness, affine-section and adjunction dependencies remain through the geometric node; the
certificate definition remains through the algebraic module. Unneeded explicit public imports
in the new geometric module were removed when their APIs were already exported by
SelfTorAffineSection.

## Where the brief, the DAG or earlier work was wrong

The original dependencies supply sheafification, K-flatness, a definition of the restriction
certificate and affine sections. They do not supply the augmentation-normalized derived chart
comparison or its localization naturality. Thus the plan cannot be instantiated merely by
applying the listed signatures. Its algebraic resolution-independence step can, however, be
proved directly with Mathlib, as done here.

The new geometric hole keeps the original K-flat augmentation route; no unit statement or step
is bypassed (the unit record has no realized nodes attached to this item). Its semilinear
augmentation lift uses the proof of Stacks 00LS for a projective source and an exact target
after restriction of scalars; the target need not be projective over the source ring.

Mathlib searches were run through msearch.py and are logged in searches.jsonl. LeanFinder found
affine localization and ideal-sheaf results, but no full comparison. Loogle found
ProjectiveResolution.Hom and related APIs. Grep found the canonical Tor naturality and
projective identity-lift lemmas used in the algebraic proof. LeanSearch returned HTTP 500,
recorded as unavailable. No existing blueprint statement matching either new theorem was found
in searches for Tor restriction and resolution comparison.

The published local build initially lacked SelfTorRestrictionCertificate.olean. The geometric
module and the algebraic proof (with the certificate formula expanded only in a scratch
experiment) were compiled while waiting for the published dependency. No dependency source was
changed or delivered.

## New nodes

new-q1-self-tor-restriction-resolution-independence: the generic algebraic
one-pair-to-all-pairs certificate theorem, fully proved from Mathlib resolution lifts and Tor
naturality. It is independent of schemes and derived sheaf tensor.

new-q1-self-tor-chosen-resolution-charts: the remaining geometric K-flat chart construction
with explicit augmented tensor comparisons only for the fixed projective quotient resolutions.
This omits both the cycle formula and the universal certificate, which the proved private
helpers and algebraic theorem supply. It retains sheafification, K-flatness, actual affine
sections and the tensor-pullback adjunction from the original plan.

No definition, target statement or existing public interface changed; no change record or
forced adaptation is needed.

## Second reading by Q1

1. Compared the delivered target module with the repository version. The target theorem signature and all existing declarations are byte for byte unchanged; only its proof and proof-only imports changed. The two auxiliary modules are new and are recorded by their nodes.

2. Compiled all three delivered modules with `lcompile.py`; they compile without errors or warnings. The target theorem and the algebraic certificate theorem have no `sorry`; the only remaining `sorry` is the named geometric theorem `exists_selfTor_chosen_resolution_charts`, with its source docstring and matching node. No axioms, unsafe declarations, or hollow definitions were added; the proved declarations use only the permitted axioms.

3. Checked the split-off statements against their definitions and edge cases. The geometric statement is strictly weaker than the original target: it fixes the chosen projective resolutions and omits the universal certificate and cycle formula. The algebraic certificate theorem is a genuine all-resolution consequence of one augmented comparison and its cycle formula, not a restatement of the target. Both statements are mathematically true and have matching Lean declarations and DAG nodes; searches found no duplicate library declarations.

4. Read the proof from the target downward. The target uses the geometric chart theorem, the explicit homology construction, the proved cycle formula, and the proved resolution-independence theorem. The fixed-resolution route preserves the unit route. The removed direct import of `AffineQuotientResolutionSheafification` is still used by the geometric auxiliary module; no target dependency was pruned.

5. Checked the DAG records, proof dependencies, proof origins, and unit route against the Lean proof. Existing target metadata and signature are unchanged; both new nodes describe their declarations and sources. No change record or forced adaptation is required.

I changed only this report by adding the required second-reading record. No Lean source or DAG statement was changed during review.
