## What changed

Prove the assigned theorem
`WeilConjectures.CompletedCoefficientNormalization.completed_coefficient_tensor_normalization`
from the existing coefficient pushout comparison. Preserve its exact signature and
all existing constructions. Private helpers establish quotient normalization for
all admissible indices, constant-comparison naturality, inverse-image pushouts,
and coefficient-extension compatibility.

The three adapted dependency modules are
`Sheaf.Paper.PurTwistCoefficientRings`, `Sheaf.Paper.PurTwistCoefficientTensor`, and
`Sheaf.Paper.PurTwistCoefficientComparison`. They allow independent site and
coefficient universes. The held LisseLatticeCoefficientsSized module is not
modified: its continuous presheaf is used with a fully proved private sheaf-condition
helper in PurTwistCoefficientTensor. The existing coefficient tensor/comparison
proofs are generalized to independent sizes. The change record is
`coord/changes/P7-independent-coefficient-universes.md`. No new module or node
is added, and no source-library declaration or target signature changes.

Repair of returned head `74d04997c85`: the change record's `## Users` explicitly
lists `Sheaf.Paper.DiagonalCoefficientReference`, `Sheaf.Paper.DiagonalTowerTrace`,
and `Sheaf.Paper.OrientationFiniteReductionTwists`, their precise coefficient
uses, and the effect of the preserved tied-universe specializations. The renewed
current-source audit covers all 39 active downstream modules, including the new
`Sheaf.Paper.NormalLatticeFiniteCoverPresentation`. Archived consumers remain
listed as well. Current DAG audit metadata is preserved.

## Proved and sorry left

Closed the item's one original hole:
`WeilConjectures.CompletedCoefficientNormalization.completed_coefficient_tensor_normalization`
(node `lem-pur-completed-coefficient-tensor-normalization`).
The open public sheaf-condition theorem in J7's module remains outside this
packet. A private, fully proved sheaf-condition helper is used instead; no claim
is made to close J7's hole.

Added holes: zero. Remaining holes in all four delivery modules: zero.
Split-off statements: zero. No definition contains a hole.

The pre-ownership-repair packet compiled successfully and its theorem axiom
check reported only propext, Classical.choice and Quot.sound. Fresh compilation
and axiom checks of the final private-helper packet are recorded below when complete.

Earlier retained checks compiled eight external consumers unchanged:
ContinuousCoefficientSliceNormalization, EtaleMonodromyRealizationData,
MonodromySingleObjectCover, PurTwistIntegralBasis, PurTwistSheafLocallyFree,
PurTwistSheaves, IntegralLisseReductionData, and StratifiedLatticeRank.
These are historical checks, not claims of fresh compilation of quarantined files.

## No longer needed

Removed direct imports `Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis`,
`Sheaf.NumberTheory.Padics.LocalFieldCoefficientStages`,
`Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`, and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
The existing coefficient comparison already proves the arithmetic tensor result;
the constant comparison follows directly from adjunctions, and the ring tensor
is the categorical pushout. The private imports
`Mathlib.CategoryTheory.Sites.LeftExact`, `Mathlib.CategoryTheory.Sites.Sheafification`,
and `Mathlib.NumberTheory.Padics.PadicNumbers` are redundant and removed.

This removes the item's direct proof dependencies on
`lem-sfb-local-field-integral-basis`, `lem-pur-local-field-coefficient-stages`,
`lem-weil-pbc-sheafification-sets-exact`, and
`lem-pe-constant-left-module-inverse-image`. Separate proof dependencies
`def-weil-l-adic-numbers` and `def-weil-pbc-constant-sheaf` are absorbed into
coefficient interfaces; their definitions remain used through those interfaces.
The node's proof, proof_deps, proof_origin and withdrawn tool-use entries reflect
this route. No library module is withdrawn or claimed globally unnecessary.
No unit statement or realized unit route changes.

## Where the brief, the DAG or earlier work was wrong

The planned finite-basis argument duplicates the proved coefficient comparison.
Its former interface tied site and coefficient universes together, whereas the
assigned theorem has independent universes. Generalizing the existing proof
resolves that mismatch without weakening a hypothesis or conclusion.

The quotient condition is available already at k = n: l is in the maximal ideal,
and field inclusions preserve spectral norms and maximal ideals. The proof still
checks every admissible quotient pair. The empty scheme, identity inclusion,
H = Q_l, and ramified extensions require no extra hypotheses.

The first return (head 01fbc69aa) concerned concurrent Q11 API additions; the packet
preserves those additions. The current return (head 74d04997c85) concerned the three
missing consumer records above; all are now present. Current main has quarantined
DiagonalCoefficientReference, DiagonalTowerTraceCoefficients,
DiagonalTowerTraceModels and OrientationFiniteReductionTwists (rework 58206abfd).
Their archives, dependencies and DAG attachments remain untouched. The obsolete
sandbox adaptation of DiagonalTowerTraceCoefficients is excluded from this packet;
no library path is deleted, and there is no deleted.txt. There are no forced
adaptations of another group's module in the current active packet.

The previous session's delivery attempts each exhausted the 50-minute capacity
wait. The fresh first attempt reached compilation but stopped before push on a
tensor-module timeout. The explicit successful recheck and fresh axiom check above
provide new verification evidence for redelivery. No timeout limit or launcher
script was changed. A profiling probe was attempted; its timeout returned no
profiling details. No performance conclusion is drawn from it.

Fresh preflight found J7 now holds LisseLatticeCoefficientsSized. The final repair
excludes that module and its node from the packet, preserves its public signatures,
and puts all needed sheaf-condition constructions in private proved helpers of
PurTwistCoefficientTensor. There is no forced adaptation of a held module.

Reviewer correction (head 8258bb6d97bb): the "historical" consumer checks above did not hold
for this head. Unchanged PurTwistSheaves failed, because the old tied names were again
independent copies of the OfUniverses constructions. Unchanged PurTwistIntegralLocalModels
(`import all` of PurTwistCoefficientTensor) failed on the generalized private helpers.
The reviewer restored the abbrev specializations of head 01fbc69aaf63's fix and added
tied-universe private wrappers for `discreteCoefficientComparison` and
`constantSection_principal_quotient`. See the change record. All four downstream modules
of the adapted modules now compile.

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
