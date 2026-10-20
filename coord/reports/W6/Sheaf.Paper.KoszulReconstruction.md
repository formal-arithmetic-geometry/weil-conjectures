## What changed

Repaired return C-373e2 point by point. `KoszulReconstructionComparison` now has a
complete proof from `completedKoszulQuotientRoosAugmentation` and
`ExactProductsRoos.comparisonIso`. It restricts to K-flat representatives using
right-fraction density, forms the normalized comparison, descends it along the
restricted localization, and reflects its invertibility by fully faithful
precomposition. The augmentation unit equation and the normalized Roos equation
identify the descended unit with the one characterized by
`reconstructionCompletionUnit_exists`. Generic proved private lemmas normalize the
homotopy/cochain comparison maps without unfolding the coefficient constructions.

Both localization assembly theorems are proved from Mathlib. The target theorem
has its original signature and follows by composing isomorphisms. Its docstring
and `prop-weil-pbc-koszul-reconstruction` proof/proof_deps now describe this proof.
The comparison node likewise records the actual dependencies.

`KoszulReconstructionModels` preserves the original public imports, public model
signatures and instance attributes. Its generic helpers remain private. The unit
specifies the canonical `Localization.liftingLift` instance explicitly; no chain
map, coefficient object, completion choice or target meaning changes. The product
naturality proof uses a proved private tensor square and the existing transition
endomorphism API. The change record is
`coord/changes/W6-koszul-model-extraction.md`.

## Proved and sorry left

Original item hole closed: `AlgebraicGeometry.Scheme.koszulReconstruction` (1 of 1).
The packet retains exactly one added hole:
`AlgebraicGeometry.Scheme.completedKoszulQuotientRoosAugmentation`, node
`lem-weil-pbc-completed-koszul-quotient-roos-augmentation`, in its own module. This
is the strictly smaller strict chain augmentation/quasi-isomorphism result that
the return explicitly permits to remain sorry. Relative to the original item,
this is a decomposition: one local hole closed and one local hole added. Closure
progress is left to the ledger, rather than inferred from these local counts.

The repair also closes `AlgebraicGeometry.Scheme.koszulReconstructionComparison`,
`AlgebraicGeometry.Scheme.localizationNatTransIso`, and
`AlgebraicGeometry.Scheme.localizationUnitEq` from the retained packet. No new
holes were added by this repair. `CategoryTheory.ExactProductsRoos.comparisonIso`
and every model/helper declaration in this packet are proved. There is no sorry
inside a definition, no new axiom, and no restatement of the comparison left sorry.

Validation: all six packet modules compile together on the server with no warnings
or errors. The comparison takes 51.5 seconds under the unchanged 60-second limit.
All sixteen current and quarantined direct importers were compiled unchanged against
the packet artifacts. Fourteen pass. The two failures reproduce the baseline missing
names: `FinitePerfectModelsCompatible`, `HasUniformFinitePerfectModels` and
`ringedSiteDerivedRestrictionOfUniverses` in `FinitePerfectAdicRealization`;
`LocallyClosedStratification` and `UniformAdicTowerData` in
`ReconstructionUniformTower` (which also reaches the same pre-existing heartbeat
limit at line 560). Their holders are B3 and B7. No consumer adaptation is necessary.
The previously timed-out `OrderedExchangeCoefficientComparison` passes with this
packet. The public import and instance movement introduces no observed regression.

| Direct importer | Baseline | With packet |
| --- | --- | --- |
| Sheaf.Paper.CompletedAdicLevelwiseIsomorphismCones | pass | pass |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | pass | pass |
| Sheaf.Paper.CompletedCompactSupportExchange | pass | pass |
| Sheaf.Paper.CompleteCompactSupportProetale | pass | pass |
| Sheaf.Paper.FinitePerfectAdicRealization | existing missing declarations | same missing declarations |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | 60s timeout | pass |
| Sheaf.Paper.OrdinaryCompletedIntegralPullback | pass | pass |
| Sheaf.Paper.RationalCompactSupportCoefficientCoherence | pass | pass |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | pass | pass |
| Sheaf.Paper.CompletedCoefficientPushforwardComparison | pass | pass |
| Sheaf.Paper.ReconstructionUniformTower | existing missing declarations | same missing declarations |
| Sheaf.Paper.AdicLisseCohomologyCalculus | pass | pass |
| Sheaf.Paper.IntegralPullbackCompletedComparison | pass | pass |
| Sheaf.Paper.IntegralCanonicalTruncations | pass | pass |
| Sheaf.Paper.CompletedReductionSquare | pass | pass |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | pass | pass |

## No longer needed

The target module drops its direct proof imports of
`CompletedKoszulQuotientRoosAugmentation`, `ExactProductsRoosComparison` and
`RightDerivedFunctor.ShortExactPullback`; it needs only the proved comparison as a
private proof import. Its unused local sheafification instances are removed.
The comparison drops the redundant direct `ExactProductsRoosComparison` import,
which is publicly available through the augmentation module. Its augmentation and
`ShortExactPullback` imports are now actually used: the former constructs the
comparison, and the latter supplies the right-derived-limit unit, naturality and
K-injective normalization. The generic assembly module needs only Mathlib's
localization API and no longer imports the completed models.

The earlier reconstruction route through
`lem-weil-pbc-constant-completion-equivalence` / `Sheaf.Paper.ConstantCompletionEquivalence`
and `Sheaf.Paper.IntrinsicCompletionCompleted` is not used by the new proof.
`CompletedConstantSheafReduction` is no longer a direct proof import here, but its
node remains a dependency of the retained augmentation and is not withdrawn.
All model constructions, the K-flat resolution/density inputs, and the unit's
strict quotient/Koszul route remain needed. No source-library declaration, DAG
node, quarantined source, or module is deleted. Absence from this item's import
closure is not claimed as global withdrawal.

## Where the brief, the DAG or earlier work was wrong

The returned comparison hole merely repackaged the item. It has been replaced by
real descent and unit-normalization proofs, not another interface with the same
conclusion. The earlier report also misdescribed the unfinished glue as smaller
results: all that glue is now proved. The parent node previously retained proof
steps for the older constant-completion route; its proof and dependencies now
agree with the Lean term.

The current source has one live direct importer and fifteen preserved quarantined
direct importers, so the consumer check includes sixteen files. Quarantine is not
interpreted as withdrawal. Baseline errors in quarantined consumers are distinguished
from any failure caused by moving the public imports or instance attributes.

The first preflight of this repair found two metadata errors in the assembly node:
Loogle and LeanFinder counted as one search kind, so a LeanSearch record was still
required, and the stored signature omitted the declaration's explicit namespace.
The missing search has now been run through msearch.py, all recorded assembly
searches have matching execution records, and the signature is copied exactly
from the compiled declaration. No Lean change was needed for these corrections.

## New nodes

`def-weil-pbc-koszul-reconstruction-models` records the existing model constructions
and their unchanged public API in the extracted module; it has no holes.

`lem-weil-pbc-exact-products-roos-comparison` records the proved generic normalized
Roos comparison with the right-derived inverse limit.

`lem-weil-pbc-completed-koszul-quotient-roos-augmentation` records the sole retained
strictly smaller hole, with its source, complete proof in words, and exact chain
unit equation. Edge cases r = 0, the zero ideal, the unit ideal, and the empty base
site are consistent with the construction.

`prop-weil-pbc-koszul-reconstruction-comparison` records the now-proved natural
comparison and its canonical-unit equality.

`lem-weil-pbc-koszul-localization-assembly` records the two proved generic
localization helpers. Its dependencies now match its Mathlib-only proof.

Change record: `coord/changes/W6-koszul-model-extraction.md`.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
