## What changed

Rebuilt `primitiveQuotientScalarModelExistence` by descending the actual ordinary
quotient scalar comparison through the good-complex localization. Its sequence
K-flatness helper and the final normalization calculation are complete proofs.
`primitiveQuotientScalarModelRealization` keeps its signature and projects the
normalized model. The only new assumed step is the ordinary balanced tensor-tower
comparison, before derived realization, Roos comparison or localization.

Corrected `IsIntegralComparisonScalarNormalized` to require the existing
`IsIntegralComparisonPresentationCoherent`, as the reviewed pullback predicate
already does. The generator and Roos equations remain identical. Uniqueness uses
a canonical coherent presentation; transport carries its coherence through the
left-adjoint unit identity.

Repaired return C-ff2c4, head ff2c4697e: restored the entire original Roos block
in `IntegralComparisonRealizationModels`, including its private generic theorem,
unique map construction, normalization predicate and model. Removed the unlanded
`IntegralComparisonRoosModel` module and node proposal, its dependency entries,
and its extraction text. Restored the five declaration attachments and original
Roos proof step. The reviewer's concurrent paired timings (30.1 seconds with the
block in place, 31.1 seconds extracted) show that extraction was unforced.
Also restored the original private `restriction_exact` proof and removed its
extra proof import and node dependency. Added T1/date to the shared node's
statement-change record. All other accepted repairs are retained.
Reviewer correction (2026-10-28): the elaboration settings added to the shared
module are withdrawn. These were the explicit ring map and e.functor arguments,
the file-level respectTransparency options and the local irreducible attributes.
They were unforced: in paired concurrent compiles the published module took
31.2 s, the delivered module 30.5 s, and the published module plus only the
coherence hypothesis 31.2 s. The shared module now differs from live by that one
line.


Repaired every point of return C-26e70, head 26e70c300:

- Adapted D3's newly landed `ScalarModelUnit` by passing its existing `hc` to
  `bEE.normalization P C e κ hp hc`, and recorded D3 in the Users table.
- Rebased `ScalarModelIteratedStrictCalculation` on E9's completed live proof
  f3f64. Only the `hcoh` binder and its normalization argument are added. Its node
  changes only statement fields; `proof`, `proof_deps`, `reviewed_proof`, and
  `proof_origin` are the live values. Associativity supplies this coherence.
- Withdrew `IntegralComparisonRoosComparison`, restoring both original types.
- Withdrew the extractions from `CoherentQuotientOrdinaryLift`,
  `IntegralTowerInverseImageUnit`, `IntegralComparisonCounitCharacterization`,
  and `OrdinaryQuotientPullbackTowerComparison`, with their four proposed modules
  and nodes. Restored those consumers and `PrimitiveQuotientRealizationComparisons`.
  These proposed helpers were never present in the live tree; no existing node
  or module is deleted.
- Preserved existing `proof_origin` provenance, appending the necessary route
  explanation where the proof route changes.

The false arbitrary-realization normalization helper is retired, with its node
preserved and `lean: null`. No source-library module, Challenge statement, or unit
route is changed. Change record:
`coord/changes/T1-scalar-presentation-coherence.md`.

## Proved and sorry left

Zero holes remain in the item module. Its original one hole,
`WeilConjectures.primitiveQuotientScalarModelNormalization`, was false and is
retired, not proved. The existence and realization theorems now have complete
proofs from their imported declarations. The private K-flatness helper is proved.

Exactly one new hole remains:
`WeilConjectures.ordinaryQuotientScalarTowerComparison`, node
`lem-trf-ordinary-quotient-scalar-tower-comparison`, in
`Sheaf.Paper.OrdinaryQuotientScalarTowerComparison`. It states only the ordinary
balanced tensor-tower isomorphism and strict generator formula. This is a
strictly smaller step of the corrected construction. Counts: 0 of 1 original
holes proved, 1 false hole retired, 1 strictly simpler hole added; no definition
holes. E9's `scalarModelIteratedStrictCalculation` is preserved as proved, with
zero holes; its proof is not claimed as this worker's achievement.

All eight retained Lean modules compile cleanly. With the reviewer's minimal shared module, all eight modules compile (shared
32.6 s, item 31.6 s). The other modules reuse their successful artifacts;
their earlier full timings were: E9 calculation 36.9 seconds, D3 unit 22.5,
associativity 9.4, ordinary comparison 3.4, uniqueness 20.4 and transport 10.3.
The packet has seven nodes and exactly one named theorem hole. No definition
contains a hole. The unchanged direct importers were checked on temporary live
copies, then removed. The original pullback consumer had already passed the
reviewer's 51-second check; its new local timing checks and the unrelated live
new-generator timing issue are recorded below. All other importer checks passed,
including the new finite-evaluation factors (49.4 seconds), scalar association
(0.1 seconds), and integral-operation shift data (27.1 seconds).

## No longer needed

The restored shared module no longer imports the proposed
`Sheaf.Paper.IntegralComparisonRoosModel`, nor the optional private-proof import
`Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`. Its original
public imports and private restriction-exactness proof are preserved.

Removed proof imports `Sheaf.Paper.CoefficientExtensionReductionModel` and
`Sheaf.Paper.TransportedReductionScalarNormalized`, and private helpers
`globalUnit_of_residueUnits` and `scalarModelIso'` from the item.
The existence proof no longer uses the false normalization node
`lem-trf-primitive-quotient-scalar-model-normalization`,
`lem-pur-coefficient-extension-reduction-model`,
`stage3-pur-reduction-skeleton-exists`,
`stage3-pur-extension-strict-representatives`, or
`stage3-trf-transported-scalar-normalized`. Other consumers and all adopted source
statements remain intact. These are local route prunings, not global withdrawals.
The finite ordinary association and successor statements remain relevant to the
new ordinary comparison and are not claimed pruned.

The returned public Roos alias and the unforced Roos extraction module/node are
withdrawn. The following earlier unlanded extraction
proposals and their modules are removed from the packet:

- `lem-trf-coherent-quotient-section-unit` / `CoherentQuotientSectionUnit`.
- `lem-trf-integral-sequence-direct-image-equivalence` /
  `IntegralSequenceDirectImageEquivalence`.
- `lem-trf-normalized-roos-adjunct` / `NormalizedRoosAdjunct`.
- `lem-trf-ordinary-quotient-pullback-evaluation` / `OrdinaryQuotientPullbackEvaluation`.

Their original consumers and original proof dependencies are preserved verbatim.


## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the retired helper normalized every realization isomorphism,
although multiplication by a nonidentity coefficient unit changes its comparison
while the generator formula fixes it. The realization must be constructed with
its normalization. This is not counted as proving the false assertion.

Finite derived evaluations alone do not determine the whole-system comparison.
The scalar predicate and the iterated auxiliary hypothesis repeated the reviewed
pullback defect. Their explicit correction requires whole-system adjunction
coherence, available for every good complex from the canonical presentation.
The change record gives the invisible-twist example and exact old/new signatures.

The prior packet was stale against E9's proof and D3's new scalar-unit proof.
Its replacement of E9's proof by a hole and its claim that ScalarModelUnit needed
no adaptation were incorrect. Both are repaired against live sources. The
reviewer's paired timings showed that the extractions and PQRC local attributes
were unforced; all are withdrawn, rather than retaining the earlier performance
justification.

## New nodes

`lem-trf-ordinary-quotient-scalar-tower-comparison`, module
`Sheaf.Paper.OrdinaryQuotientScalarTowerComparison`, is the ordinary balanced
tensor isomorphism from scalar extension of an actual strict quotient complex to
the direct quotient scalar tower, with its local generator formula for any strict
isomorphic presentation. No calculus, derived realization, localization, K-flat
computation, or Roos normalization occurs in its hypotheses or conclusion. Its
source is balanced association (Stacks 03D7/03EK) on the sequence site (0941).
The argument includes zero complexes, level zero, identity and ramified embeddings
without division. It has a full proof in words and one named theorem hole.

## Forced adaptations

`Sheaf.TraceFormula.ScalarModelUnit` (D3): return C-26e70 reports the original
line-90 error as "rcases on IsIntegralComparisonPresentationCoherent → …".
After the predicate correction, `bEE.normalization P C e κ hp` is still a
function. Its existing canonical presentation supplies `hc`; passing it yields
the existential the unchanged proof destructures. The only edit is adding `hc`
on that line. Every signature, visibility, import and other proof line is live.

`Sheaf.TraceFormula.ScalarModelIteratedStrictCalculation` (E9): the same missing
coherence argument would leave `bEL.normalization P C e κ hC` a function. The
review expressly requests the extra `hcoh` hypothesis and argument; these are the
only Lean edits to the live file. Its completed proof, imports and node proof
metadata are preserved. `ScalarModelAssociativity` obtains that hypothesis from
the canonical coherent presentation, preserving its public signature.

Temporary consumer type annotations, tactic-linter settings and proof refactors
were all withdrawn. The pullback consumer's timing experiments did not establish
a reliable improvement; its original source is preserved as the review requests.
The new live `IntegralPullbackStrictFiniteGenerators` timed out both with this
packet (92.2 seconds) and against the unmodified live shared module (64.7 seconds;
control result 1034f4b00b679e6c608c7563). It does not use scalar normalization.
No adaptation is forced there, and its source is not included in the delivery.

All temporary Lean copies, timing controls and profiling experiments are removed.

## Related modules compiled before delivery

Not checked: the delivered modules did not compile in the overlay (service fault); the landing compiles the related modules.

```json
{"capped": false, "direct": 36, "left_out": 0, "own": {"Sheaf.Paper.IntegralComparisonRealizationModels": "1cd460b746400390901776d0d538d4e5dfd7f4d8", "Sheaf.Paper.OrdinaryQuotientScalarTowerComparison": "df05c1a471ba5445949613de11fbac2bc84b2059", "Sheaf.Paper.PrimitiveQuotientRealizationsTransport": "1a8766ebcd360a0d7b4744815abf572816a5fcec", "Sheaf.Paper.PrimitiveQuotientRealizationsUnique": "6e6ba0e93b4069668a933e2f2dd0936c4ac0756f", "Sheaf.Paper.PrimitiveQuotientScalarModelExistence": "2d503774b9e9372f25db9413c96f341963859829", "Sheaf.TraceFormula.ScalarModelAssociativity": "0f4a73b08c167cb3b8d31051f888cabe480781bd", "Sheaf.TraceFormula.ScalarModelIteratedStrictCalculation": "479f3e7a7c7cec313d68222b394f4e34595c0ef6", "Sheaf.TraceFormula.ScalarModelUnit": "f89e51f389a0416824798292d71e864addb838d4"}, "own_failed": ["Sheaf.Paper.IntegralComparisonRealizationModels", "Sheaf.Paper.OrdinaryQuotientScalarTowerComparison", "Sheaf.Paper.PrimitiveQuotientRealizationsUnique", "Sheaf.TraceFormula.ScalarModelIteratedStrictCalculation", "Sheaf.TraceFormula.ScalarModelUnit", "Sheaf.Paper.PrimitiveQuotientRealizationsTransport", "Sheaf.Paper.PrimitiveQuotientScalarModelExistence", "Sheaf.TraceFormula.ScalarModelAssociativity"], "results": {}, "time": "2026-10-28T01:24:52+0800", "transitive": 0, "version": 1}
```

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
