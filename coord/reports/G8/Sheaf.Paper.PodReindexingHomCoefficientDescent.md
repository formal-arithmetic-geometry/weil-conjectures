## What changed

Repair of returned head `3ed40cb0ebd`: the independent review passed, but the
landing rejected a reviewer override named
`g8-field-weil-shriek-sequential-elaboration.md`. The record is present in this
packet at `coord/changes/g8-field-weil-shriek-sequential-elaboration.md`.
The lander accepts its flat reviewer override as
`g8-field-weil-shriek-sequential-elaboration.change.md`, as verified against
`tools/batch_land.py` (`fixes`). The change record now documents both paths
explicitly, and its long alias-normalization paragraph is wrapped. The first
dry run then found three consumer regressions: QbarCurveDuality,
WeilMixedUpperBounds and WeilShriekShiftCompatibility could not synthesize the
Frobenius CommShift instances, although they compiled on main. Scope the field
operation barriers inside Finite, and restore the original geometric-fiber alias
status after that section. This preserves the final shift instances' original
lookup keys without changing their signatures or bodies. No DAG edit is needed. All retained sources were compared with current main; the existing node still
changes only `proof`, `proof_deps` and `proof_origin`. The initial five-module server
compile passed; after the instance-key repair, the final clean field shift module
compiles in 34.8 seconds. All three unchanged consumers now pass:
QbarCurveDuality 33.3 seconds, WeilMixedUpperBounds 6.2 seconds, and
WeilShriekShiftCompatibility 5.5 seconds. Their temporary verification copies
were removed. A subsequent dry run took 65.3 seconds on the item. Cache the existing
preadditive, pair-category and linear-Hom wrappers after the generic helpers,
and the full-subcategory category only in the common-stage portion; earlier
integral signatures still need to project underlying morphisms. These settings
are local, with no instance registration in the item. The clean item now compiles
in 39.3 seconds. The delivery is rebuilt on current `sheaf-dag`, retaining the
reviewed proof and elaboration repairs below. The final five-file server overlay
passes: normalization interface 1.3 seconds, semilinear consumer 21.2 seconds,
field shift data 48.3 seconds, item 54.8 seconds, and ContinuationB 52.0 seconds.

Prove `common_pair_permitted` in `Sheaf.Paper.PodReindexingHomCoefficientDescent`.
Two private, proved helpers identify the underlying integral stage object and
compare its pullback with integral pullback. At the input coefficient compositum,
apply `integral_pair_permitted` and transport constructibility through the
resulting internal-Hom isomorphism.

Add the proved interface `podCommonStageObjectNormalizations` in
`Sheaf.Paper.PodCommonStageObjectNormalizations`. It projects the three literal
object clauses of the existing unique operation specifications. The item's three
`copyObj` definitions use these proofs, so the new module is publicly imported.
The definitions retain their data definitionally by proof irrelevance. Their
existing signatures, and every other existing declaration signature, stay fixed.
Move the existing local irreducibility settings for the chosen common-stage
functors earlier, and use the new interface in the equality and tensor-transport
proofs. This avoids repeatedly unfolding the raw uniqueness specifications.
Use sequential elaboration, with the original transparency settings retained for
the existing integral comparison, common transposition and signed-shift proofs.

Update the item's proof steps and proof origin, and add the proved interface's node.
Repair of returned head f5f20330e9b: discard the obsolete adaptation of
`DerivedAutomorphismHomEvaluation`, its node edit, and its change record. F8's
Base/ContinuationA/ContinuationB split and all its proofs are retained verbatim.
ContinuationB receives only sequential elaboration and local operation barriers;
its unchanged original compile took 63.9 seconds, while the adjusted file takes
41.0 seconds against the final item. Its main re-export compiles in 5.5 seconds.
The item node is rebased on the current node, changing only its proof fields.

Repair `SemilinearFieldOperationLifts` by caching the category and operation
wrappers in a local section around the composition argument. Explicit types and
`unfold rationalDerivedPullback` let the private rational-composition proof
project the same specification without expensive type-class reconstruction.
The section closes before the Frobenius transport specifications. Public
statements, definitions, theorem proofs and imports in this consumer stay fixed.
The original consumer timed out after 120 seconds even against the published
library. The adjusted consumer compiles in 25.5 seconds with no errors or warnings.
All seven direct semilinear importers pass. CommonConstantUnitFrobenius takes
28.1 seconds, CommonFrobeniusSquareNormalization 5.6 seconds,
ConstructibleMateCoherence 42.0 seconds,
FrobeniusPullbackMonoidalAdjunctionCoherence 8.7 seconds,
CoefWeilExceptionalCompatibility 30.1 seconds, and SfLocalizationAllStages
10.3 seconds. FieldWeilShriekShiftData initially took 68.2 seconds; its final
clean compile takes 34.8 seconds after restoring the final instance contexts. It uses separate local contexts for the initial
shift lemmas and later operation proofs. Geometric-fiber aliases are normalized
after the instance caches are registered and restored before compact-support
normalization. All declarations, proofs and construction data remain verbatim.
The unchanged verification copies were removed from the sandbox.

The item maps the existing rational signed-shift equality with
`Functor.congr_map`, then applies rational_signed_shifts with parameters inferred
from the goal and discharges its hypotheses from the context. An isolated check
reduces this application from 7.44 to 1.05 seconds. The local completed-coefficient,
scalar-reduction and rational-operation barriers prevent repeated unfolding of
the corresponding constructions. The final item compiles cleanly in 48.7 seconds,
and ContinuationB compiles against it in 41.0 seconds. The proved normalization
interface compiles in 26.6 seconds. The unchanged F8 Base and ContinuationA compile in 7.3 and 38.7
seconds against this delivery. Change records:

- `coord/changes/g8-pod-common-stage-object-normalizations.md`
- `coord/changes/g8-pod-continuation-sequential-elaboration.md`
- `coord/changes/g8-pod-semilinear-composition-elaboration.md`
- `coord/changes/g8-field-weil-shriek-sequential-elaboration.md`

## Proved and sorry left

Closed 1 of the item's 21 original holes: `common_pair_permitted`.
Added 0 holes; split off 0 unfinished statements. The adapted ContinuationB
retains its 16 original holes; the adapted semilinear consumer and field shift
module each have 0 holes.
`WeilConjectures.podCommonStageObjectNormalizations` is fully proved.
The remaining 20 original item holes belong to
`lem-pod-reindexing-hom-coefficient-descent`:

- `ambient_reindex_scalar`
- `ambient_scalar_chain`
- `ambient_coordinates`
- `rational_transpose_existsUnique`
- `rational_signedShift_existsUnique`
- `rational_comparison_existsUnique`
- `integral_existsUnique`
- `integral_scalar`
- `rational_scalar`
- `integral_evaluation_transposition`
- `rational_evaluation_transposition`
- `rational_composition`
- `rational_pullbackShift_existsUnique`
- `rational_signed_shifts`
- `common_evaluation_existsUnique`
- `common_comparison_existsUnique`
- `common_evaluation`
- `common_transpose_existsUnique`
- `common_compositor_existsUnique`
- `common_composition`

## No longer needed

None. No original import or dependency is removed. The unfinished obligations
retain their original plans. The new proved interface uses the existing operation
definitions and their unique-existence specifications.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement discrepancy found. The prior packet incorrectly
assumed local reducibility settings could not affect exported instances. Lean
uses that local context when indexing an instance: restoring the contexts before
the final shift instances is required for downstream type-class inference. The prior consumer adaptation
was superseded by F8's independently landed split; it is removed in this repair.
The returned semilinear-consumer timeout also occurs against the published
library; the repair targets local elaboration of its composition argument.
The common-stage domain check can be made on underlying integral objects using the existing rational scalar object
and pullback/scalar compatibility formulas. Repeated elaboration of the raw
common-stage object specifications made the file exceed the compile limit;
the proved interface keeps those chosen functors abstract.

## New nodes

- `lem-pod-common-stage-operation-object-normalizations`: proved object-normalization
  interface for common-stage pullback, tensor and internal Hom; no `sorry`.

## Related modules compiled before delivery

33 related module(s) compiled against this delivery by deliver3.py: 32 OK, 1 SLOW.

```json
{"capped": false, "direct": 32, "left_out": 0, "own": {"Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationB": "26f1682872233b77da7f63ae8496a94cdfdecb31", "Sheaf.Paper.FieldWeilShriekShiftData": "8339b4e3e8b675fccaec54fc404987de96ebcd23", "Sheaf.Paper.PodCommonStageObjectNormalizations": "d90cb2b2a4118acedf5ac70e359d53cbc2bf2d95", "Sheaf.Paper.PodReindexingHomCoefficientDescent": "4b6076fc6d4d550fd8781d01d110651fd3b17b28", "Sheaf.Paper.SemilinearFieldOperationLifts": "6d6a2d120d28b0ce7b932dc7e4a3827dcf34daf2"}, "results": {"Sheaf.DeligneLaumon.QbarCurveDuality": {"hash": "698919cd1c65cfbd98e0a94220b347ea95489629", "status": "OK"}, "Sheaf.Paper.AdmissibleHomSubstitution": {"hash": "87f9546cb0ed2bfea176bcd0e50abc3cf05aab40", "status": "OK"}, "Sheaf.Paper.CommonConstantUnitFrobenius": {"hash": "35e0636842df571094c943c61fea9cbff1703952", "status": "OK"}, "Sheaf.Paper.CommonFrobeniusSquareNormalization": {"hash": "2c3f270b54586ad4051e12940525a81f48e9025c", "status": "OK"}, "Sheaf.Paper.CommonStageCurveWeilMiddleExtension": {"hash": "3b4e1e3e0a0364c5e9d137436e1b5da790a42c3a", "status": "OK"}, "Sheaf.Paper.CompactSupportProjectionFormula": {"hash": "9d8a08bf4a6d4025a7ffc9ce8b51e70bcc8ad44a", "status": "OK"}, "Sheaf.Paper.ConstantPurityFrobeniusSquare": {"hash": "57e1afb9cc6da75a28f05ec3856b5b1c77ee5d7b", "status": "OK"}, "Sheaf.Paper.ConstructibleMateCoherence": {"hash": "dfb4c0c8b6fc0f43ca770d197a9725e4dad3d614", "status": "OK"}, "Sheaf.Paper.DerivedAutomorphismHomEvaluation": {"hash": "d9b824a9ef213fa3e1d5aa65989f86a8ff078cf4", "status": "OK"}, "Sheaf.Paper.DerivedAutomorphismHomEvaluationBase": {"hash": "c27cd2f10e04680a2a135350be82c472640d2bcf", "status": "OK"}, "Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationA": {"hash": "1c517655a7b96fc9a0945de6ef60a8654b3ecef6", "status": "OK"}, "Sheaf.Paper.DlConstantFieldCharts": {"hash": "96eb0dac8c43b117a4270c948af4c6a35cb1e350", "status": "OK"}, "Sheaf.Paper.FixedPairTruncationCohomology": {"hash": "2d664b1e22e47b4d2c2480150ffe682699b01589", "status": "SLOW"}, "Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence": {"hash": "3aaa50f38e9b24cd916a6add7f1d5a39a7607c49", "status": "OK"}, "Sheaf.Paper.PointWeilPairingCoordinates": {"hash": "bfa154bdcbd23685edbb6c734c2db5dbd1617508", "status": "OK"}, "Sheaf.Paper.PointWeilPairingRealization": {"hash": "2e869adba9a1186bcb44abe64fa91095dd13072b", "status": "OK"}, "Sheaf.Paper.RationalPurityExchangeEndpointData": {"hash": "cb692b8d3529fcd7b913c1b14163ca742d543822", "status": "OK"}, "Sheaf.Paper.RationalPurityExchangeEndpoints": {"hash": "2e0b34e6f560e98f044510a932036f7ab2880263", "status": "OK"}, "Sheaf.Paper.RationalPurityLocalizedFamilyData": {"hash": "54c1855ce804b6e14d7e2842124fd98c952fc87d", "status": "OK"}, "Sheaf.Paper.RationalWeilPurityNaturalityMate": {"hash": "bea9b1ea85e14d4d7c780bf521d6174ea17668f6", "status": "OK"}, "Sheaf.Paper.ResidueCompatiblePullbackFrobenius": {"hash": "3809fb3bf7cf447f73328d73f4943b7fdf05fed4", "status": "OK"}, "Sheaf.Paper.SfLocalizationAllStages": {"hash": "935dd63c3231a8f15ee7594a37135467b4c94250", "status": "OK"}, "Sheaf.Paper.SfNormalizedRationalClosedComparison": {"hash": "f0a2e43fee3fcdf3ba57bfee56345f81e9d4c432", "status": "OK"}, "Sheaf.Paper.TwistedPullbackSquareMaps": {"hash": "fd199a6d0a935f08a9814a1358adc6cb766cff3e", "status": "OK"}, "Sheaf.Paper.WeilMixedUpperBounds": {"hash": "beffc77815e590ac15c5a9f34f8da5e0c45663a5", "status": "OK"}, "Sheaf.Paper.WeilShriekShiftCompatibility": {"hash": "248c00fafaba791c12d8863379c86a237f856528", "status": "OK"}, "Sheaf.Paper.ZlWeilShriekCoefficientLongExact": {"hash": "540a26ecffa5f3eb4f05a4ac668de5753cf5a970", "status": "OK"}, "Sheaf.SecSmoothPurity.RationalPurityLineComparisons": {"hash": "7dfea4a2aa9ca58786b61db04994341c85d15175", "status": "OK"}, "Sheaf.SecSmoothPurity.RationalPurityTraceCoherence": {"hash": "0091913289529cd60ce8938cc38e96ee7a2ce7a4", "status": "OK"}, "Sheaf.SixFunctors.CoefWeilExceptionalCompatibility": {"hash": "add67b0187599655d011c82c04faaaef8fca3b1e", "status": "OK"}, "Sheaf.SixFunctors.IntegralOperationShiftData": {"hash": "d79d356f094f2fb511f9e0bde2182c3cf96581b4", "status": "OK"}, "Sheaf.SixFunctors.OpenClosedWeilMateData": {"hash": "9630df99472a0f41c00bc0768460c09c74bc07ae", "status": "OK"}, "Sheaf.SixFunctors.SupportedWeilMateLift": {"hash": "dd593ad91ee5296e4c3c0ffc281f23c784a54726", "status": "OK"}}, "seconds": 180, "time": "2026-10-28T04:49:53+0800", "transitive": 1, "version": 1}
```

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
