## What changed

Repaired the ordinary normalization gap identified by the H4 audit. The unclaimed
`Sheaf.Paper.NativeWeilClosedModels` predicate `NativeOrdinaryTensorModels` now
retains the canonical localization tensorator and its signed balanced total
comparison. The added clause is a concrete representative normalization, not an
associativity hypothesis. The new, fully proved
`native_ordinary_canonical_tensor_representatives` retains the actual explicitly
constructed model and proves the required summand equation. The unclaimed ordinary
existence constructor is adapted to retain this data. The change record is
`coord/changes/T4-native-ordinary-tensor-normalization.md`; it gives the exact old
and new definitions and all users. The core node records the semantic change and
its citer audit. No adopted source-library declaration or target signature changes.

The assigned theorem keeps its signature text. Its proof first identifies the
supplied ordinaryModel with the canonical witness on K-flat pairs: curry a
K-injective resolution of the tensor total, apply both normalization equations,
then cancel the localized resolution map. This calculation is proved privately
inside the item, using the existing normalized-map calculation. The independently
claimed DAG node for ordinary model uniqueness is not changed or duplicated.

The residual geometric equations are restricted to K-flat representatives and
separated into associativity, and one common unit with both unit equations and
symmetry. Each is a strict part of the argument. The item contains the complete
extension to arbitrary derived objects: A.localization gives essential
surjectivity, and private naturality and isomorphism-cancellation calculations
transfer each representative equation. No residual all-object coherence theorem
under another name is introduced. The DAG proof is updated to this argument.

## Proved and sorry left

Original hole removed:
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_derived_square_native_coherence`.
Its body now contains no sorry. This is a decomposition, not a completed proof of
the geometric coherence theorem: one original hole is replaced by two strictly
smaller representative obligations, so the hole change is minus one net closure.

The delivery adds exactly these two sorry declarations, each in its own module
with a source, complete proof in words, and matching node:

- `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_associator_representatives`
  (`lem-sf-native-weil-tensor-ringed-associator-representatives`): associativity
  only on three native K-flat complexes, with the ordinary model already fixed
  to the canonical localization normalization.
- `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_unit_symmetry_representatives`
  (`lem-sf-native-weil-tensor-ringed-unit-symmetry-representatives`): one unit
  comparison, the two unit equations on K-flat representatives, and symmetry on
  representative pairs; no associativity or all-object extension.

Fully proved new public theorem:
`AlgebraicGeometry.ProEtaleWeilSheaf.native_ordinary_canonical_tensor_representatives`.
The normalization predicate and the adapted ordinary constructor have zero holes.
The private fixed-adjunction uniqueness and all isomorphism transport calculations
are also proved. No sorry is added inside a definition or private declaration.

Validation: all six delivery modules and 35 temporary consumer copies compiled
in import order against the repair, covering every direct core importer and all
current modules that mention the changed predicate. Every file completed within
60 seconds; the assigned module took 35.7 seconds and the new canonical constructor
52.7 seconds. The temporary copies were removed after checking. The local
heartbeat-budget warning is addressed by an explanatory comment.

The statements were checked on zero complexes, degree-zero units, complexes in
arbitrary positive or negative single degrees, and the empty-site case. The
summand normalization uses all integer degrees. Its sign is precisely the
existing signed total interchange; in the associator equation the signs agree by
pq+(p+q)r=qr+p(q+r), and the unit sign is one.

## No longer needed

Removed the proof-only import `Mathlib.Tactic.NormNum` and the private scalar
obstruction calculation from this item after repairing its underlying interface.
No public declaration or source-library declaration was removed.

The original proof route's direct inference from ringed TensorComparison
coherence to native t coherence is replaced by normalized representative
equations and proved all-object descent. The original ringed descent, structure,
model and ordinary-data nodes remain needed for the supplied data or the
representative argument; none is claimed globally pruned. The item keeps its
three public imports because its statement uses their interfaces. The new proof
imports are private. No library module is withdrawn and no unit statement or
realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The H4 audit correctly distinguished adjunction normalization relative to arbitrary
chosen Hom representatives from normalization of the tensor model to the fixed
monoidal localization. Signed symmetry alone cannot supply associator coherence.
The former predicate omitted the latter normalization even though its concrete
constructor already used it. The repair retains that actual construction and
proves its new clause, rather than assuming the desired coherence equations.

This changes the meaning of the intermediate predicate explicitly: hypotheses
using it are strengthened, and its existence conclusion is strengthened with a
proved constructor. The semantic review of the affected native closed interfaces
is reopened. The exact target declarations do not mention the predicate and their
signatures stay unchanged. The node's statement_change audits every current citer.

The existing ordinary-model-uniqueness node is claimed independently and has no
Lean attachment in this snapshot. Its elementary argument is written as a proved
private helper here, rather than importing an unavailable theorem, altering its
claim, or adding a duplicate public node.

## New nodes

`lem-sf-native-ordinary-canonical-tensor-representatives` exposes the signed
balanced total comparison and the canonical localization formula of the existing
explicit ordinary tensor model. It is fully proved, with no additional
normalization axiom. Its source is Stacks 06YS, 06YT and 0FPT. It strengthens the
existing representative existence interface precisely where the repaired
predicate needs the retained construction.

`lem-sf-native-weil-tensor-ringed-associator-representatives` isolates the
associator calculation on three K-flat native complexes after canonical ordinary
normalization has been proved. Its source is Stacks 06YU and 0FPT and the current
blueprint's native tensor transport. The final localization and naturality
extension is proved in the item, outside this residual statement.

`lem-sf-native-weil-tensor-ringed-unit-symmetry-representatives` isolates the
common degree-zero unit and signed swap calculations on K-flat native complexes.
It uses the same sources and leaves the all-object extension to the proved item.
It preserves a single common unit for both equations and includes no associator.

The recorded LeanSearch, LeanFinder, Loogle and Mathlib grep searches found
monoidal localization and generic associator tools, but no exact statement for
these native normalized representative comparisons. The existing explicit
ordinary construction and generic naturality argument were reused. The broader
native geometric tensor comparison already imports this item; importing it here
would create a cycle. The generic ringed-equivalence descent theorem requires
coherent total comparisons as input, so it does not supply the missing native
representative calculation. Change record:
`coord/changes/T4-native-ordinary-tensor-normalization.md`.

## Related modules compiled before delivery

35 related module(s) compiled against this delivery by deliver3.py: 35 OK.

```json
{"capped": false, "direct": 32, "left_out": 0, "own": {"Sheaf.Paper.NativeOrdinaryCanonicalTensorRepresentatives": "826399baf5c24c7fe5393cd26c90694f4b687531", "Sheaf.Paper.NativeOrdinaryClosedTensorModels": "b9b6c05f540e18d139e9af860294477c9f5aec8c", "Sheaf.Paper.NativeWeilClosedModels": "e498beba53d70e3edfed26fa0fdd6812cefe2857", "Sheaf.Paper.NativeWeilTensorRingedAssociatorRepresentatives": "e44d605d15b4756a2b724cc2a559b2d32a5d4019", "Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNativeCoherence": "3c0cf26550499fad857ebcf50871dbfc8f2f0b8d", "Sheaf.Paper.NativeWeilTensorRingedUnitSymmetryRepresentatives": "4df6741a9e8ed1d1ba4d95b15105b414d496b68d"}, "results": {"Sheaf.Paper.NativeClosedTransposition": {"hash": "c08beb033f9a8abd1ac148cb79fa48fc1c31eb0b", "status": "OK"}, "Sheaf.Paper.NativeCoefficientTensorComparison": {"hash": "c5259a0ddf2c297c354eea488b71dbfe003a7b67", "status": "OK"}, "Sheaf.Paper.NativeGeometricTensorComparison": {"hash": "57d1f5c607ebccaab8e4fbd820137440f5f9b05a", "status": "OK"}, "Sheaf.Paper.NativeHomEvaluationSquareAllSources": {"hash": "ad36cce87fdb7429d9a552067e33c7cd6a3ab90b", "status": "OK"}, "Sheaf.Paper.NativeHomRepresentativeExistence": {"hash": "63e4311d946846e1280dde2616d1d481f0ff9631", "status": "OK"}, "Sheaf.Paper.NativeHomRepresentativeUniqueness": {"hash": "c5f0c115480a14fb4f7d3a3d4ec0b9ddf61d188b", "status": "OK"}, "Sheaf.Paper.NativeNormalizedOrdinaryHom": {"hash": "3ffcb4fe92c4e109510b024a9203ecb2426fc89c", "status": "OK"}, "Sheaf.Paper.NativeOrdinaryRepresentativeCurrying": {"hash": "282b71ca8030e90f946c00393043d48b9eb401d4", "status": "OK"}, "Sheaf.Paper.NativeOrdinaryTensorIdentification": {"hash": "204f923ae81f89858fa527abc59a442a66848622", "status": "OK"}, "Sheaf.Paper.NativeOrdinaryTensorModelNaturality": {"hash": "77e6b31d3fcba7b416bcb91d589a8d6c99e46787", "status": "OK"}, "Sheaf.Paper.NativeOrdinaryTensorModelResolutionData": {"hash": "1d8c0806bd1ed91d5fdc588b24dca8e5c96bbf83", "status": "OK"}, "Sheaf.Paper.NativeOrdinaryTensorModelResolutionExtension": {"hash": "24138241f806d3427c32f3e2d624e5f1e1001468", "status": "OK"}, "Sheaf.Paper.NativeOrdinaryTensorModelResolutionNaturality": {"hash": "928b39b27b73923d9285702475ae7e505f617cf2", "status": "OK"}, "Sheaf.Paper.NativeOrdinaryTensorModelResolutionRoof": {"hash": "505aff4689b95aa5b8db2bafb7448a352fa84ab4", "status": "OK"}, "Sheaf.Paper.NativeOrdinaryTensorModelResolutionTransport": {"hash": "5e1cd5ef90a69d648f97c2ea1906f5867de8c852", "status": "OK"}, "Sheaf.Paper.NativeOrdinaryTensorRepresentatives": {"hash": "35a8ead89847ddace2c50378299dc5d8a65baf34", "status": "OK"}, "Sheaf.Paper.NativeWeilClosedForgetful": {"hash": "8928dff1f79cb57697790300f32209f6cbb2b07f", "status": "OK"}, "Sheaf.Paper.NativeWeilHomClosedStructure": {"hash": "9fc1ef0dba218034b59e9f97473592613c8127b6", "status": "OK"}, "Sheaf.Paper.NativeWeilHomRightAdjoint": {"hash": "a63ff976f6178915d67df471c9e2b07d5b80ea37", "status": "OK"}, "Sheaf.Paper.NativeWeilInverseHomSquare": {"hash": "1a331881a1c8f36bfd175824d81d08c1388efa02", "status": "OK"}, "Sheaf.Paper.NativeWeilRingedPresentation": {"hash": "dcf42135413cd36040f7b16e202820324a20e9bf", "status": "OK"}, "Sheaf.Paper.NativeWeilRingedTensorModel": {"hash": "b885547c957187100d6b62ed74b9d535bda7438a", "status": "OK"}, "Sheaf.Paper.NativeWeilRowHomComparison": {"hash": "5957f7361abf42edb43d21f74eb852cbcc227934", "status": "OK"}, "Sheaf.Paper.NativeWeilTensorAdjoints": {"hash": "f50421d13a10b8a56f6d6dd4c8871f284d56f02a", "status": "OK"}, "Sheaf.Paper.NativeWeilTensorCoherence": {"hash": "6fff0b698607d9d90a2ac9f358206aeffdcc219c", "status": "OK"}, "Sheaf.Paper.NativeWeilTensorConstraintLifts": {"hash": "abf2760ca590de4f829154848e909635f6a577cb", "status": "OK"}, "Sheaf.Paper.NativeWeilTensorGeometry": {"hash": "a06aaf9f6abd6a1a704db0f1e71c9ad390f2e9c8", "status": "OK"}, "Sheaf.Paper.NativeWeilTensorLift": {"hash": "6484a42c93025fb2c74b4ed1e3da7971696bc27f", "status": "OK"}, "Sheaf.Paper.NativeWeilTensorPresentation": {"hash": "4a3b30321edf63cd2da366b20b8c096fcad9ab34", "status": "OK"}, "Sheaf.Paper.NativeWeilTensorRingedDerivedSquare": {"hash": "5b025cfd7e4859282042e936f945814922d493b6", "status": "OK"}, "Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNative": {"hash": "c8e550c2ce0b12dcf0b74ffb1011fa65c7b46ce0", "status": "OK"}, "Sheaf.Paper.NativeWeilTensorRingedDerivedSquareOrdinary": {"hash": "ff7c1fed7a1304082dcf2503aa6bca2861d25814", "status": "OK"}, "Sheaf.Paper.NativeWeilTensorRingedTransport": {"hash": "2f7b875b57570960d5704a144e3098b21e00d053", "status": "OK"}, "Sheaf.Paper.NativeWeilTensorTransport": {"hash": "6c20ee93dddc033703d728dfb0501fe0e9aaa49b", "status": "OK"}, "Sheaf.Paper.NativeWeilUnitMateIsIso": {"hash": "4769af7a2f48e94d3dd98b53e25d08d694521c4c", "status": "OK"}}, "seconds": 291, "time": "2026-10-28T10:50:39+0800", "transitive": 3, "version": 1}
```

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
