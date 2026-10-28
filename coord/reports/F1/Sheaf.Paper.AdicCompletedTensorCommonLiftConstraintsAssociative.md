## What changed

Repaired the arbitrary-tensorator normalization defect of
completed_tensor_common_lift_constraints_associative. The statement now requires
its tensorator components to be the explicit completedTensorCommonComponent maps.
Added the proved construction completed_tensor_common_lift_normalized_tensor_unit,
which retains this equality while assembling the tensorator with NatIso.ofComponents.
Its unit is the existing ordinary coefficient-unit comparison composed with
coherence.unitIso.

The constraint wrapper now constructs such data and returns them together with
the constraints. AdicCompletedTensorCommonLiftCoherence consumes that pair and
keeps exactly its original theorem and structure signatures. The two adapted
existing modules were unclaimed on the server. No source-library file is changed.

A private category of graded rational lines supplies an explicit natural invertible
binary comparison whose two associativity paths at degrees (1,0,0) differ. This
certifies the generic normalization obstruction; it is not a full instantiation
of the old scheme/realization theorem. The existing disputed warning and source
were read before making the correction.

All four delivered modules compile alone through lcompile.py in import order.
The unchanged direct consumers AdicCompletedTensorCommonLiftAgreementComponent
and AdicCompletedTensorCommonLiftAgreement also compile against the repair
(15.2 s and 4.5 s). Their temporary unchanged sandbox copies were removed.

## Proved and sorry left

Holes closed: 0. Holes added: 0. This is a normalization/interface repair and a
proved construction, not a proof or decomposition of the original associativity
assertion. The old false universal statement is not counted as proved.

Proved: WeilConjectures.AdicQbarRealization.completed_tensor_common_lift_normalized_tensor_unit
(new node lem-sf-adic-completed-tensor-common-lift-normalized-tensor-unit).
The private graded-line sign-twist example is also proved, without any sorry.
The constraint wrapper and coherence assembly remain fully proved from their
existing component declarations and the new concrete construction.

The sole sorry left in this delivery is
WeilConjectures.AdicQbarRealization.completed_tensor_common_lift_constraints_associative
(node new-sf-adic-completed-tensor-common-lift-constraints-associative).
It has the corrected normalization hypothesis and an expanded proof plan in its
docstring. In particular the source coherent-reduction associator must be
identified with its normalized chain representative; pairwise tensor models
alone do not supply that identification. No split-off sorry modules are added.

## No longer needed

No library module is withdrawn and no imported mathematical dependency is claimed
unnecessary. The coherence constructor no longer invokes
completed_tensor_common_lift_tensor_unit separately: its data now come from the
constraint wrapper, whose normalized constructor has a proved component equality.
Remove new-sf-adic-completed-tensor-common-lift-tensor-unit from the coherence
node's direct proof dependencies only; it remains a type dependency of the new
constructor and remains used elsewhere. No import is removed from a source file.

## Where the brief, the DAG or earlier work was wrong

The original associativity theorem and constraint wrapper treated arbitrary
natural tensor/unit comparisons as if they were the constructed normalized ones.
STATEMENT-DISPUTED (repaired): the former universal data quantifier had no
normalization field. A degree-dependent invertible sign can preserve naturality
while changing the associativity equation. Merely passing N and native coherence
beside data does not relate those objects.

The existing tensor/unit existence theorem constructs the right maps but its
Nonempty conclusion forgets their component equation. The new proved constructor
retains it; the only immediate caller constructs its new hypothesis. The upper
coherence statement is unchanged, so the intended existence theorem is preserved.

I checked a finite-field decomposition, including the left and right path
transport separately. The native target coherence does not itself identify the
selected source coherent-reduction associator with its chain model (the related
CompletedPullbackTensorAssociativityRepresentatives module already flags that
issue). I retained this work in the one existing named obligation, and did not
add a new theorem asserting an unjustified source normalization. No new hole is
hidden in a definition or a private helper.

## Statement corrected

new-sf-adic-completed-tensor-common-lift-constraints-associative now requires the
explicit component equation. Its only DAG citer,
new-sf-adic-completed-tensor-common-lift-constraints, is adapted here and constructs
that equation via the new proved constructor.

new-sf-adic-completed-tensor-common-lift-constraints now asserts existence of data
and their four constraints. Its only DAG citer,
lem-sf-adic-completed-tensor-common-lift-coherence, is adapted here and keeps its
original statement. Its own citers (lem-sf-adic-completed-tensor-common-lift and
lem-sf-adic-completed-tensor-common-lift-agreement-component) see the same interface.
The statement_change records enumerate both changed nodes' complete citer lists.

## New nodes

lem-sf-adic-completed-tensor-common-lift-normalized-tensor-unit records the proved
explicit component construction with its normalization equality retained. It is
strictly construction data and does not assert any associativity equation. The
three search services were run; NatIso.ofComponents is the generic constructor
used in the proof, while the project supplies the actual components and naturality.

Change record: coord/changes/F1-common-tensorator-normalization.md.

## Related modules compiled before delivery

73 related module(s) compiled against this delivery by deliver3.py: 3 INFRA, 68 OK, 2 SLOW.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AdicCompletedTensorCommonLiftCoherence": "0cda3d7900a6d8d0ce86e31651d54de4df189264", "Sheaf.Paper.AdicCompletedTensorCommonLiftConstraints": "efa322448274a3538d1f0a7f0839dd9b4187bba2", "Sheaf.Paper.AdicCompletedTensorCommonLiftConstraintsAssociative": "ca66f01e5adf174cb32dc1c796a0607e676201a0", "Sheaf.Paper.AdicCompletedTensorCommonLiftNormalizedTensorUnit": "069050f1faf2d6c3888267e09649d1046cf65e7e"}, "results": {"Sheaf.DeligneLaumon.MarkedGeometricCurveModel": {"hash": "9c1a341196df0e0f09ccb19f9e86e0a9a805b27c", "status": "OK"}, "Sheaf.DeligneLaumon.PairEigenvalueCurveTest": {"hash": "d3bbf6cfba9472fc935b3b39e25985369491ef2c", "status": "OK"}, "Sheaf.DeligneLaumon.Reduction.AffineCurveUpper": {"hash": "ce57ae16a536204ab9eba3695780ca9dc3a63812", "status": "OK"}, "Sheaf.DeligneLaumon.SmoothAffineConstituentPurity": {"hash": "3e19706676d8d822f492c12f728dccbfdebf066f", "status": "OK"}, "Sheaf.Paper.AdicProperAdjunctionRealization": {"hash": "96ee4c0c30f40ae8fea46a37912de4f72984f9d2", "status": "OK"}, "Sheaf.Paper.AdicQbarConstructibleRealization": {"hash": "7e2ce2076ec6ff2ae7f31dd670b20fca6d09af3f", "status": "OK"}, "Sheaf.Paper.ArithmeticRoots": {"hash": "7bd225699855f1f1739a412f3afcefd75c9feb78", "status": "OK"}, "Sheaf.Paper.CurveMiddleExtensionUpper": {"hash": "c6f8dfc1e80926b9a264bde2f1d573a678b9a70a", "status": "OK"}, "Sheaf.Paper.NativeProperProjectionComparisons": {"hash": "94a4cec31da2a9fcc9d3b90314671c1aa440a4e4", "status": "OK"}, "Sheaf.Paper.NativeProperProjectionRealization": {"hash": "a5224fc4ecf3b95c4c95e42ff8df633243877b25", "status": "OK"}, "Sheaf.Paper.NativeWeilDualizingHomTransposition": {"hash": "5b927f525bb69bb0e0e9f19f1d041f628dbb2ae4", "status": "OK"}, "Sheaf.Paper.NativeWeilScalarCounitCategories": {"hash": "45d3944eaf2d27b4f4591ccc09d56f229f3c804b", "status": "OK"}, "Sheaf.Paper.WeilCompactStructureTensorComparison": {"hash": "4af22f43d117514bcd7bffefad37846fa469680b", "status": "OK"}, "Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse": {"hash": "aa192c680dc77c64ea316a68187f1536468e6fa0", "status": "OK"}, "Sheaf.WeilSheaf.DualRealizationComparison": {"hash": "a4c7aed1bf1cface6c840589f93a3d310530ca70", "status": "OK"}, "Sheaf.WeilSheaf.NativeBidualEvaluationRealization": {"hash": "237c3de53410c930efdb5d8359bcec22e4f96f2b", "status": "OK"}, "Sheaf.WeilSheaf.NativeExceptionalClosureCompactSupport": {"hash": "7d39293f80044355c3fead78b6479b741b5e65eb", "status": "INFRA"}, "Sheaf.WeilSheaf.NativeExceptionalCounitHomSquares": {"hash": "2943a9fc6fd129f8289051e2740553ab4f9defcc", "status": "INFRA"}, "Sheaf.WeilSheaf.NativeExceptionalForgetful": {"hash": "558d68376aa151c040c27a8900d7ec63bc19178f", "status": "INFRA"}, "Sheaf.WeilSheaf.NativeExceptionalForgetfulData": {"hash": "689f4dff827e0634508a8c7747796789416b8331", "status": "OK"}, "Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitCarrier": {"hash": "00bc6b9e0c1ed9394c39d215ee6de33ac82f1f83", "status": "OK"}, "Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitGraded": {"hash": "d0ab950ff0ec31c68b5574fcf2aba41eeda69323", "status": "OK"}, "Sheaf.WeilSheaf.NativeSectionClosedForgetful": {"hash": "f286d3f68deed64803e66383d8da201f974a2d5e", "status": "OK"}, "Sheaf.WeilSheaf.StructuralBidualInvertible": {"hash": "86e30fe2b8d9b87dbbdb3f36423e71736b903e75", "status": "OK"}, "WeilConjectures": {"hash": "a9f1970d653af90a208232c6a0658c40dd10bba9", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper": {"hash": "25e17f64018e0dd56a69ea571797e24d9dca8518", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform": {"hash": "c268069b6605a2f643c4277583a0dd05e3b61c65", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights": {"hash": "aa257ff62b94eea1c6ddd0332b5869efab118b18", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist": {"hash": "56b09c11f9acc0b083ba686f416eb107d8ffde92", "status": "SLOW"}, "WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound": {"hash": "7016f8c78748678e28c93e6e10d1b5e818497292", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.DegreeOne": {"hash": "77fbca2b83b62e86f20139006879cb4527ee1e31", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional": {"hash": "a801a2eb52766304ff7d9f5336e6ff625cd694aa", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents": {"hash": "bd68082076d6be0b267679036edc1b5400168baa", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude": {"hash": "a3f2bb005144566b73d2d85c1b584f7eadcd3d00", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport": {"hash": "921280e6e46c895b53991bdb4a9c3b05548dfe03", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.LocalDuality": {"hash": "362511fd1ec8ffac6035ff8ce532c2e19daa78d9", "status": "SLOW"}, "WeilConjectures.DeligneLaumon.AffineLine.Perverse": {"hash": "532f304ad95829a1e4211ea2353c3d601a0bb647", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform": {"hash": "0d7dbae6f69ef36fd481f1c3239ee3c5366e8e49", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.Purity": {"hash": "aaa9b5c9fea18e40024bf5b24a0c69ff22e99ec7", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel": {"hash": "e5ddff4ffd6608520ea51cf86dcee0518a9e5f0c", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy": {"hash": "07e21eb9c7bc1d1ffa3dc1b3c3734060c970e2d1", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension": {"hash": "f5b207e4d4b7a872b1a11a7e214de57646312212", "status": "OK"}, "WeilConjectures.DeligneLaumon.Reduction.AffineCurve": {"hash": "8bb655d0a4f6a82fcfdd1ed5a7b1fb5e7238ddac", "status": "OK"}, "WeilConjectures.DeligneLaumon.Reduction.DirectImage": {"hash": "9246cfbabe1a4bc9d3bb351a15113408b707b89b", "status": "OK"}, "WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension": {"hash": "540ce6b39bccc3c943bd009279b59bf301d7a606", "status": "OK"}, "WeilConjectures.DeligneLaumon.Reduction.MixedStalk": {"hash": "01f7d58af49a6562d41b5ee144dbe131d18a831b", "status": "OK"}, "WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed": {"hash": "52e7e5c28569d665cf4735a8ed52c11bfa9a8d65", "status": "OK"}, "WeilConjectures.DeligneLaumon.Reduction.RealSheaves": {"hash": "3d3491027e07ee3e2dd18fc3df95caa6869d9eb7", "status": "OK"}, "WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine": {"hash": "6c73b57001b8950cc7f31da4c2f731db4903d590", "status": "OK"}, "WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity": {"hash": "eb45959895a844b88c4ed2b809af3168e39e57bd", "status": "OK"}, "WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants": {"hash": "a8831739817950f0331524f4c1e6694204689c9a", "status": "OK"}, "WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity": {"hash": "d8023c1bf91f5442edacbd2e8b8edd2387c958ae", "status": "OK"}, "WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin": {"hash": "cc9e175fa74dd547ad615c05d25b8402281ced61", "status": "OK"}, "WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity": {"hash": "18ce085ff094a3a54b51e847c1318b29501e1616", "status": "OK"}, "WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity": {"hash": "25e6ab1b83aba88d7e8a761e1e92bb9bcc1a03ed", "status": "OK"}, "WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity": {"hash": "cdb3223783897af1559b130b1ce31daeef4173a7", "status": "OK"}, "WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary": {"hash": "ffe03e4cd28e4f739a2f1219a1d8fbe04930691a", "status": "OK"}, "WeilConjectures.WeilSheaf.CohomologicalRange": {"hash": "6ca2482878f1da28c25673e03e74340fbf93acdd", "status": "OK"}, "WeilConjectures.WeilSheaf.CohomologicalRangeAffine": {"hash": "7841feb68e94c3373f511da11e24c3b2b5c8dc3c", "status": "OK"}, "WeilConjectures.WeilSheaf.Curve": {"hash": "df8ca5919998ad169a38f9cf1784d6ff7a54bf32", "status": "OK"}, "WeilConjectures.WeilSheaf.CurveEndpoints": {"hash": "a34bf6b1522712199f815703144df1c0e606f3ab", "status": "OK"}, "WeilConjectures.WeilSheaf.Karoubian": {"hash": "c89a68f262590266711dacf11cba93b5f07435b5", "status": "OK"}, "WeilConjectures.WeilSheaf.PoincareDualityLisse": {"hash": "fe2552db6be2b06e8bc0d4abfa9280a97893fe83", "status": "OK"}, "WeilConjectures.WeilSheaf.RealPurity": {"hash": "f1d064ef649328d0668c47418d2639a92883d27a", "status": "OK"}, "WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity": {"hash": "a044b657bf5c50ba6e92c2715c05a668c83e7f02", "status": "OK"}, "WeilConjectures.WeilSheaf.VerdierDual": {"hash": "cbd782ced4a4ed0d3932076da1a163a61a8db8c5", "status": "OK"}, "WeilConjectures.WeilSheaf.VerdierDualFinite": {"hash": "539fae180cbfedfacb31b1a5aa570bb55b24ba94", "status": "OK"}, "WeilConjectures.ZetaFunction.Examples": {"hash": "e36146ba0f7231927a1328c607237203746bb899", "status": "OK"}, "WeilConjectures.ZetaFunction.FinalTheorems": {"hash": "3d6504ef77b73dbdab403a3a493962f20a4c0207", "status": "OK"}, "WeilConjectures.ZetaFunction.HasseWeil": {"hash": "123bdc4c708b08a7661d2a5157af692f000eecb5", "status": "OK"}, "WeilConjectures.ZetaFunction.RealizationIndependence": {"hash": "9e3e6a9829b5ac0703584f754efd3582cec16e16", "status": "OK"}, "WeilConjectures.ZetaFunction.RelativePurity": {"hash": "4f8c68373735a415ba035c6c4c9e1e3c3cfbac31", "status": "OK"}, "WeilConjectures.ZetaFunction.Weights": {"hash": "b06fb0c6197e5250f74dc4f6101955ac750c6bb7", "status": "OK"}}, "seconds": 425, "time": "2026-10-28T12:16:51+0800", "transitive": 73, "version": 1}
```

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
