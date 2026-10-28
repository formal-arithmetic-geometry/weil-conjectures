## What changed

Proved `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_kflat_flat`
from the existing underived and total comparison declarations. Pull an arbitrary
ringed acyclic complex through the inverse complex equivalence, use native K-flatness,
apply the exact equivalence, and transport exactness across the total comparison and
its counit. The proof works for unbounded complexes, zero tests and empty sites.

Statement corrected: restored the missing `adj : T ⊣₂ ihomBifunctor k₀ l X` argument.
This datum was already present in the parent interface and is required by both tensor
comparisons. The conclusion, universes and all target statements are unchanged.
Adapted the sole direct importer, NativeWeilTensorRingedKFlatData, by passing its
already available adj argument; its declaration signatures are unchanged.

Updated the item's node with the corrected statement, complete citer audit and actual
proof dependencies. Change record: coord/changes/native-weil-ringed-kflat-adjunction.md.
The current server queue says proof/route, with one hole and no rework or build-error record.

## Proved and sorry left

Closed the one item hole in the corrected declaration
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_kflat_flat`
(node lem-sf-native-weil-tensor-ringed-kflat-flat). There are zero textual holes in
both delivered Lean modules. Added zero holes and split off zero statements.
This is a proof from existing stated dependencies, not a new decomposition.

The pre-existing dependency
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_chain_data`
(node lem-sf-native-weil-tensor-ringed-chain-data) remains unproved outside this delivery.
The underived comparison is already proved. No assumption from the resolution theorem
is used to establish the transport implication.

Validation before this repair: the item compiled in 3.9 seconds against the
published comparison. The global build exposed that the newer ChainData interface
also requires its normalized-sign proof. This repair supplies that proof directly
by reflexivity for the local definition of the Koszul sign. Compiling ChainData plus
the item in import order compiled ChainData in 45.0 seconds and the item in 3.9 seconds.
The adapted KFlatData importer still passes `adj`; final server compilation and the
delivery probes are run by the required tools.

## No longer needed

Removed the proof import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
and the proof dependency lem-pc-kflat-resolution from this theorem's route. K-flat
transport is the direct acyclic-test argument; existence of resolutions is unnecessary.
Replaced the old statement dependency on that resolution theorem by def-pc-kflat-complex.
The resolution theorem remains needed by the separate localization argument, so no
whole module is withdrawn and no global module pruning is claimed.

The new route imports the existing NativeWeilTensorRingedChainData and uses its
underived comparison dependency as well. No other old proof imports or tool_uses
entries are removed. The unit's realized statement and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The flat-field extraction omitted the parent's tensor-Hom adjunction. Additivity alone
cannot provide the tensor comparison used by the old proof plan. Restoring the existing
source hypothesis is recorded explicitly in statement_change and the change record.
The old second step also incorrectly appealed to existence of K-flat resolutions to
prove that a specific complex is K-flat; the inverse acyclic-test argument supplies
the missing reasoning directly.

The other DAG citer, lem-sf-native-weil-tensor-ringed-kflat-localization, is unfinished
and binds neither b nor adj in Lean despite proposing to use their ringed transport.
It has no current Lean application of this theorem. Its statement_change audit entry
is holds:false: the planned application must restore the inherited data first.

STATEMENT-DISPUTED: the existing native_weil_tensor_ringed_chain_data theorem quantifies
over arbitrary sign operations, while its summand identity can hold only for the
canonical Koszul sign. For example the zero operation would force every image of a
summand inclusion to vanish. This proof uses only its chain field at the canonical
sign (-1)^(pq), which is the genuine total-complex comparison described in the source;
it does not use the overly general sign assertion. The module is held by E5 and is
unchanged here; its owner should restrict the sign parameter before closing that hole.

Mathlib searches via leanfinder, loogle and grep found the complex-equivalence API and
generic bifunctor transport but no native K-flat transport theorem. The existing
comparison statements give the short proof; no new helper statement is needed.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Repair of returned landing

The global build of landing `20261027T234046-L-4177423` failed at line 57 because
`native_weil_tensor_ringed_chain_data b T adj U sign` had acquired a required
`hsign` argument in the published ChainData interface. The error appeared as
`rcases failed` because `obtain ⟨c⟩` was trying to destruct a function waiting for
that proof. I now pass `(fun _ _ _ _ _ ↦ rfl)`, since `sign` is defined exactly as
the required `ZSMul.zsmul` expression. No signatures, node statements, imports, or
declarations outside this item's proof changed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NativeWeilTensorRingedKFlatData": "bb876e09b7084c2f1cd2843f0f5b1876e8da4018", "Sheaf.Paper.NativeWeilTensorRingedKFlatFlat": "d554faec2329d984609747ca83ad33e1a3d70f1b"}, "results": {}, "time": "2026-10-28T09:08:36+0800", "transitive": 0, "version": 1}
```
