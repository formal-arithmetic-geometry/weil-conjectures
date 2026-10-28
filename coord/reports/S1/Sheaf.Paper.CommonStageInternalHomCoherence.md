## What changed

Proved `WeilConjectures.CommonStageInternalHom.commonStageHomComparison_hom_square`
without changing its statement. The proof bundles the existing rational Hom comparisons
into a natural isomorphism, applies their scalar tower law, and transports this law
through the chosen stage functors. The input corrections satisfy the same tower law by
the stage-system cocycle. Conjugating the resulting naturality square gives the theorem.
The support module constructs the finite-stage scalar-pair functor and comparisons
and proves their tower law; its general categorical calculations and input-correction
lemmas are private and proved.

Added the proof import `CommonStageInternalHomCoherenceLemmas`, which uses
`SpecifiedHomScalarRationalNaturality` and `SpecifiedHomScalarTower`. The support
module separates the finite-stage proof and categorical calculations so each file compiles
within the per-file limit; it introduces no unfinished statement. Narrowed
`SpecifiedHomScalarTower`'s public imports to
`FiniteRationalDerivedOperations` and `SfScalarExtensionComposition`, preserving its
existing declaration verbatim. Its former import of `DerivedPullbackTensorHom` would
create a cycle through this item. Corrected the two scalar-compatibility nodes' matching
finite-stage dependencies and recorded the actual proof route in the item's node.
The change record is `coord/changes/common-stage-hom-scalar-imports.md`.

Validation: `lcompile.py --all` compiled the repaired scalar tower (6.1 s),
the support module (45.5 s), and the item (51.8 s), with no warnings or errors. The unchanged direct importer
`SpecifiedHomScalarEvaluation` also compiled against the overlay (9.3 s); its
temporary sandbox copy was removed after the check.

## Proved and sorry left

Closed the item's single hole:
`WeilConjectures.CommonStageInternalHom.commonStageHomComparison_hom_square`
(node `lem-weil-common-stage-internal-hom-coherence`). No holes remain in the item;
none were added or split off. The new proved support theorem is
`WeilConjectures.CommonStageInternalHom.rationalHomComparison_tower`
(node `lem-weil-common-stage-internal-hom-scalar-coherence`).

The adapted `SpecifiedHomScalarTower` retains its existing hole
`WeilConjectures.specifiedHomScalarRational_tower`
(node `lem-zl-specified-hom-scalar-rational-tower`). Its statement and proof body
are unchanged. The proof also uses the existing stated
`WeilConjectures.specifiedHomScalarRational_naturality`
(node `lem-zl-specified-hom-scalar-rational-naturality`), whose hole is unchanged.
These are existing dependencies, not new obligations.

## No longer needed

Removed `public import Sheaf.Paper.DerivedPullbackTensorHom` from
`SpecifiedHomScalarTower`: its finite-stage statement only needs the two replacement
imports. Removed `def-weil-derived-pullback-tensor-hom` from the scalar naturality and
tower nodes' dependencies and proof-step uses; these finite-stage laws do not depend on
the common-stage Hom construction.

The item's proof uses the more precise existing scalar naturality and tower declarations
and the coefficient-stage specification instead of directly using
`lem-pur-integral-operations-scalar-extension`. The latter remains needed transitively;
no whole module or blueprint unit is withdrawn or claimed globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The generic integral scalar-extension dependency did not directly state the normalized
rational Hom equations needed here. Those equations were already available as the
specified scalar naturality and tower lemmas. Their broad common-stage dependency edges
(and the tower module's broad import) were circular when used to prove this coherence.
Replacing those edges by their actual finite-stage interfaces resolves that cycle without
changing any mathematical statement or definition. The unit's route is preserved.

## New nodes

`lem-weil-common-stage-internal-hom-scalar-coherence` records the proved finite-stage
Hom scalar tower in `Sheaf.Paper.CommonStageInternalHomCoherenceLemmas`, together with
its explicit scalar-pair functor, natural comparison and pair associator. It is a genuine
part of the argument and has a complete proof from existing specified scalar laws.
The support module also holds the proved private categorical calculations and input
correction lemmas used only by the item's proof. It adds zero holes.
The related import repair is recorded in
`coord/changes/common-stage-hom-scalar-imports.md`.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 3 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.CommonStageInternalHomCoherence": "2c4aaa58e93c800f6a750f1d92efe32ca8e87d2b", "Sheaf.Paper.CommonStageInternalHomCoherenceLemmas": "4d8c7cd35a5a88498855b21ee89f32e9bb2a594e", "Sheaf.Paper.SpecifiedHomScalarTower": "708ff322fe97a9a7292e26a9b32fe60df14c75cd"}, "results": {"Sheaf.Paper.CommonStageInternalHomRepresentative": {"hash": "f31368609b9b9d7e2ce4c71602e17e5f46a29bcb", "status": "OK"}, "Sheaf.Paper.RelativeSupportCoordinateModel": {"hash": "10578c3766ba1e2284ed91a08ab128bdc7d1ccf5", "status": "OK"}, "Sheaf.Paper.SpecifiedHomScalarEvaluation": {"hash": "835e9cd05e3d1b1d2f94bc804c63c84ebeefa92a", "status": "OK"}}, "seconds": 58, "time": "2026-10-28T11:04:08+0800", "transitive": 1, "version": 1}
```

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
