## What changed

Repair of the return of `84edc36ad6a`: restore the original item module and its
DAG attachment after the batch rollback `a62c78b1fa2`. The current shared source
contains neither the module nor a `coord/rework.tsv` row or quarantine archive
for it; the existing module claim remains held by P5. The retained sandbox
module was checked byte-for-byte against the returned commit before repair.
It preserves the original declaration and all its dependencies. This packet
restores that source and node rather than withdrawing an absent path.

The compile against the current snapshot initially took 64.1 seconds. Profiling
identified repeated checking of the nested ordinary tensor comparison. Its
normalization proof now composes explicit section equalities instead of a long
rewrite chain, retaining the same construction and statement.

Filled `WeilConjectures.SemilinearSections.semilinearScalarTensor` in
`Sheaf.Paper.SemilinearScalarTensor`, preserving its statement. The ordinary
comparison is transported from the existing binary scalar-extension tensor core
to the supplied `ScalarData.model.E`; its ordinary adjunction proves naturality
and the actual unit-section formula. The inverse ordinary comparisons define the
signed total comparison, with precisely the recorded summand equation.

Scalar-specific tensor cancellation preserves every K-flat complex. K-flat
resolutions, fully faithful restriction to representatives, and the existing
`tensorComparisonDescent` construct the natural derived comparison. An elementary
isomorphism cancellation lemma reverses its forward counit square to exactly the
square required by `ScalarTensorComparisonModel`.

Private proof imports reuse the ordinary-comparison presentation helpers, the
proved total-comparison naturality helpers, and independent-coefficient K-flat
preservation. All new helpers are private and proved; no public definitions,
instances, declaration signatures or public imports change. The item node's
proof and proof dependencies now describe this argument. There are no adapted
consumer modules. `coord/changes/P5-semilinear-scalar-tensor-restoration.md`
records the restoration against the currently absent item.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.SemilinearSections.semilinearScalarTensor`
(node `lem-coef-semilinear-scalar-tensor`).

Original holes: 1. Holes closed: 1. Holes added: 0. Holes left in the item: 0.
No split-off statements or new nodes.

Validation: the returned version compiled in 54.1 seconds before delivery;
the current snapshot required the timing repair described above. The revised
file compiled through `lcompile.py` in 54.8 seconds with profiling enabled;
the ordinary-normalization kernel check fell from 12.1 to 6.75 seconds. Profiling
options have been removed. The delivery command checks the final source and runs
the required server preflight and axiom probe.

## No longer needed

No original Lean import is removed: the original public
`Sheaf.Paper.SemilinearSystemModels` import supplies the unchanged statement.

The direct proof dependency `lem-weil-pbc-ringed-topos-kflat-pullback`
(`Sheaf.Paper.KFlatRingedToposPullback`) is unnecessary here: the scalar-specific
`lem-pur-kflat-change-of-rings-all-independent` proves preservation of all K-flat
complexes without constructing identity-topos inverse-image data or needing flat
terms. The direct proof dependency
`lem-weil-pbc-site-derived-tensor-descent`
(`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`) is
replaced by the supplied tensor-model comparisons together with
`lem-weil-pbc-resolving-representative-whiskering` and
`lem-weil-pbc-tensor-comparison-descent-representatives`.
These are removals from this node's direct plan; their modules may remain
transitively needed elsewhere. No module is withdrawn.

The pre-existing `lem-sfb-scalar-tensor-comparison` and
`lem-sfb-scalar-ordinary-tensor-comparison` supply proved generic private helper
APIs, rather than imposing their simultaneous `ScalarHomModels` interfaces on
this theorem. The binary scalar core, tensor-colimit, all-K-flat cancellation,
and representative descent nodes are generic tools below the unit level. The
unit `sk-prop-sf-biduality-general` has no realized statement or steps replaced.

## Where the brief, the DAG or earlier work was wrong

The return described this item as quarantined. At repair time it has no current
quarantine copy or rework row: the batch rollback removed the original split
module and its node. The P5 claim is already present. This restoration uses the
retained delivered module and node, with the original theorem signature and
Lean attachment. No quarantine archive is deleted and no absent path is listed
in `deleted.txt`.

No mathematical correction was needed. The stronger existing scalar-specific
K-flat preservation theorem shortens the planned general ringed-topos route.
The ordinary helper theorem in the library takes a complete simultaneous
homotopy-derived scalar presentation; only its proved ordinary presentation
helpers are needed for the supplied cochain `ScalarData` here.

Edge cases checked in the argument: the empty site, zero ring/module/complex,
identity coefficient maps, arbitrary nonflat coefficient maps, and unbounded
complexes. Nothing uses faithful scalar extension, coefficient flatness,
boundedness, or generation of sheaf-tensor sections by global pure tensors:
ordinary extensionality uses the sheafification adjunction and presheaf tensor
generators.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
