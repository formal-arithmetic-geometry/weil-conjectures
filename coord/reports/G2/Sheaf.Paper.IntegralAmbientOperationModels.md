## What changed

Repair of returned head `19902c6d20c` (reviewer C-19902): the proof packet was accepted,
but the reviewer-fix application rejected the filename
`G2-integral-ambient-push-category.md`. The landing parser requires the reviewer override
basename `G2-integral-ambient-push-category.change.md` for the delivered file
`coord/changes/G2-integral-ambient-push-category.md` (`tools/batch_land.py`, function `fixes`).
The change-record cross-reference now uses its full repository-relative path. The accepted
Lean proof and declaration changes are preserved; this repair is rebuilt on current
`sheaf-dag` by the delivery launcher and recompiled on the server. Any further reviewer
correction to this record must use the `.change.md` override basename above.

Reduced `WeilConjectures.IntegralAmbient.tensorTowerModel` to normalized existence and proved
uniqueness. Scalar-extended total summand generators determine maps out of scalar extension:
the scalar-extension adjunction preserves the total coproduct, and extensionality successively
identifies degree maps, chain maps, tower maps and the natural isomorphisms. The private
`tensorLevel_hom_ext` proof and the combination proof are complete.

Added `Sheaf.Paper.NormalizedIntegralTensorTower`, stating normalized existence separately.
Its statement is strictly the existence part of the argument, with no uniqueness assertion.
The finite normalized comparisons and transition compatibility already exist; assembling them
with their specified components is the remaining proof. No arbitrary witness of mere existence
supplies definition data: the public tensor isomorphism is still chosen from the original
uniquely normalized theorem.

Replaced the completed coefficient-map proof by the existing completed-ring coherence theorem
and adjunction naturality, preserving its signature. Supplied definitionally equal canonical
functor types for `push`, `pullComplex`, `pullTower`, `tensorTower` and `tensorRepresentative`
to reduce large
coefficient/category conversions. Section-local reducibility and instance commands control
elaboration. No adopted source-library module or target statement is changed. No held consumer
is adapted. Change records:

- `coord/changes/G2-integral-ambient-push-category.md`
- `coord/changes/G2-integral-ambient-tensor-elaboration.md`
- `coord/changes/G2-unrestricted-reduction-category.md` (withdrawn by the reviewer)

## Proved and sorry left

Original item holes: 4. Upper holes closed: 1,
`WeilConjectures.IntegralAmbient.tensorTowerModel`. Lower holes added: 1,
`WeilConjectures.normalizedIntegralTensorTower`, at
`lem-pur-normalized-integral-tensor-tower`. This is a decomposition, net zero holes, not a
complete proof of tensor comparison existence. The new theorem has exactly `:= by sorry`.

The three original holes retained are:

- `WeilConjectures.IntegralAmbient.pullTowerModel`
- `WeilConjectures.IntegralAmbient.pull_good`
- `WeilConjectures.IntegralAmbient.integralAmbientOperationModels`

Each belongs to `lem-pur-integral-ambient-operation-models`. There are 3 sorries in the item,
1 in the added existence module.
No new private declaration or definition contains a sorry. The existing coefficient-map proof
is shortened, not counted as a closed hole.

## No longer needed

No original public import, module or unit is withdrawn. The old private
`sequenceConstantUnit` and `sequenceConstantMap_naturality` proofs are unnecessary: the
completed coefficient coherence theorem already supplies the projection equations, transported
by adjunction naturality. No upstream declaration is removed.

The item does not directly import `IntegralTensorReductionTowerComparison`: its remaining
finite-comparison use is precisely in the new existence theorem's proof plan. The item imports
`IntegralTensorTransitionCompatibility` only for its proved scalar-extension/coproduct generator
extensionality API. The new existence module's statements need only
`IntegralDerivedOperationsOnSlices`, `IntegralOperationsWellDefined` and
`CoefficientRingedTensorHomModel`; experimental proof imports are removed.
The completed coefficient-map clause no longer directly needs the separate adjunction-lifting
and right-adjoint-limit-preservation proof nodes; these are supplied within
`lem-tw-completed-coefficient-ringed-coherence`. Other unfinished clauses retain their planned
dependencies, including strict coefficient comparison, K-flat pullback and derived descent.

## Where the brief, the DAG or earlier work was wrong

The previous landing failure concerned the reviewer's override filename, not a Lean build
error. No compiler error was attached to the return. A delivered change record ends in
`.md`, whereas the stage-3 reviewer override must end in `.change.md`; these are distinct
interfaces. The sandbox contains the record at its normal delivered path.

An arbitrary map after restriction of scalars is only linear over the completed coefficient
ring. Extending unit-scalar normalization to arbitrary finite scalars must therefore be done
at the finite comparison before restriction of scalars, as the new node's proof states.
The attempted argument using finite-scalar linearity of an arbitrary ambient map was removed.
The normalized existence statement has the expected formula also for zero sections, empty
sites, negative degrees and the first quotient (index zero means exponent one); no boundedness
or nonzero-generator hypothesis is added. Extensionality uses all scalar-extended generators.

The full constructed existence proof was attempted repeatedly with explicit components and
local reducibility control, but its comparison with the recorded strict functors has not passed
the per-file compile check. It is not reported as proved. The partial delivery separates the
mathematical existence and uniqueness arguments and records the former honestly as unfinished.

The launcher reset the reference start on resumption from 2026-10-23T12:23:33Z
(attempt start 1792758213.9237168) to 2026-10-23T15:22:24Z
(attempt start 1792768944.3830268). The worker did not modify budget metadata.

## New nodes

`lem-pur-normalized-integral-tensor-tower`, in
`dag/nodes/sec-smooth-purity/lem-pur-normalized-integral-tensor-tower.json`, records normalized
existence, sourced from Stacks 03EL/07A4 and compatible quotient-tower construction in
Bhatt--Scholze Definition 3.4.10. The node cites the existing finite comparison and quotient
transition theorems. Its public Lean statement is
`WeilConjectures.normalizedIntegralTensorTower` in
`Sheaf.Paper.NormalizedIntegralTensorTower`. The item's node records the completed coefficient
coherence route and the existence/uniqueness decomposition; the unit route is preserved.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Reviewer correction (2026-10-24, head 0925fdf7c03d)

The repair kept the annotations of `unrestrictedIntegralReductionFunctor` and
`unrestrictedIntegralComplexFunctor` in `Sheaf.Paper.IntegralReductionTowerUnrestricted`, which the
reviewer of head 19902c6d20c had already withdrawn. They are withdrawn again. With the new codomain,
`Sheaf.Paper.IntegralOperationsWellDefined` (held by S4) still fails to compile: it cannot synthesize
`PreservesZeroMorphisms` for `curriedTensor (integralOperationsFiniteModules …)` at line 937, and
then `integralOperationsTotalTensorSection` is unknown. The item compiles against the published
module, so `Sheaf.Paper.IntegralReductionTowerUnrestricted` is delivered unchanged. The reviewer's
other corrections of head 19902c6d20c are applied again: the missing stmt_deps of
`lem-pur-normalized-integral-tensor-tower` and the full users table of the push-category record.
