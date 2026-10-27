## What changed

Filled three theorem proofs in `Sheaf.Paper.CompletedPullbackTowerRealizations`,
without changing any existing signature, public import or mathematical definition.

`pullbackTensorReductionGood` computes finite evaluations as ordinary scalar
extension, then detects the acyclicity of arbitrary tensor tests componentwise.
`pullbackTensorSequenceGood` applies finite-level K-flat preservation, transports
through the specified evaluation isomorphism, and uses the same componentwise
criterion. `pullbackTensorSystemComparison_existsUnique` applies the existing
generic `tensorComparisonDescent`. The proved `RingedDerivedNative.kFlatLocalization`
and Mathlib product localization give full faithfulness for all K-flat pairs, so
the displayed normalization holds on the entire class in the existing statement.

Added the proved finite-level theorem `completedTowerFinitePullbackKFlat` in
`Sheaf.Paper.CompletedTowerFinitePullbackKFlat`. Its stalk/scalar-extension proof
follows the already proved `pullbackTensorFiniteGood` in the descendant
`CompletedPullbackTensorComparison`, which cannot be imported here without a Lean
cycle. The finite theorem identifies the right adjoint directly with the actual
coefficient module direct image, so no intrinsic finite-coordinate bridge is used.
This is a strictly smaller finite-level step, with a complete proof and no sorry.

The first combined proof file exceeded 60 seconds. Profiling found substantial
kernel type-checking cost. Local transparency changes made it worse and were
removed. The self-contained finite-level preservation proof was then isolated in
its own module, and the resolving-whiskering assembly was replaced by the existing
K-flat localization theorem. No existing definition or consumer is changed.
The final combined item then took 61 seconds. Its existing pullback-tower
naturality proof now transports the component equalities through a small proved
congruence lemma, avoiding the two large dependent rewrites. Debug profiling
options have been removed.

The item adds proof imports of `TensorPullbackRepresentativeDescent`,
`SemilinearDerivedSections`, `CompletedTowerFinitePullbackKFlat`, and private access
to `KFlatRingedToposPullback` and `RingedDerivedTensorHomAdjunction`. The new module's
statement imports `IntegralOperationsWellDefined`, `NormalizedDVRTower` and
`KFlatIndependentCoefficients`;
its proof imports the pro-etale algebraic lift and module operations, enough points,
constant-ring operations, algebraic inverse-image K-flatness and scalar-extension
K-flatness. Three item-node proof routes and the new proved finite-step node record
these arguments.

## Proved and sorry left

Closed 3 of the original 6 holes. Added 0 holes; 0 sorry statements split off.
The new finite-level theorem and the private componentwise helper are fully proved.

- `WeilConjectures.pullbackTensorReductionGood`
  (`lem-pur-coherent-reduction-kflat`).
- `WeilConjectures.pullbackTensorSequenceGood`
  (`lem-pur-sequence-pullback-kflat`).
- `WeilConjectures.pullbackTensorSystemComparison_existsUnique`
  (`lem-pur-coherent-derived-pullback-tensor`).

The following 3 original named theorems remain sorry, unchanged:

- `WeilConjectures.pullbackTensorTensorTower_existsUnique`
  (`lem-pur-coherent-tensor-tower`).
- `WeilConjectures.pullbackTensorIntegralTensorModel_existsUnique`
  (`lem-pur-integral-tensor-roos-realization`).
- `WeilConjectures.pullbackTensorSequenceCochain_existsUnique`
  (`lem-pur-sequence-pullback-tensor-cochain`).

The derived comparison uses the last theorem through its uniquely normalized
cochain comparison, as intended by stage 3. The already proved integral pullback
realization is retained unchanged. These are proofs from existing declarations,
not a claim that the full target has no remaining sorry dependencies.

## No longer needed

No original Lean import was removed. No module is withdrawn or globally pruned.
Temporary proof imports `ResolvingRepresentativeWhiskering` and
`KFlatResolutionIndependentCoefficients` are unnecessary after using the existing
K-flat localization theorem. The initially explored finite intrinsic-coordinate
comparison is not imported or used.

The following dependencies are no longer directly used by the revised item-node
proofs. They may remain needed elsewhere or transitively through the tools used.

For `lem-pur-coherent-derived-pullback-tensor`, removed from `proof_deps`:

- `def-coef-ringed-sequence-site`.
- `lem-pc-kflat-resolution`.
- `lem-sf-cochain-tensor-model-rigidity`.
- `lem-weil-pbc-exact-functor-derived-factorization`.

Removed obsolete `tool_uses` approvals: `lem-sf-cochain-tensor-model-rigidity`, `lem-pc-kflat-resolution`.

For `lem-pur-coherent-reduction-kflat`, removed from `proof_deps`:

- `lem-coef-semilinear-tensor-evaluation`.
- `lem-pur-kflat-change-of-rings-independent`.
- `lem-pur-system-coproducts`.
- `lem-pur-system-derived-evaluation`.
- `lem-pur-system-evaluation-topos`.
- `lem-pur-system-ringed-sequence-site`.
- `lem-sf-ringed-derived-tensor-hom-adjunction`.

Removed obsolete `tool_uses` approvals: `lem-coef-semilinear-tensor-evaluation`, `lem-sf-ringed-derived-tensor-hom-adjunction`.

For `lem-pur-sequence-pullback-kflat`, removed from `proof_deps`:

- `def-coef-ringed-sequence-site`.
- `def-trf-geometric-morphism`.
- `def-weil-proetale-inverse-image`.
- `lem-pc-kflat-extension-of-scalars`.
- `lem-pe-constant-left-module-inverse-image`.
- `lem-pur-integral-comparison-sequence-direct-evaluation`.
- `lem-pur-system-evaluation-topos`.
- `lem-sf-sequence-module-pullback-evaluation`.
- `lem-sfb-proetale-enough-points`.
- `lem-sfb-ringed-site-kflat-stalk-criterion`.
- `lem-sfb-ringed-topos-pullback-stalk`.
- `lem-weil-pbc-ringed-topoi-module-adjunction`.

Removed obsolete `tool_uses` approvals: `lem-pe-constant-left-module-inverse-image`, `lem-sf-sequence-module-pullback-evaluation`, `lem-sfb-proetale-enough-points`, `lem-pur-system-evaluation-topos`, `lem-weil-pbc-ringed-topoi-module-adjunction`, `lem-sfb-ringed-topos-pullback-stalk`, `lem-pc-kflat-extension-of-scalars`, `lem-sfb-ringed-site-kflat-stalk-criterion`.

Reduction and sequence K-flatness use finite-level detection rather than
reconstructing the entire sequence geometric morphism or a tensor/Hom adjunction.
The derived comparison uses localization on all K-flat representatives rather
than flat-term rigidity and a later enlargement of the normalization class.

## Where the brief, the DAG or earlier work was wrong

The old docstring for sequence K-flatness mentioned a flat-term filtration, but
its statement has no flat-term assumption. The new proof uses arbitrary-K-flat
algebraic inverse-image preservation, whose stalk proof supplies exactly the
required stronger result. No statement was weakened. The actual finite pullback
is compared to inverse image followed by scalar extension as left adjoints to the
same module direct image, retaining coefficient actions.

The initially considered intrinsic-coordinate bridge creates a DAG path back to
this item; the direct right-adjoint comparison avoids it. The general descent and
K-flat localization tools give a shorter route to the derived comparison than the
previous rigidity plan. Existing unit statements and steps remain in place.
New off-unit tools are recorded in proof_deps; this delivery adds or reorders no
maintainer approvals in tool_uses.

Validation: remote `lcompile.py --all` succeeded for both modules with exit code 0.
No profiling options remain. Existing theorem signatures and public imports are
unchanged; all Lean lines have at most 100 characters. The item has exactly three
remaining sorry tokens and the new module has zero.

## New nodes

`lem-pur-completed-tower-finite-pullback-kflat` states and proves finite-level
preservation for the actual `integralOperationsLevelPullback`. It is a proper
finite-level part of the sequence-site argument and has no remaining hole.
The node records the conservative-point argument, arbitrary scalar-extension
preservation and direct adjoint comparison, together with three Mathlib searches.
There is no change record: existing interfaces and definitions are unchanged.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
