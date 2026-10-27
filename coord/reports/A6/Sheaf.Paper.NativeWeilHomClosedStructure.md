## What changed

Replaced the hole in `native_weil_hom_closed_structure` by an explicit construction
from an underived additive ringed-site presentation. The proof normalizes native
row-sign Hom projections with the already proved `standardHomModel`, compares the
resulting Hom complexes using their projection equations, and descends the
comparison through K-injective representatives. Private, proved categorical
helpers transport the ringed derived tensor and its adjunction and prove the
source-parameter evaluation naturality required by `CoefficientClosedStructure`.
The original theorem statement and all public imports are unchanged. Both delivered modules compile through `lcompile.py`; the final assigned-module compile took 18.3 seconds. The proof-dependency audit finds no cycle back to the item, and both delivered dependency lists equal the unions of their proof-step uses.

The one remaining geometric step is stated in the new module
`Sheaf.Paper.NativeWeilRingedPresentation`. It concerns only an equivalence of
abelian sheaf categories and their underived Hom bifunctors. It has no parameter
`NativeClosedHomModels`, no derived tensor, no derived adjunction, and no
representative or sign normalization data. Its witnesses are eliminated inside
the proof of the existential conclusion; no definition chooses data from an
unproved existence theorem.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_hom_closed_structure` (one of one).
The three private categorical helpers are fully proved. Added one hole:
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_ringed_presentation`, node
`lem-sf-native-weil-ringed-presentation`. This is a decomposition with net zero
holes, not a sorry-free proof of the original result. The derived comparison,
monoidal transport and adjunction assembly contain no further holes.

## No longer needed

None. The original dependency `def-sf-native-weil-closed-models` is still needed.
No original import, node, module, or declaration is withdrawn. The new proof uses
the existing normalized standard-Hom, projection comparison, K-injective descent,
ringed representative, and ringed derived closed-structure nodes.

## Where the brief, the DAG or earlier work was wrong

The item's two-step plan cites only the model definition. That definition states
neither the native action-site equivalence nor its compatibility with internal
Hom. The existing Frobenius action resolution construction provides an ordinary
small-site module equivalence and an action-site presentation for its own fixed
pairs. The further identification with native Frobenius-fixed internal modules,
and the associated Hom compatibility, is not supplied by that Lean declaration.
The new node isolates this precise underived step; the derived consequences are
proved here rather than repackaged into another existence obligation.

The empty site and zero-module cases satisfy the same restriction and Hom
formulas. No assumptions beyond those of the original statement were added, and
no target or shared definition was changed. The biduality unit's statement and
realized steps are preserved.

## New nodes

`lem-sf-native-weil-ringed-presentation` states the underived native Frobenius
ringed-site equivalence and its natural internal-Hom comparison. Its proof plan
uses the existing small-site realization, internal-to-sectionwise module
equivalence, fixed-pair category, and twisted action-site presentation. The new
statement is strictly the underived portion of the original argument. There is
no change record because no other existing module or node is changed.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
