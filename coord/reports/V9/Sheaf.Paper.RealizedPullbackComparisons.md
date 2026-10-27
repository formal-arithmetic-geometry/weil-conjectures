## What changed

Proved `WeilConjectures.integralComparisonRationalScalarComponent_naturality` in
`Sheaf.Paper.RealizedPullbackComparisons`, preserving all public signatures,
component formulas, definitions, and imports.

The proof first packages the existing lambda and mu constructions as whiskered
natural transformations. Cancelling mu proves integral scalar naturality for the
specified system C itself. The prescribed object and pure-tensor formulas then
identify both rational composites with the localized integral composites.
Tensor induction proves the rational square: integral naturality handles pure
tensors, and additivity handles zero and sums. All helpers are private and proved.
The existing node's proof fields now describe this argument.
Local irreducibility annotations keep the existing whole-tower functors from
unfolding during proof elaboration; these attributes are local to this module.

Searches: Lean Finder for naturality under tensor extension returned generic
module change-of-rings lemmas; Loogle located `TensorProduct.induction_on`;
Mathlib grep located `conj_eqToHom_iff_heq`. Repository searches found the same
localization argument in the private helpers of `DerivedPullbackTensorHom` and
`CompactSupportRationalScalarIso`, and the same lambda/mu component formulas in
`SfFrameworkThetaShiftCompatibility`. Their private implementation pattern was
used without importing those modules or their unrelated proof dependencies.

## Proved and sorry left

Closed the module's only hole:
`WeilConjectures.integralComparisonRationalScalarComponent_naturality`
(node `def-trf-realized-pullback-comparisons`).

Holes closed: 1. Holes added: 0. Holes left in the delivered module: 0.
No split-off statements or new public declarations.
The complete proof compiled on the server in 29.2 seconds during profiling;
the temporary profiler settings were removed before delivery.
Existing dependency theorems are used through their recorded interfaces.

## No longer needed

None. All three original public imports still supply the public comparison
constructions and their statements. No node or module is withdrawn.
No proof-only imports were added.

## Where the brief, the DAG or earlier work was wrong

The node had no proof steps despite the named naturality theorem's docstring
already containing the tensor-induction plan. Those proof fields are supplied.
The theorem quantifies over an arbitrary specified C, so the existential
realization/coherence theorem cannot directly supply its integral naturality.
Instead this delivery proves that naturality directly from the natural
transformations used in C's lambda and mu definitions, without adding hypotheses
or replacing C. There is no mathematical statement change.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
