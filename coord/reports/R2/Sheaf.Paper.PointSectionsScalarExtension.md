## What changed

Prove `WeilConjectures.pointSectionsScalarExtension` by assembling the six integral and
rational naturality, unit and tower equations. Ordinary sections equations are checked
on pure tensors and transported through exact derived localization using the existing
coefficient-comparison descent lemmas. Completion is handled by naturality and cancellation
of the specified comparison isomorphisms. All existing signatures and constructions stay
unchanged. Private categorical and compatible-coordinate lemmas keep the proofs at their existing
interfaces. Local settings select the existing instances at the actual module size and
restrict unnecessary unfolding.

## Proved and sorry left

The item initially contains one hole, in
`WeilConjectures.pointSectionsScalarExtension` (node
`lem-weil-point-sections-scalar-extension`). The proof closes that hole and adds zero holes. No `sorry` remains in the item.
The complete module compiled successfully in 55.0 seconds. The delivery tool also
runs its combined-file and axiom checks.

## No longer needed

The separate existence package in `Sheaf.Paper.PointDerivedTensorTowerCoherence`
(node `lem-weil-point-derived-tensor-tower-coherence`) is not used: the ordinary sections
unit and tower equations are proved directly from the existing normalized generator
formulas and descended through localization. The auxiliary sections comparison already has a complete direct proof in this
module, using coefficient-ring equivalences and evaluation of sheafification. Thus the original
separate basis package `Sheaf.Paper.PointFiniteFreeSectionsTensor` (node
`lem-weil-point-finite-free-sections-tensor`) is not an additional direct dependency.
Both changes concern this parent's dependency edges; other consumers and transitive
imports are retained. No Lean modules are withdrawn and no public imports are removed.

## Where the brief, the DAG or earlier work was wrong

The dependency statements use separately bundled comparison data. The canonical
constructions in this module can instead be handled directly through their unique
pure-tensor normalization, avoiding a separate transport between the two packages.
The unchanged source exceeded the per-file compile limit in the initial check.
The completed-section bijectivity argument is factored through a proved generic
compatible-coordinate lemma. Ordinary exactness reuses the already proved
`podCompletedOrdinaryScalarExtension_preservesFiniteLimits` and
`podCompletedOrdinaryScalarExtension_preservesFiniteColimits` from
`Sheaf.Paper.CompletedScalarExtensionTExact`. Naturality explicitly normalizes the two
scalar-extension wrappers and the specified comparison, avoiding costly elaborator
conversion. No inline metaprogram is needed. The coherence proofs use generic
categorical cancellation and local transparency settings. No construction body or compile limit is changed.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
