## What changed

Prove the six original clauses of `Sheaf.AlgebraicGeometry.ProEtaleDirectImageGlobalEvaluation`
from the canonical right-derived compositor, the existing unit–Leray chain formula,
the section-normalized module composition, and the published identity pullback comparison.
The generic comparison, section-realization, terminal restriction, mate transport,
composition and identity arguments are proved private helpers. Public declaration signatures
and all definitions in the assigned module are unchanged.

Repair `proEtaleUnitLerayDirectImageIso` in the unclaimed module
`Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula`: use Mathlib's
`SheafOfModules.pushforwardCongr` on the identical adjunct coefficient equality. This
preserves the isomorphism and exposes its definitional identity action on sections,
avoiding repeated expensive equality-transport unfolding. The change record is
`coord/changes/V5-ProEtaleDirectImageTransport.md`; its consumer search finds only the
assigned module besides the defining module itself. Both files are compiled together. The private section-realization maps are bijections
because sheafification of a sheaf is invertible; no data are selected from a mere
existence theorem. The proof works for the empty scheme and zero coefficient ring.

Update the item's existing DAG proof, dependencies and origin to this route. No new public
statements, modules or nodes, and no additional hypotheses or changes to targets.

## Proved and sorry left

Six original holes closed:

- `AlgebraicGeometry.Scheme.proEtaleDirectImageGlobalEvaluation`.
- `AlgebraicGeometry.Scheme.proEtaleDirectImageGlobalEvaluation_shift`.
- `AlgebraicGeometry.Scheme.proEtaleDirectImageGlobalEvaluation_comp`.
- `AlgebraicGeometry.Scheme.proEtaleDirectImageGlobalEvaluation_id`.
- `AlgebraicGeometry.Scheme.proEtaleDirectImageGlobalEvaluation_open`.
- `AlgebraicGeometry.Scheme.proEtaleDirectImageGlobalEvaluation_third`.

No `sorry` remains in either delivered module. Zero holes added or split off.
The complete assigned module compiled against the sandbox repair in 41.7 seconds
(the earlier full compile took 45.7 seconds), under the unchanged 60-second limit.
The definition repair closes zero additional holes; the six closed holes are precisely
the original six in the assigned module.
The imported intrinsic scalar-realization normalization is an existing stated dependency;
its existing proof obligations are not newly introduced by this delivery.

## No longer needed

Removed imports:

- `public import Sheaf.Paper.FiniteDirectImageComposition`.
- `import Sheaf.AlgebraicGeometry.ProEtaleOpenUnitEvaluation`.
- `import Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`.
- `import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`.
- `import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution`.
- `import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`.
- `import Sheaf.Paper.SfDerivedDirectImage`.

The universal derived-functor arguments directly prove statements on all derived objects,
so no new bounded-below complex, resolution transition or separate derived-Hom computation
is required. The open clause follows from the already proved unit–Leray chain formula;
it does not separately use the open-evaluation or pre-derived-adjunction theorem.
The displayed compositor is its specified adjunction mate, so the general ringed-topos
composition theorem and the paper-level finite direct-image comparison are unnecessary
for this proof. Definitions still appearing in public signatures or transitively required
by retained constructions remain in the library. No source-library declaration is removed.

Removed proof-plan dependency edges (not withdrawals of these declarations):

- `def-pur-kinjective-complex`.
- `def-weil-pbc-bounded-derived-subcategories`.
- `def-weil-pbc-proetale-modules`.
- `def-weil-pbc-proetale-site`.
- `def-weil-proetale-module-direct-image`.
- `lem-pc-pre-derived-adjoint-functors-general`.
- `lem-pur-proetale-open-unit-evaluation`.
- `lem-sc-bounded-below-injective-resolution`.
- `lem-sf-kinjective-derived-map-computation`.
- `lem-weil-derived-direct-image-composition`.
- `lem-weil-pbc-kinjective-hom-derived`.
- `lem-weil-pbc-right-adjoint-preserves-kinjective`.
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`.
- `prop-pur-kinjective-resolutions-exist`.
- `prop-weil-pbc-proetale-constant-ring-map`.
- `pur7710-def-derived-sections`.

Remove from the existing `tool_uses` only approvals absent from both the retained statement
and proof dependencies; keep the remaining approvals in their original order. New route
dependencies are recorded in `proof_deps`; no maintainer approval is invented.

## Where the brief, the DAG or earlier work was wrong

The old proof plan unnecessarily reconstructed bounded-below representatives and resolution
naturality. The existing canonical right-derived functors already supply naturality and
K-injective computations. The unit–Leray chain formula supplies the entire open calculation.
Composition and identity require matching the specifically chosen inverse-image mates;
this is done explicitly using the published section normalizations, not by assuming
arbitrary abstract comparison isomorphisms coincide.

The old direct-image identification was implemented by rewriting a scalar-map equality
under an isomorphism. Its normalization required expensive unfolding; the documented
`pushforwardCongr` repair preserves the same construction with a usable section API.
The blueprint unit's statement and proof steps remain unchanged. No false statement or
changed target meaning was found.

## Second reading by V5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
