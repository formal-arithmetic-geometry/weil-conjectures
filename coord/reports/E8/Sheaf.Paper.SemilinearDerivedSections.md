## What changed

The main module keeps every existing public signature and public import. Its original
`semilinearDerivedSections` hole is replaced by a complete proof assembling two distinct
construction layers. New private proofs derive reduction naturality, the push transition
formula from the pull transition formula, and projection evaluation from the recorded
tensor pullback and evaluated adjunction equations. The previously landed `evaluation_mate`
proof is retained and is not counted as E8 work.

Two new modules state the remaining constructions: `SemilinearSystemsExistence` for the
ordinary system calculus and cartesian internal Hom, and `SemilinearOperationsExistence`
for geometric operations, ring-tower scalar extension and open localization on a fixed
calculus. The operations statement requests only the pull transition equation; the main
module proves the push transition and projection evaluation equations. Both the main
proof and the two new statements compile. The three-module `lcompile.py --all` check
completed successfully (41.4 s, 23.3 s and 45.7 s for the individual modules).

Exploratory scalar, tensor/Hom, and transition-localization files are preserved as text
in the sandbox scratchpad and are not delivered or imported. They are not additional
holes in this packet.

## Proved and sorry left

Closed: `WeilConjectures.SemilinearSections.semilinearDerivedSections` (one original hole).
Its body contains no `sorry`. The complete private compatibility proofs are
`evaluation_transpose`, `reduction_naturality`, `push_transition_of_pull`, and
`projection_evaluation`.

Added and still unproved:

- `WeilConjectures.SemilinearSections.semilinearSystemData`, node
  `lem-coef-semilinear-system-existence`, in
  `lean/Sheaf/Paper/SemilinearSystemsExistence.lean`.
- `WeilConjectures.SemilinearSections.semilinearOperationsData`, node
  `lem-coef-semilinear-operations-existence`, in
  `lean/Sheaf/Paper/SemilinearOperationsExistence.lean`.

Thus this is a decomposition: one upper hole closed, two genuinely separate construction
holes added, two holes left in the delivered modules, and no claim of net hole progress.
There are no holes in definitions, anonymous proofs, or private helpers. Neither split
repeats the parent statement: the systems result contains no geometric operations, and
the operations result starts with a fixed system calculus and does not assert the two
compatibility equations proved in the parent.

Edge checks: arbitrary nonflat coefficient maps are retained; no flatness assumption is
added. The cartesian hypothesis remains on the first Hom argument. Equal indices, the
empty site, zero coefficient rings, identity geometric morphisms and identity open
localizations do not require exceptional cases. The categorical compatibility proofs
never infer equality of arbitrary derived morphisms from evaluations.

## No longer needed

Removed proof-only imports from the main module:

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.QuasiIsoHomComplexMap`
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.RingedTopoiDerivedPullback`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`

These former direct construction dependencies are not used by the new categorical
combination proof. Their relevant construction steps are retained, with their original
source and dependency lists, in the two new nodes. They are not claimed to be unnecessary
for proving those remaining constructions. No public import was removed and no blueprint
unit was bypassed. No existing module is withdrawn; no whole-module pruning is claimed.
The experimental `SemilinearTensorHomData` split is not delivered, because the two-layer
packet does not use it. Likewise the experimental scalar-data module is not delivered.

## Where the brief, the DAG or earlier work was wrong

The original plan bundled construction of operations with compatibility equations that
follow formally from its normalized adjunction and tensor fields. The parent now proves
the push-transition and projection-evaluation equations directly. The remaining original
construction route is preserved in the two child nodes. Existing signatures and target
statements are unchanged; no interface change or forced adaptation is needed. Preflight nevertheless classifies
the new namespace/variable layout as a command visibility change; its required record is
`coord/changes/SemilinearDerivedSectionsProofScopes.md`.

The preserved earlier work had not been delivered. Its first dry run failed because the
report was missing. Some interrupted requests returned no service response; later checks
also exposed genuine elaboration timeouts and unfinished experimental proofs. Those
experiments are not represented as successful proofs in this report. The sandbox budget
start had reset on resumption (recorded in resume-notes.md); it was not edited here and
elapsed time is not offered as a reason for the decomposition.

## New nodes

`lem-coef-semilinear-system-existence` records the ordinary abelian/derived system
construction and the cartesian Hom transition law (original proof steps 1--6 and 12--14).
Its Lean statement is `semilinearSystemData` in `Sheaf.Paper.SemilinearSystemsExistence`.
Its docstring gives the complete representative and adjunction argument in words.

`lem-coef-semilinear-operations-existence` records geometric, coefficient and open
operations on a fixed calculus (original proof steps 7--11 and 15, with the normalized
geometric tensor representative construction). Its Lean statement is
`semilinearOperationsData` in `Sheaf.Paper.SemilinearOperationsExistence`. The parent
node's proof, proof dependencies and proof origin now record the actual combination.
The proof-scope command layout is recorded in
`coord/changes/SemilinearDerivedSectionsProofScopes.md`, as requested by preflight.
All existing statements and definitions are unchanged.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
