## What changed

Completed `WeilConjectures.twist_preserves_finiteness` in
`lean/Sheaf/Paper/TwistPreservesFiniteness.lean`. The proof assembles finite-level
constructibility and Tor transport, integral completeness, normalized reductions,
and the rational and common-stage inverse clauses from five named intermediate
interfaces. The parent proof also transports support and constructibility across
the resulting reduction isomorphisms. The five interfaces are new modules with
explicit source and proof-plan documentation.

## Proved and sorry left

The parent `WeilConjectures.twist_preserves_finiteness` has a complete proof term,
closing its one textual hole. The following new interfaces also contain complete
proofs:

- `WeilConjectures.finiteLineTensor_conditions`
  (`lem-weil-finite-line-tensor-conditions`);
- `WeilConjectures.signedLineTensor_equivalence`
  (`lem-weil-signed-line-tensor-equivalence`);
- `WeilConjectures.fieldTwist_inverse` (`lem-weil-field-twist-inverse`).

Two new holes remain:

- `WeilConjectures.integralLineTensor_complete`
  (`lem-weil-integral-line-tensor-completeness`);
- `WeilConjectures.signedTwistReduction_comparison`
  (`lem-weil-signed-twist-reduction-comparison`).

No definition contains `sorry`. Relative to the original item this currently closes
one hole and adds two supporting holes. This is a decomposition, with net textual
hole change minus one closed plus two added, not a complete axiom-free proof. The
parent and all five supporting modules compile together in the sandbox.

## No longer needed

The parent proof was compiled after removing these proof-only imports, which are
not used by the completed Lean term:

`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`,
`Sheaf.CategoryTheory.ModulePullbackTensorIso`,
`Sheaf.Algebra.Homology.ChangeOfRingsKFlat`,
`Sheaf.Paper.DerivedCompleteOnSlices`,
`Sheaf.SecSmoothPurity.WeilTwistRationalization`,
`Sheaf.Paper.IntegralTwistBaseChange`,
`Sheaf.Paper.FiniteFreeCompletedScalarComparison`,
`Sheaf.Paper.SfScalarExtensionComposition`,
`Sheaf.Algebra.Homology.KFlat`,
`Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
`Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`,
`Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`,
`Sheaf.Paper.IntegralTwistDerivedScalarCanonical`,
`Sheaf.Paper.IntegralTwistScalarCoherence`,
`Sheaf.Paper.PurTwistSheafLocallyFree`,
`Sheaf.Paper.QbarTwistCommonStage`,
`Sheaf.Paper.SfRationalizationKaroubi`, and
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`.

No existing proof-dependency node is claimed pruned: these imports remain
transitively available through the five intermediate modules or the public
statement imports where needed.

## Where the brief, the DAG or earlier work was wrong

The saved report was stale: the signed-line and field inverse interfaces already
had proof terms, and the finite-line interface is now proved as well. The explicit
coefficient universe annotation and the naturality helper in
`SignedLineTensorEquivalence` compile, as do all six sandbox modules in import order.

The required initial dry run was attempted and refused the added holes under its
early-decomposition gate. The final dry run passed: commit `3f11d9a6ee` compiles and
passes preflight with review class CODEX. It requires independent review of the new
nodes and modules and the two retained intermediate theorem holes. No existing
signature, public definition, or target statement was changed.

The earlier compile-server failures were transient. The current full compile checks
all six files in import order successfully. Repeated provider interruptions also
terminated dry runs before they returned; their logs and active processes were checked
before retrying. No push was made by those interrupted no-push commands.

## New nodes

`lem-weil-finite-line-tensor-conditions` isolates the finite line's local
constancy, constructibility, and Tor-amplitude transport.

`lem-weil-integral-line-tensor-completeness` isolates preservation of the
canonical integral derived-completeness triangle.

`lem-weil-signed-line-tensor-equivalence` isolates signed rank-one powers and
their exact inverse tensor functors.

`lem-weil-signed-twist-reduction-comparison` isolates normalized finite reduction
maps and the derived natural comparison.

`lem-weil-field-twist-inverse` isolates rational and algebraically closed inverse
twists after localization and common-stage descent.


The unit-route import `Sheaf.Paper.FiniteTorAmplitudeSites` is retained.
Change record: `coord/changes/twist-preserves-proof-commands.md`.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
