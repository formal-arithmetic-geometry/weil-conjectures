## What changed

Prove `WeilConjectures.twistSheafScalarComparison_existsUnique` from the existing
normalized signed-line scalar comparison and the general binary scalar-extension
tensor comparison. A fully proved private helper transports the specified
ordinary scalar functor to its sheafification presentation, constructs the
natural isomorphism, checks its pure-tensor formula and proves uniqueness by
local tensor generation. No mathematical statement is split off.

Existing proofs of `twistScalarMaps_identity` and `twistScalarMaps_composition`
reuse the proved completed-coefficient identity and composition lemmas. The
composite semilinear map retains its existing construction and normalization
proof.

Remove the unused legacy rational/common-stage functor branch, whose current
unit realization already uses the intrinsic tensor functors. Every retained
public signature and non-theorem definition body is unchanged. The change
record gives exact old text, consumers and the replacement unit route:
`coord/changes/coefficient-twist-legacy-functors-pruning.md`.

Add proof-only imports of
`Sheaf.Algebra.Homology.ScalarHomOrdinaryTensorComparison`,
`Sheaf.Paper.SignedLineScalarTensorTower`,
`Sheaf.Paper.ScalarExtensionComposition`, and
`Sheaf.Paper.ScalarExtensionBinaryCoherence`. Private site instances from the
composition import and the duplicate commutative-presentation derived-category
instance are disabled during this module's elaboration.
`HasDerivedCategory.standard` and `completedIntegralCoefficientSheafUnrestricted`
are locally irreducible, keeping the completed inverse-limit construction abstract.
Profiling identified the repeated inverse-limit normalization; the delivery
checks the complete module without profiling options, including the axiom probe.
The public stage-descent import is retained because `QbarTwistCommonStage` uses
its reexported interface.

Proof search used LeanFinder, Loogle, Mathlib grep and searches of both library
roots. The existing binary scalar tensor core avoids reconstructing balanced
maps and gluing their local inverses.

## Proved and sorry left

Proved one of the six original holes:
`WeilConjectures.twistSheafScalarComparison_existsUnique`.
No holes are added; zero statements are split off.

Two original holes remain:

- `WeilConjectures.twistScalarMaps_existsUnique`
- `WeilConjectures.twistLineScalarIso_existsUnique`

Both retain their existing source and complete proof docstrings citing
`def-coefficient-twists-detailed`. Their statements and constructions are
unchanged. The proved sheaf comparison depends on the normalized line comparison,
so this is a proof from existing stated dependencies, not a claim that the whole
signed-line construction is sorry-free.

Three original holes are pruned, not proved:

- `WeilConjectures.integralComplexTwist_constructible`
- `WeilConjectures.rationalTwistScalarComparison_unit`
- `WeilConjectures.coefficientTwistStageComparison_coherent`

The delivered module therefore contains two `sorry` occurrences, down from six;
one is closed by proof and three disappear with the unused branch.

## No longer needed

The 22 removed declarations are:

- `WeilConjectures.integralComplexTwist_linear_statement`
- `WeilConjectures.integralComplexTwist_constructible`
- `WeilConjectures.rationalComplexTwist`
- `WeilConjectures.integralConstructibleComplexTwistFunctor`
- `WeilConjectures.integralConstructibleComplexTwistFunctor_linear_statement`
- `WeilConjectures.integralConstructibleComplexTwistFunctor_additive_statement`
- `WeilConjectures.rationalComplexTwistFunctor`
- `WeilConjectures.rationalComplexTwistFunctor_obj`
- `WeilConjectures.rationalComplexTwistFunctor_map`
- `WeilConjectures.twistIntegralScalarComparison_existsUnique`
- `WeilConjectures.twistIntegralScalarComparison`
- `WeilConjectures.twistRationalOrdinaryComparison_existsUnique`
- `WeilConjectures.twistRationalOrdinaryComparison`
- `WeilConjectures.rationalTwistScalarComparison`
- `WeilConjectures.rationalTwistScalarComparison_unit`
- `WeilConjectures.algebraicClosureComplexTwist`
- `WeilConjectures.coefficientTwistStageFunctor`
- `WeilConjectures.coefficientTwistStageComparison`
- `WeilConjectures.coefficientTwistStageComparison_coherent`
- `WeilConjectures.algebraicClosureComplexTwistFunctor`
- `WeilConjectures.algebraicClosureComplexTwistFunctor_obj`
- `WeilConjectures.algebraicClosureComplexTwistFunctor_map_exists`

Imports removed:

- `import Sheaf.Paper.ScalarExtensionDualLocalIso`
- `import all Sheaf.Paper.IntegralConstructibleLinear` (its ordinary public import remains)

No module file or node is withdrawn. No unused source-library declaration is
removed. The current unit's `sfIntegralTwistingFunctor`,
`sfRationalTwistingFunctor` and `sfQbarTwistingFunctor` remain the recorded
realizations, using the retained signed lines and intrinsic rational/common-stage
tensors. This is the actual replacement route; it does not bypass the unit.
All active DAG references and all 32 listed quarantine archives were audited,
in addition to active Lean consumers. Historical review hole lists remain intact.
`tools/downstream.py --uses` found only this item among all 3,491 transitive
importers for the branch declarations. No parent or consumer requires adaptation.

The module's two currently attached statement nodes,
`lem-route-coefficient-twist-line-exact` and
`lem-pur-signed-integral-coefficient-twist-constructible`, and their already proved
statements are retained unchanged. No proof-dependency edge of those nodes changes.

## Where the brief, the DAG or earlier work was wrong

The assigned file includes an older independent rational/common-stage branch,
while the current `def-coefficient-twists-detailed` attachment already points to
`IntrinsicCoefficientTwistsUnrestricted`. Proving the old branch is unnecessary
for that recorded route. The cleanup is documented for independent review rather
than claiming its three removed holes as proofs. No false statement or target
weakening is introduced, and no new node is needed for fully proved private
transport glue.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
