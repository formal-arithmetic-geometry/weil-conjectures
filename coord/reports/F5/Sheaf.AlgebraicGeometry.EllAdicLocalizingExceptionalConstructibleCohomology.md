## What changed

Proved `ellAdic_localizing_rightAdjoint_obj_homology_constructible` with its exact
original signature and all three coefficient families. The sole changed Lean module
is the assigned item. Its public import is unchanged.

A proof-only `import all Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded`
reuses the existing, completely proved private helpers `certified_comparison` and
`hull_eq`. These establish the coefficient certificate, generator equality, and equality
of the actual hulls, including the different coproduct indexing universes. No helper
was copied or exported, and neither boundedness theorem is used. The proof then applies
`exceptionalInverseImage_exists`, identifies the identity compactification with proper
pushforward, transports the supplied adjunction through the fully faithful inclusions,
and applies `rightAdjointUniq`. Isomorphism invariance transports the finite-Tor
constructibility predicate; the generator equality yields the requested homology clause.

The DAG proof, proof dependencies and proof origin now record this route. Compilation
through `lcompile.py` succeeded in 7.0 seconds without diagnostics. No definition,
statement, target, public import or source-library file changed. The local elaboration
commands are recorded in
`coord/changes/F5-adic-exceptional-cohomology-proof-context.md`, with all 21 consumers.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_localizing_rightAdjoint_obj_homology_constructible`
(node `lem-sfb-adic-localizing-exceptional-cohomology`).

No `sorry` remains in the item. Added holes: zero. Split-off statements: zero.
The proof uses existing declarations with their own outstanding dependencies, notably
`exceptionalInverseImage_exists`; those obligations were not restated or moved.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality`
- `Sheaf.Paper.CondensedQbarLfpLocalTriviality`
- `Sheaf.Paper.IntegralLfpLocalTorsionCharts`
- `Sheaf.Paper.IntegralLfpLocallyFreeResolution`
- `Sheaf.AlgebraicGeometry.BoundedConstructibleLocalizingClosure`
- `Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient`
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
- `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`
- `Sheaf.Paper.CondensedConstantConstructibility`
- `Sheaf.Paper.IntegralLfpConstantModelComparison`
- `Sheaf.Paper.LocalizingAdmissibleCoefficients`
- `Sheaf.Paper.LocalizingClosureCtfEqualsBc`
- `Sheaf.Paper.LocalizingExceptionalAdjoint`
- `Sheaf.Paper.ProperExceptionalRestriction`
- `Sheaf.Paper.RationalExceptionalRestriction`
- `Sheaf.SixFunctors.IntegralBrownAdjoint`
- `Sheaf.SixFunctors.IntegralExceptionalRestriction`

The coefficient comparison dependencies remain needed through the reused helper proofs;
they are not claimed as pruned modules. The former direct rational/integral adjoint and
restriction imports are supplied behind the existing `sk-thm-existence` assembly.
The node `lem-sfb-adic-proper-localizing-adjunction-comparison` and module
`Sheaf.Paper.AdicProperLocalizingAdjunctionComparison` are not needed by this proof:
the sibling's already proved `hull_eq` handles the full ordinary hulls and their indexing
universes directly, and the proper identity comparison is assembled in Lean. They may
still be needed by other parents; no module is withdrawn by this delivery. The node
`sk-prop-sf-existence` is no longer a direct proof dependency: the stronger existing
`sk-thm-existence` supplies the same adjoint together with constructible preservation.
No globally pruned module is claimed.

## Where the brief, the DAG or earlier work was wrong

The DAG's newer comparison interface uses `finiteTorLocalizingClosureOfSize.{u+1}`,
while the existing Brown and restriction interfaces use `localizingClosureProEtale`.
These are not definitionally identical. The proved sibling helpers already settle this
comparison by a small-support argument, so using them avoids duplicating that work or
adding a new hole. The unit's proper-identity-compactification and exceptional-adjoint
route is preserved. The source read was main-20261015
`sk-thm-existence/det-existence-restriction.proof.md`, all three coefficient bullets,
and `sk-cor-existence-ii/_section.md`. Empty schemes, zero inputs, identity maps and
integral torsion are retained: no new hypotheses, inversions or coefficient restriction
occur in the proof. There are no new statements needing separate edge-case tests.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
