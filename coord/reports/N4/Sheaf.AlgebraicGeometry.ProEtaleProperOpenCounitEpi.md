## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.sfProperOpenCounit_epi` by a complete
Lean combination of two strictly smaller geometric statements. Its signature and
three public imports are unchanged. The new proof-only imports are
`Sheaf.AlgebraicGeometry.ProEtaleProperQcOpenCounitSections` and
`Sheaf.AlgebraicGeometry.ProEtaleOpenCounitFiniteSupportDiagram`.

The first statement handles global sections only, with affine base and a
quasi-compact open. The second constructs a finite-support commuting diagram for a
section under a qcqs morphism, without assuming properness and without asserting
surjectivity of either counit. Apply the first to the base-changed proper morphism
in the second diagram and compose the two equalities to lift the original section.
A proved private lemma `epi_of_surjective_affine` then uses affine open covers,
local surjectivity of abelian sheaves, and the faithful forgetful functor to obtain
the module-sheaf epimorphism. No data definition or existing interface was changed.

The new statements have full source/proof docstrings and matching DAG nodes. The
original node now records the actual three-step Lean assembly. All three modules
compiled without warnings in the final import-order check; the assigned module
took 7.2 seconds, and each new module was below 6 seconds.

## Proved and sorry left

Original holes: one, in `AlgebraicGeometry.Scheme.sfProperOpenCounit_epi`.
That declaration now has a complete Lean proof from the two new statements. The
private `epi_of_surjective_affine` is proved without any new assumption.

Two holes are added, both whole public theorem proofs in their own new modules:

- `AlgebraicGeometry.Scheme.sfProperQcOpenCounit_sections_surjective`, node
  `lem-exc-proetale-proper-qc-open-counit-sections`.
- `AlgebraicGeometry.Scheme.sfOpenCounit_finiteSupportDiagram`, node
  `lem-exc-proetale-open-counit-finite-support-diagram`.

This is a decomposition: one original hole closed, two holes added, zero holes
remaining in the assigned module, two in the delivery. It is not a sorry-free proof
of the proper/open support theorem. Both steps are needed: the diagram by itself
supplies no preimage under a counit; the affine quasi-compact-open lemma by itself
does not treat arbitrary opens or arbitrary test objects. Their combination and
the affine epimorphism criterion are real Lean proofs.

## No longer needed

Removed these ten proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized`.
- `Sheaf.RingTheory.WContractibleClosedLocalization`.
- `Sheaf.AlgebraicGeometry.AffineClosedSpecializationLocalization`.
- `Sheaf.AlgebraicGeometry.ProEtaleShriekSpecializationZero`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`.

These are import removals, not module withdrawals. The specialization localization,
weakly etale localization, zero-extension and exact-sheafification dependencies
remain needed by the two geometric steps and are retained in their DAG proofs.
In particular the original geometric plan is not claimed pruned merely because
its imports have moved below the two new obligations. The normalized finite-ring
tower and arbitrary-ring operations are not needed by the finite-coefficient
underived assembly here. No existing declaration or module is withdrawn, and no
upstream declaration is removed. No whole node is claimed globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The assigned node's one proof step compressed both the proper specialization
argument and the finite-representative reduction for a possibly non-quasi-compact
open. They are different steps: the latter needs qcqs, while the former uses
properness. The new nodes separate them and explicitly retain the commuting
counit maps, rather than merely asking for an abstract isomorphism.

The original module-level blueprint marker had the nonexistent suffix
`proper-open-counit-isiso-epi`; it now names the actual assigned node. No statement
was changed. The ancestry script returns no blueprint ancestor for this item,
because the existing `created.item` chain terminates at a Lean module name rather
than a DAG id. The new nodes preserve its computed null ancestor and record the
actual proper-base-change proof location in `from.place`; their `via` names the
assigned node. The parent support node explicitly identifies
`prop-exc-base-change-proper`, Steps 3--4. No unrelated ancestry records were edited.

The mathematical edge cases checked were empty base, empty smaller open, zero
section, zero coefficient ring, and the full open. Empty finite representatives
allow the empty union, and the identity-open counit gives the full-open case.
Properness is not silently added to the finite-support statement. No target
statement, binder, universe, or definition was weakened.

## New nodes

`lem-exc-proetale-proper-qc-open-counit-sections`, in
`Sheaf.AlgebraicGeometry.ProEtaleProperQcOpenCounitSections`, isolates Steps 3--8 of
the parent support argument: finite principal opens, closed-specialization
localizations, proper closedness, vanishing, and gluing. Its conclusion is
surjectivity on global sections over an affine base with quasi-compact open.

`lem-exc-proetale-open-counit-finite-support-diagram`, in
`Sheaf.AlgebraicGeometry.ProEtaleOpenCounitFiniteSupportDiagram`, isolates Steps
9--11: choose finite representatives, shrink their support to a quasi-compact open,
and construct the additive commuting diagram using the specified adjunction
counits. The diagram asserts neither original nor smaller counit surjectivity.
There are no change records because no other existing module or public interface
was changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProEtaleOpenCounitFiniteSupportDiagram": "bc7aaee841c36b1bcf6ef3a6844de775286a91d8", "Sheaf.AlgebraicGeometry.ProEtaleProperOpenCounitEpi": "8d25a52ab3de798241985f37d1f0efcda8db2b36", "Sheaf.AlgebraicGeometry.ProEtaleProperQcOpenCounitSections": "e00f75ed0f9b655df55a6326743855f36351c96f"}, "results": {"Sheaf.AlgebraicGeometry.ProEtaleProperOpenSheafComparison": {"hash": "09e7169473109df788dd91ac0f0bb5ea32e0cd7d", "status": "OK"}}, "seconds": 16, "time": "2026-10-28T12:11:19+0800", "transitive": 0, "version": 1}
```

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
