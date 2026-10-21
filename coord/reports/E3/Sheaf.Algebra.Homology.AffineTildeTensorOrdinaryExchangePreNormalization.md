## What changed

Restored the explicitly quarantined
`Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalization`
by publicly re-exporting the adopted source implementation, which already proves
`AlgebraicGeometry.affineTildeTensorOrdinaryExchange_preNormalization` under the
original fully qualified name. This is a repair of a zero-hole module, not a new
proof counted against the sorry ledger.

Consolidated the unclaimed
`Sheaf.Algebra.Homology.AffineBaseChangeTildeRepresentative` with its identical
adopted implementation. Keeping the old duplicate definitions prevents importing
the restored theorem: Lean reports that the environment already contains
`AlgebraicGeometry.affineBaseChangeTildeComplexIso._proof_18` from the Sheaf module.
The normalization import and all five public representative declarations remain.
Both data constructions are unchanged.

The exchange node and representative node gain explanatory `lean.note` fields.
Their original Lean attachments, statements, proof steps, dependencies and unit
route remain unchanged. The exchange proof still uses the ordinary chain equality,
the homotopy quotient, derived localization and right-derived-unit naturality.

The quarantined chain module has a J1 claim. Its file and node are untouched.
The restored exchange interface gets the same chain declaration through its
public adopted source import. This preserves that proof dependency without
restoring or changing another group's item.

Change record:
`coord/changes/E3-affine-exchange-prenormalization-source-reuse.md`.

Validation: `lcompile.py --all` compiles the final representative and exchange
interfaces in 1.7 seconds each. The coexistence/axiom check, importing the restored
interface alongside the canonical ordinary-exchange parent, compiles in 2.0 seconds.
The archived representative API checks compile in 27.6 seconds: both old concrete
definition bodies are equal to the adopted definitions by `rfl`, and all three
representative equations retain their archived signatures. All nine axiom checks,
including the ordinary-exchange parent, show only the three permitted axioms.
Scratch files are excluded from the packet; import-direction checks pass.

## Proved and sorry left

The archived item contains zero `sorry` occurrences. Closed: 0. Added: 0.
Split off: 0. Remaining in the delivered modules: none.

The restored interface supplies the complete existing proof of
`AlgebraicGeometry.affineTildeTensorOrdinaryExchange_preNormalization`.
The representative interface supplies the existing concrete
`affineBaseChangeTildeComplexIso` and `affineBaseChangeTildeRepresentativeIso`,
and the proved `affineBaseChangeTildeComplexIso_hom_f`,
`affineBaseChangeTildeRepresentativeIso_counit` and
`affineBaseChangeTildeRepresentativeIso_identity_hom`, all in
`AlgebraicGeometry`.

Axiom checks of all these declarations, the chain theorem and the termwise
pushforward comparison report only `propext`, `Classical.choice` and `Quot.sound`.
No existential witness, axiom or new mathematical statement is introduced.

## No longer needed

No mathematical node, dependency or module is pruned or withdrawn.

The restored item does not repeat its archived proof-only imports of
`Sheaf.Algebra.Homology.AffineTildePushforwardCohomologyNormalization`,
`WeilConjectures.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility`,
`WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction` and
`WeilConjectures.AlgebraicGeometry.TensorPullbackTilde`: the complete source proof
already uses them. The same declarations remain available through the retained
public comparison and representative interfaces.

The archived public Sheaf-chain import is supplied through the adopted source
module's public chain import. The chain node remains an explicit dependency and
its original Sheaf attachment is retained for J1's repair. This is consolidation
of duplicate implementations, not pruning of the chain argument.

## Where the brief, the DAG or earlier work was wrong

The assigned item is a quarantine/build repair with zero holes. Its absence from
`lean/` was not a withdrawal: the preserved source and dependencies were read.
The adopted source library already contains the full proof, so reopening the
previously split argument would duplicate existing work.

The archive's `ModuleCat.extendScalars_additive_sheaf` helper no longer exists.
The source theorem uses `ModuleCat.baseDerivedTensor_extendScalars_additive`
instead, only as a proof-irrelevant additive-instance value. Textual comparison of the complete public signature and proof matches the
adopted implementation exactly after that replacement, expansion of the tilde
abbreviation and renaming two unused let binders. No mathematical hypothesis
changes. A redundant scratch copy of the large theorem exceeded 60 seconds;
the delivered library interfaces compile in seconds.

The original chain copy times out at 60 seconds; the canonical implementation
is already compiled and fully proved. No time limit was changed, proof split
introduced, source-library declaration removed or tool modified.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
