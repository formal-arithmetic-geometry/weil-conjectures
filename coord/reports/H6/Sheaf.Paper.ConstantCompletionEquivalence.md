## What changed

Change record: `coord/changes/H6-constant-completion-comparison-proof-context.md`.

In `Sheaf.Paper.ConstantCompletionEquivalence`, proved four existing comparison
statements from the prescribed ordinary comparisons and K-flat computation theorems.
Added private proved localization-extension, extensionality, comparison-square, and
flatness-transport helpers. The resolving-class extension passes through the homotopy
category and its calculus of fractions, then uses fully faithful localization
precomposition. No public signature or definition changed. The shared K-flat transport proof and the comparison squares are parametrized
by abstract functors before specialization, avoiding repeated kernel reduction of
concrete scalar-extension and complex-composition constructions.

Added private proof imports of `WeilConjectures.CategoryTheory.NatTransFromResolvingClass`,
`WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated`,
`Sheaf.Paper.KFlatRingedToposPullback`,
`Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients`,
`Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat`, and
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`.
The two `WeilConjectures` imports and the independent change-of-rings theorem
are proved general tools attached to other units; this delivery does not
change their nodes or the maintainer's `tool_uses` approvals. The proper-base-change
unit route is retained. Updated the existing node's proof, proof dependencies and origin.

Also optimized existing `quotientPresentation_exists` by passing the specified ordinary
limit unit and its proved projection equations into the private derived-tower lemma,
and eliminating the derived presentation witness in proved generic helpers.
A module-sheaf specialization keeps the tower functor abstract while checking the
category-instance conversion, before inserting concrete scalar-extension functors. Its statement and construction are unchanged.

Local irreducibility attributes prevent elaboration from repeatedly unfolding chosen
derived-category data and scalar functors. They do not change exported reducibility.

## Proved and sorry left

Closed four of fourteen original holes, all in namespace
`CategoryTheory.ConstantCompletion`:

- `finiteDerivedComparison`
- `derivedReductionTowerComparison`
- `derivedPullComparison_existsUnique`
- `finitePull_existsUnique`

Added zero holes and split off zero statements. These proofs use existing stated
mathematical dependencies, some still unproved; this is not a claim that their axiom
closures are already free of `sorryAx`.

The ten remaining original holes, all attached to
`lem-weil-pbc-constant-completion-equivalence`, are:

- `flat_and_quotients`
- `koszul_quotient_reflector`
- `completion_restriction`
- `inverseImageData_exists`
- `ordinaryPullComparison_existsUnique`
- `ordinaryFinitePull_existsUnique`
- `completedFinitePull_existsUnique`
- `pullbackTowerComparison_existsUnique`
- `pullback_composition`
- `pullback_identity`

## No longer needed

The old private `towerOrdinaryUnit` construction is removed: the generic derived-tower
proof now receives the actual `ordinaryUnit` and its proved projection equations directly.
No import, DAG node, module, or unit step is withdrawn. The remaining original holes
still require their planned dependencies. Zero current imports is not used as a reason
to prune a node.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy found. The resolving-class natural-transformation extension
and its quasi-isomorphism calculus were needed as general tools in addition to the
previous proof-dependency list. The finite reduction and strict tower arguments use
the already proved ordinary comparison isomorphisms; their tensor construction does
not need to be repeated in the derived proofs.

Validation: the complete module compiled through `lcompile.py` in 56.2 seconds
as `ResumeLocalAbelian.lean`, and the actual delivery file subsequently compiled in
56.1 seconds. The formerly missing published dependency is available. A redundant
pair of local irreducibility attributes was removed. Private theorem proofs and the
quotient-presentation proof reconstruct their existing abelian structures with the
preadditive parents explicitly exposed; all public signatures and constructions are
unchanged. The latest complete version compiled in 55.1 seconds as
`ResumeQuotientAbelian.lean`, with no warnings. The same complete module with explicit
`#print axioms` checks for all four replacement proofs compiled in 55.6 seconds as
`ResumeAxioms.lean`. Each reported only `propext`, `Classical.choice`, `Quot.sound`
and the expected `sorryAx` from existing unfinished dependencies. The delivery tool
checks the actual module again, including its axiom probe and preflight, before pushing. A previous
probe exceeded 60 seconds; a subsequent attempt received no answer from the busy
compile server, so neither pushed. The ordinary completion-unit restriction
calculation is proved in scratch work, but is not claimed as a closed hole or
included in this packet.

The delivery subsequently passed compilation and its axiom probe, then failed preflight
only because this report omitted the exact change-record path. That path is now named
under `What changed`; delivery is being rerun with the same Lean packet.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
