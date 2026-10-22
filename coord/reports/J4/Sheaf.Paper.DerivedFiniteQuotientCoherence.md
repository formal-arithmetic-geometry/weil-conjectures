## What changed

The target route needs the finite evaluation transition square, not the larger
six-conjunct intermediate theorem. Its only Lean consumer,
`adicPresentationFiniteIso_transition`, used exactly the first conjunct. The only
DAG proof-dependency parent used that same square. The unit has no realized statement
or proof step assigned to the withdrawn node.

The packet proves `finite_quotient_transition_compatibility` directly, from the canonical
ordinary quotient square and the existing K-flat normalization interfaces. It changes
the unclaimed `AdicPullbackPresentationTransport` module in exactly two lines: its
private import and the proof application. Every statement, definition and public import
of that consumer is preserved. The formerly required extended module is withdrawn
through `deleted.txt`, and its node's Lean attachment is set to null. The parent's
proof dependencies now cite the directly proved transition square.

The new ordinary comparison theorem proves the strict quotient square on sections.
The new derived theorem lifts that square to complexes, uses the prescribed finite
computation maps and exact restriction factors, and descends along K-flat resolutions.
Generic naturality and composition lemmas keep those computations abstract. No quotient
is assumed K-flat over the completed ring. No coefficient, tensor, pullback,
localization, target, or canonical-map definition is changed.

The three delivered modules compiled together: ordinary comparison in 5.7 seconds,
finite transition compatibility in 32.8 seconds, and the adapted consumer in 38 seconds.
No compile limit, kernel check, launcher tool, or source-library declaration was changed.
The change record is `coord/changes/J4-finite-transition-route.md`.

## Proved and sorry left

The original module's one hole is removed by withdrawal, not reported as a proof of
its unused six-conjunct statement. Original holes proved: 0 of 1. Original holes
pruned: 1. Holes added: 0. Holes retained in the packet: 0. Unproved split-offs: 0.

The following two theorems are completely proved:

- `AlgebraicGeometry.Scheme.ordinary_finite_quotient_comparison`
  (`lem-cbc-ordinary-finite-quotient-comparison`).
- `AlgebraicGeometry.Scheme.finite_quotient_transition_compatibility`
  (`lem-cbc-finite-quotient-transition-compatibility`).

The retained public statements in `AdicPullbackPresentationTransport` remain proved
with exactly their original signatures. All three delivered Lean modules contain
zero `sorry`. No hole is placed inside a definition. Existing dependencies retain
their own proof obligations; this packet adds none.

## No longer needed

`Sheaf.Paper.DerivedFiniteQuotientCoherence` is withdrawn, together with its unused
`cbcFiniteOrdinaryTarget`, `cbcFiniteOrdinaryNormalization`, and
`derived_finite_quotient_coherence` declarations. Its mathematical DAG statement and
proof plan are retained. The parent no longer cites its node in `proof_deps` or any
proof step. The finite-interface node has no dependency on the withdrawn node;
its historical references do not require a Lean declaration. A repository-wide search
found no other Lean consumer of any of these three declarations. The unit's
`realized.statement` and `realized.steps` lists are both empty.

The directly proved transition square does not require the additional invertibility,
balanced section, derived normalization, normalization cocycle, and normalization unit
conclusions of the former conjunction. The attempted ordinary-balancing module and
its node were never published and are omitted from the packet. The prior complete
proof attempt is preserved under the sandbox scratchpad; none of its unused assertions
is moved to a new hole.

These private imports of the withdrawn module are not required by the replacement:

- `Sheaf.Algebra.Homology.DiagramKFlatReplacements`
  (`lem-weil-pbc-diagram-kflat-replacements`).
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
  (`prop-weil-pbc-proetale-constant-ring-map`).
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat` (`lem-pur-kflat-change-of-rings`).
- `Sheaf.Algebra.Homology.KFlatTotalTensorModel` (`lem-pur-kflat-total-tensor-model`).
- `Sheaf.Paper.RingedTopoiTensorSections`
  (`def-weil-pbc-ringed-tensor-section-calculus`).
- `Sheaf.Paper.FlatCommonQuotientReductionTower`
  (`lem-weil-pbc-flat-common-quotient-reduction-tower`).
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`
  (`lem-pur-cochain-pullback-tensor-coherence`).
- `Sheaf.Paper.KFlatRingedToposPullback`
  (`lem-weil-pbc-ringed-pullback-preserves-kflat`).
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`
  (`lem-pe-constant-left-module-inverse-image`).
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`
  (`lem-pur-left-derived-from-kflat-class`).
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
  (`prop-weil-pbc-proetale-constant-exact`).
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`
  (`lem-sfb-successive-derived-quotient-normalization`).

The replacement also does not invoke `lem-cbc-finite-constant-map-naturality`,
`lem-cbc-derived-tower-evaluation-normalization`, or
`lem-weil-pbc-flat-scalar-restriction-kflat`. This is pruning of this proof route;
these library declarations remain available to their other consumers. Constant-completion
results remain used indirectly by the ordinary comparison proof. The consumer's
public imports of coefficient, pullback, and constant-completion modules stay verbatim.
No module or declaration under `lean/WeilConjectures/` is withdrawn.


The unit-route import flag concerns
`lem-weil-pbc-flat-common-quotient-reduction-tower`, realized in Step 1 of
`sk-lem-integral-models`. The original CBC node explicitly lists this node in
its maintainer-approved `tool_uses`, and its `split_report.tool_uses` calls it a
generic common-quotient comparison tool for a simultaneous tensor resolution.
SETUP.md's "Tool lemmas and the unit route" rule permits treating that use as
a tool use, independently of the integral-models unit's own proof. The new finite
square proof uses the published model normalizations instead of reconstructing
that resolution. No statement, step, dependency, or realization of
`sk-lem-integral-models` is changed. Its tool module and existing consumer
`Sheaf.Paper.RingedCommonQuotientPullbackComparison` remain verbatim. Thus removal
of this generic tool from the CBC subargument bypasses no unit step.

## Where the brief, the DAG or earlier work was wrong

The original item packaged the finite transition square together with five additional
normalization assertions. Reading its consumer shows that only the square is needed
by this target route. Proving that square directly avoids reconstructing a simultaneous
resolving tower or proving the unused normalization assertions. The existing canonical
model normalizations suffice for the derived descent.

The earlier missing published dependency is available. Several complete six-clause
proof attempts were developed and diagnosed before this consumer audit; none is
claimed as compiled or delivered. The final packet follows the shorter mathematical
route, preserves the consumer's complete statement, and withdraws the unused extended
lemma under the brief's §8d. This is pruning of unused assertions, with no unproved
parts retained in another module and no definition repair adopted.

## Forced adaptations

Server preflight requests the original-versus-adapted consumer check for
`Sheaf.Paper.AdicPullbackPresentationTransport`. The shared claim record is unclaimed.
The original, verbatim consumer was compiled against the withdrawn module represented
by an empty module file. That empty module compiled in 0.2 seconds; the original
consumer failed in 35.2 seconds at its only use of the withdrawn theorem:

```text
AdicPullbackPresentationTransport.lean:1195:14:
error(lean.unknownIdentifier): Unknown identifier `derived_finite_quotient_coherence`
```

The remaining diagnostic is the consequently unsolved transition square. The adapted
consumer has compiled in 38 seconds against the new, fully proved transition theorem.
Only line 19 (the private proof import) and line 1195 (that proof application) change.
Every existing signature, visibility, public import, definition body and other proof
stays verbatim. Both edits are necessary to replace the removed dependency; there are
no additional adaptations.

## New nodes

`lem-cbc-ordinary-finite-quotient-comparison` records the strict ordinary quotient
square used by the finite-reduction compatibility argument. Its proof transports
surjectivity of the completion projection, cancels the epic quotient unit under the
normalized inverse-image adjunction, and compares the prescribed generators.

`lem-cbc-finite-quotient-transition-compatibility` records exactly the canonical finite
transition square consumed by presentation transport. Its proof combines the ordinary
square, exact restriction composition, naturality of the tower counit, cancellation of
finite computation on K-flat representatives, and descent through a K-flat resolution.
It includes equal indices and the first positive quotient and assumes no completeness
of the derived object. LeanSearch, Loogle/LeanFinder and source grep found only the generic localization and
factor-naturality APIs used in this proof, not the required normalized comparison.

Both nodes have source proofs, edge-case checks, Mathlib searches and Lean attachments.
Both new statements are true portions of the source argument and are fully proved.
The original node is retained with `lean: null`, and its parent is updated to the new
route. The record `coord/changes/J4-finite-transition-route.md` lists all 21 downstream
modules and verifies that their retained statements and definitions are unchanged.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
