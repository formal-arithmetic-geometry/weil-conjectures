## What changed

Replaced the proposed isomorphism-existence/arbitrary-square decomposition with
separate restriction and common-source naturality subarguments, each in its own
new module. The original theorem constructs its roof source comparison from the
homology precomposition maps of q and p, whose invertibility follows from the
existing `quasiIso_homComplex_map` via the unchanged private helper. It constructs
its target comparison by applying `SheafOfModules.homFunctor` to the opposite
homology isomorphisms of q,p and evaluating at target homology. Their forward
maps are the required `homObjMap` morphisms. It then combines the restriction square and naturality equation by
associativity and cancellation. Existing declaration signatures and definitions
are unchanged. New imports used only in the proof are plain `import`.

## Proved and sorry left

Closed the original named hole:
`CategoryTheory.homologyEvaluation_roof_comparison`
(node `new-v4-homology-evaluation-roof-comparison`). Its proof is a reduction to
two smaller statements, not an unconditional proof.

Added exactly two named holes:

- `CategoryTheory.homologyEvaluation_restriction_comparison`
  (`new-e3-homology-evaluation-restriction-comparison`) handles restriction and
  supplies cycle-compatible evaluation; it has no roof or K-injectivity assumption.
- `CategoryTheory.homologyEvaluation_roof_naturality`
  (`new-e3-homology-evaluation-roof-naturality`) gives the common-source morphism
  equation on a small ringed site, with invertibility of Hom(p) on degree-n
  homology and explicit Hom-component differential/naturality identities; it has no restriction, scheme, quasi-isomorphism, or K-injectivity
  hypothesis, and no arbitrary comparison isomorphisms. Its projection family
  carries the differential and naturality identities supplied by the already
  proved `homComplex_projections_exists`.

This is a decomposition: one upper hole closed and two lower holes added. The
local holes-closed-minus-holes-added count is -1. No global ledger improvement is
claimed. The two discarded `roof_comparison_isos`/`roof_comparison_square` holes
were never in the repository and are not delivered. No hole occurs in data or
in a definition. The existing private helper remains proved.

## No longer needed

Removed these direct proof-only imports from the item's module:
`Sheaf.Algebra.Homology.HomComplexRestrictOpen`,
`Sheaf.AlgebraicGeometry.HomComplexRestrictScheme`,
`Sheaf.AlgebraicGeometry.InternalHomOverEquiv`.
Their comparison constructions belong to the restriction subargument, whose
node retains them as dependencies. No claim is made that these modules leave
all targets' import closures.

The old direct `proof_deps` absent from the item's new direct `proof_deps` are:
`lem-sc-hom-complex-restrict-open`, `lem-sc-hom-complex-restrict-scheme`,
`new-b2-homology-evaluation-definitions`, `lem-sc-derived-hom-mayer-vietoris`,
`lem-sc-internal-hom-over-equiv`.
All remain below the restriction or naturality node, as needed for those
subarguments. Direct uses of `lem-pur-rhom-well-defined`,
`def-pc-quasi-iso-modules`, `def-pur-sheaf-hom`, and
`lem-sc-hom-complex-projections` are retained.

The discarded sandbox-only Isos/Square modules and nodes are not imports or
pruned repository modules. `dag/units/sk-thm-picard-duality.json` has empty
`realized.statement` and `realized.steps` bindings; no realized unit node was
bypassed, and the original restriction/roof/evaluation route is retained.

## Where the brief, the DAG or earlier work was wrong

The proposed `roof_comparison_square` quantifies over arbitrary a,b without
requiring them to be the projection-compatible roof comparisons. Retaining the
sheaf context does not fix this. In degree zero over a nonzero field, identity
restriction and identity roofs give ordinary nonzero evaluation. Keeping b
fixed and replacing a by its negative changes the right side while leaving
all hypotheses unchanged. Over characteristic different from two, both
asserted squares cannot hold. The Boolean scratch example from the prior round
only refutes a generic categorical statement; this scalar-change argument also
explains the fault in the proposed sheaf statement itself.

The first new theorem had a `True` tail and unused e,he assumptions, and its
proof docstring was split into an ordinary comment. Both new nodes copied the
entire original proof, including cycle-square steps absent from the Isos
statement. The item node was not updated to the delivered proof. These defects
are repaired by replacing the invalid decomposition, updating the item node,
and writing full docstring proofs and separate, accurate node plans.

Sources checked: [Stacks 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
for the Hom differential and precomposition;
[Stacks 0A95](https://stacks.math.columbia.edu/tag/0A95) for the existing
quasi-isomorphism argument; [Stacks 08DL](https://stacks.math.columbia.edu/tag/08DL)
for restriction. The expanded subargument proofs are marked as agent-written.

## New nodes

`new-e3-homology-evaluation-restriction-comparison` is the open-restriction
subargument: comparison isomorphisms, transported evaluation and its two cycle
identities, with no roof. Its module is
`Sheaf.Algebra.Homology.HomologyEvaluationRestrictionComparison`.

`new-e3-homology-evaluation-roof-naturality` is the evaluation-naturalness
subargument: an equation through the actual homology precomposition maps and
internal-Hom homology maps. Its module is
`Sheaf.Algebra.Homology.HomologyEvaluationRoofNaturality`.

Both have complete docstring proofs, source citations, nodes, statement and
proof dependencies, blueprint ancestry, and searches. No existing public
interface was changed, so there is no change record.

## Second reading by E3

1. Compared the delivered item to the repository with `diff` and the declaration
   reader: existing statements unchanged, existing private helper unchanged,
   no definition or existing public import changed. Verdict: passes after repair.
2. The first decomposition would compile only because its false square was
   admitted. Replaced it with the reduction described above. Final local compile
   and axiom results are recorded below. The only textual holes are the two
   named smaller theorems. No forbidden declaration or hollow definition is
   present. No arbitrary witness of an unproved existence statement defines data:
   the restriction witnesses are eliminated only in a proposition proof, and
   the roof isomorphisms are constructed from explicit maps and inverses.
3. Tested the new statements mathematically on identity roofs, zero complexes,
   zero homology, and empty opens/sites. Identity roofs reduce naturality to
   equality of two cycle-characterized evaluations, not equality for arbitrary
   isomorphisms. The restriction statement uses no roof; the naturality statement
   uses no restriction and fixes all maps; the supplied component family must
   satisfy the stated differential and naturality identities. Each is strictly a separate part of
   the original argument. Read the existing Hom projections, restriction,
   internal-Hom, cycle existence and uniqueness modules; searched with different
   wording using LeanFinder, Loogle, grep, and LeanSearch (unavailable: HTTP 500).
   Existing cycle-existence and uniqueness statements are scheme-level, and do
   not state restriction compatibility or the common-source naturality equation.
   No matching Mathlib/upstream declaration was found. Verdict: true subarguments
   with explicit hypotheses and complete proof plans; two holes remain.
4. Constructed the roof comparisons using the existing quasi-isomorphism result
   and the existing internal-Hom functor; retained the restriction/roof/cycle route.
   Pruned the three direct imports listed above and accounted for every old
   direct proof dependency. The unit's realized bindings were read and are
   unchanged. Verdict: route kept; no whole-library pruning or proof gain claimed.
5. Replaced the two invalid sandbox nodes and updated the original node's proof,
   proof_deps and proof_origin to the exact reduction. New nodes describe only
   their respective statements and have current verbatim Lean signatures.
   Verdict: DAG agrees with the proof after repair.

Second reading changed the decomposition, constructed explicit roof isomorphisms,
removed unused direct imports, repaired documentation and node records, and made
hole accounting explicit. Verification results follow below.

The target compiled locally in 50.1 seconds (60-second limit). A declaration-local
heartbeat setting accounts for elaboration of the chosen product signatures;
its explanatory comment addresses the only initial linter warning. The final
delivery checks below rerun compilation with the axiom probe.

Final verification: `deliver3.py E3
Sheaf.Algebra.Homology.HomologyEvaluationRoofComparison --no-push` printed
`OK (dry run)` at commit `92631e6ac7`, with review class `CODEX` for two new
modules/nodes and two named holes. This includes the local three-module compile,
the tool's declaration axiom probe, and the stage-3 preflight.

A separate scratch copy appended `#print axioms` for both existing declarations
and both split-off declarations and compiled in 58.4 seconds. The unchanged
private helper uses exactly `propext`, `Classical.choice`, and `Quot.sound`.
The target and both named subarguments use those three plus `sorryAx`, as
expected from the two recorded holes. No further axiom occurs.
The final node-signature comparison was byte-for-byte identical for all three
nodes, and each proof_deps list matched the union of its proof-step uses.
