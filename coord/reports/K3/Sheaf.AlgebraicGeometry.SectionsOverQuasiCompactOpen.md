## What changed

Proved `AlgebraicGeometry.Scheme.sections_over_quasiCompact_open` with its existing
signature and public imports unchanged. The proof constructs the power transition maps,
both Hom diagrams, the evaluation cocones, and the quotient transitions. Colimit
injectivity follows by representing an element at a stage and killing its kernel
representative at a later stage; quotient lifting supplies surjectivity.

The second reading removed the unlanded `SectionsOverQuasiCompactOpenData.lean` and
`lem-weil-pbc-sections-over-quasi-compact-open-data` node. Their theorem was false.
The surviving affine radical/range/vanishing helpers are reused via a proof-only
`import all`. Local proof steps recover affine and global eventual vanishing, since
the corresponding exported declarations were withdrawn at the upstream sync.
The existing annihilator-system and quotient-local-lifting interfaces supply the
remaining geometric input. All four existing private helpers are retained unchanged.
No definition, existing signature, visibility, or public import was changed.

## Proved and sorry left

Closed one of the item's one original holes:
`AlgebraicGeometry.Scheme.sections_over_quasiCompact_open`
(node `lem-weil-pbc-sections-over-quasi-compact-open`).
Added zero holes. There are no `sorry`s in the delivered module and no split-off
statements. The false, unlanded
`AlgebraicGeometry.Scheme.sections_over_quasiCompact_open_data` was withdrawn,
not counted as a proved hole. This is a reduction to existing library obligations,
not a claim that the whole import closure is axiom-complete.

The scratch-copy axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound` for all four existing private helpers. The target additionally has
`sorryAx` from existing imported obligations: in particular the surviving private
`powers_range` in `IdealPowerEvaluationAffineEventuallyZero` is still open, and
`ideal_power_quotient_local_lifting` also has `sorryAx`. No such obligation is added
or altered by this delivery. `ideal_power_annihilator_system` itself uses only the
three permitted axioms.

## No longer needed

Removed the direct proof-only import
`Sheaf.AlgebraicGeometry.IdealPowerEvaluationEventuallyZero` and the corresponding
old direct proof dependency `lem-weil-pbc-ideal-power-evaluation-eventually-zero`:
the exported declaration is absent after the upstream sync, and the target now
proves its needed step locally. Its module remains a transitive import through
quotient lifting; no whole-library pruning is claimed.

Removed the redundant proof-only import
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`; the needed representative
API is available through the retained filtered-colimit import.
All other old `proof_deps` are retained. The original `homDiagram` and
`colimit_eval_injective` helpers are used by the repaired proof. The unlanded Data
module/node were withdrawn, not pruned from the published library.

## Where the brief, the DAG or earlier work was wrong

The first worker's `sections_over_quasiCompact_open_data` omitted the condition
that U is the entire stalk-surjectivity locus. Its assumptions hold for the unit
ideal and U empty on Spec(k), with F the structure sheaf. The power transitions are
identities, so the first Hom colimit is the nonzero additive group k, whereas the
section group on U is zero. The claimed injection is false. This also shows that
merely adding the missing condition and repackaging the whole hard conclusion
would not constitute the required proof reduction. The false theorem and node
are removed entirely; their earlier report and second-reading claims are superseded.

The upstream sync withdrew the public affine and global eventual-vanishing
declarations. Their surviving private affine helpers and the upstream
`Modules.powers_qc` suffice for local proofs of these steps in the target.
No other group's module is edited, and no withdrawn API is duplicated publicly.

## Second reading by K3

1. Compared the delivered module with the repository by diff and extracted the
   declaration headers. Every existing declaration signature is byte-for-byte
   unchanged, including the target and all four private helpers. Existing helper
   bodies and all public imports are unchanged. Verdict: pass after repair.
2. Compiled the repaired module using `lcompile.py`; no errors or warnings.
   There are no local holes, new definitions, or forbidden declarations/options.
   A scratch copy checks the axioms of every declaration: the four helpers use
   only the permitted axioms; the target also uses existing imported `sorryAx`,
   disclosed above. All choices used for diagrams are explicit constructions or
   inverses of proved bijections; the annihilator witnesses come from the proved
   `ideal_power_annihilator_system`. Verdict: pass with the recorded existing
   downstream proof obligations.
3. Tested the proposed split on the unit ideal and empty open, found the
   counterexample above, and removed it and its node. No new statement or hole
   remains. Searched Mathlib via LeanFinder for the filtered-colimit kernel
   criterion and via grep for power/Hom APIs; searched the project for existing
   vanishing interfaces. The existing short representative proof uses Mathlib
   directly and the existing geometric helpers are reused. Verdict: pass after
   removal of the false split.
4. Read the proof from the target downward, retaining the complement,
   annihilator, affine vanishing and finite-cover argument, and quotient lifting
   route of Properties 01PQ. Removed the unused imports listed above and
   accounted for every old direct proof dependency. Checked
   `dag/units/sk-thm-p1.json`: this node is below the unit's realized steps;
   no unit statement, step, or cited-unit route is bypassed or changed.
   Verdict: pass.
5. Updated the target node's `proof`, `proof_deps`, and `proof_origin` to describe
   the actual local affine/global vanishing proofs and both constructed diagrams.
   Its statement and Lean signature record are unchanged. No new nodes or change
   records are needed. Verdict: pass.

Changed during second reading: removed the false Data theorem/module/node,
replaced its application with the real diagrammatic proof from existing lower
obligations, recovered missing vanishing steps locally, retained the correct
original private helpers, pruned redundant direct imports, and corrected the
DAG and report.
