## What changed

Proved `AlgebraicGeometry.Scheme.Modules.tensorUnit_open_degree_zero` in
`Sheaf.AlgebraicGeometry.TensorUnitOpenDegreeZero`, preserving its full signature and docstring.
Added the proof-only import `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapZeroAugmentation`.
The proof follows both steps of the existing DAG plan. A proved private helper applies the
canonical degree-zero augmentation square to a section. A second proved private helper evaluates
the supplied restriction-unit square on U, restricts the result to the whole restricted scheme,
and uses naturality of the restricted map. Composing restriction maps proves the required
section equality; applying the common augmentation and the two augmentation identities closes
the theorem. No flatness, properness, nonemptiness, or nonzero-section assumption is introduced.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Scheme.Modules.tensorUnit_open_degree_zero`
(node `lem-weil-pbc-tensor-unit-open-degree-zero`).
Both private helpers, `zero_augmentation_apply` and `restricted_unit_sections`, are proved.
There are no remaining sorries in the delivered module and no holes added elsewhere.
This is a proof, not a decomposition. The module compiles cleanly with the default heartbeat
limit using lcompile.py. Independent `#print axioms` checks cover the theorem and
both added private helpers.

## No longer needed

None. The public import of `FormalFibreCohomology` is needed by the unchanged statement.
All three recorded proof dependencies are used: the augmentation-square node, the open-choices
unit square, and the fixed tensor-pullback adjunction unit. No DAG nodes or modules are bypassed,
and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface errors found. Direct dependent rewriting of equal opens caused
expensive elaboration, so the section calculation instead uses naturality along the explicit
inclusion between those opens and composition of presheaf maps. This implements the existing
plan without changing definitions, signatures, public visibility, or file-level options.
Searches using leanfinder, loogle, grep, and local rg found Mathlib's restriction-unit and
pushforward component formulas; the project's already-proved augmentation square supplies
the cohomology calculation. No new node is needed for the proved private calculation helpers.

## Second reading by U2

1. **Interface: pass.** Diffed the only delivered module against the repository.
   The existing theorem's signature is byte-for-byte identical (checked by extracting
   the text before `:=`), and its docstring and visibility are unchanged. The only
   added import is proof-only; no definition or public import changed, and there are
   no adaptations or change records.
2. **Proof: pass.** Compiled the module with lcompile.py without errors or warnings.
   A scratch copy with `#print axioms` for `zero_augmentation_apply`,
   `restricted_unit_sections`, and `tensorUnit_open_degree_zero` compiled and reported
   exactly `propext`, `Classical.choice`, and `Quot.sound` for each, with no `sorryAx`.
   Searched the delivered source for sorry and forbidden declarations: none occur.
   The helpers prove the augmentation-on-elements formula and the supplied square's
   section equality; the final transitivity calculation uses both correctly.
   No new data is chosen from an unproved existence theorem: the augmentation helper
   applies the existing theorem to the same choices defining moduleCohomologyFMap.
3. **Split statements: pass (none).** No new public statements, nodes, or holes were
   added. Both new private helpers are fully proved. Their calculations require no
   nonempty-open or nonzero-section premise and apply to empty schemes, empty opens,
   and zero sections; the whole-open premise is precisely the original hV.
4. **Route and pruning: pass.** Independently searched Mathlib via msearch grep for
   unit naturality, restrictAppIso naturality and map composition, and searched both
   library roots for restriction-unit and augmentation calculations. Read Mathlib's
   restriction-unit component formula and the upstream ZariskiDescent unit-section
   formula. These provide ingredients, not a shorter theorem for the supplied psi
   square. The proof uses the existing augmentation theorem and D.unit_square,
   followed by presheaf naturality and composition. Both imports are needed; none of
   the three old proof dependencies is unused. Read sk-thm-p1's realized statement
   and steps: this calculation lies below that unit and preserves its route.
5. **DAG: pass.** Read lem-weil-pbc-tensor-unit-open-degree-zero and its two proof
   steps. Its proof, proof_deps and proof_origin already match the implemented
   augmentation reduction and restricted-unit section calculation; no node edit is
   needed. There are no new nodes to validate.

Restored literal signature equality by removing an extra space before `:=`.
After an intermittent 60-second dry-run timeout, supplied the fixed tensor-adjunction
unit explicitly in the call to restricted_unit_sections instead of leaving it as
an inference metavariable; this keeps the proof and definitions unchanged and
reduces elaboration work. The revised complete file compiled in 49.9 seconds.
Appended this independent review. No mathematical repair was needed. Closed one original hole and added zero holes; pruned none.

The final revised-file scratch axiom check compiled in 52.2 seconds and again showed
only the three permitted axioms for all three declarations. The dry run printed OK
and review class AUTO; its bulk axiom probe exceeded 60 seconds, so the direct
per-declaration checks provide the independent axiom evidence.
