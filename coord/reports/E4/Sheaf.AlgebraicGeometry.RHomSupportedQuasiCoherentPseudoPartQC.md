## What changed
Proved `AlgebraicGeometry.rhom_supported_quasiCoherent_pseudo_part_qc` by unfolding the
quasi-coherence property degreewise and applying the new degreewise intermediate theorem.
Added the strictly lower degreewise statement in
`Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPartQCCohomology`, whose proof
remains available for a follow-up worker. Added the corresponding DAG node and updated the
parent node proof dependency.

## Proved and sorry left
The target theorem `rhom_supported_quasiCoherent_pseudo_part_qc` is proved. The new theorem
`rhom_supported_quasiCoherent_pseudo_part_qc_cohomology` remains `sorry`, recorded by node
`new-lem-sc-rhom-supported-qcoherent-pseudo-part-qc-cohomology`.

## No longer needed
No imports were removed. No planned proof dependency was bypassed; the target is reduced to
its degreewise affine-local calculation.

## Where the brief, the DAG or earlier work was wrong
The original node had only an informal affine-local proof step and no Lean-level declaration
for its degreewise conclusion. The degreewise theorem is a strict intermediate part of the
argument and makes the global `∀ n` conclusion compile.

## New nodes
`new-lem-sc-rhom-supported-qcoherent-pseudo-part-qc-cohomology` in
`dag/nodes/sec-picard-framework/new-lem-sc-rhom-supported-qcoherent-pseudo-part-qc-cohomology.json`.

## Earlier second reading (a previous round; superseded)
A second worker should check that the degreewise theorem is strictly simpler than the target,
that the target proof preserves its exact signature, and that the affine-local route remains
represented by the new node.

## Second reading by E4

1. **Visible declarations.** Compared the delivered target module with the repository version.
   The theorem signature is byte-for-byte unchanged; the only change is its proof and the
   proof-only import of the new degreewise module. The added module has a new declaration and
   does not alter an existing interface.
2. **Compilation and proof form.** Compiled both sandbox modules with `lcompile.py --all`;
   both compile cleanly. The target has no `sorry`; the only remaining `sorry` is the named
   `rhom_supported_quasiCoherent_pseudo_part_qc_cohomology`, which is recorded by its node.
   No forbidden declarations or hollow definitions occur. The target proof reduces the
   predicate degreewise by `intro n`, exactly matching the displayed conclusion.
3. **Statements and nodes.** Checked the new degreewise statement against the target's
   `schemeDerivedQCohProperty` component: it is strictly weaker by fixing one integer degree,
   while retaining all hypotheses and the exact derived internal-Hom expression. Its source,
   proof sketch, searches, Lean record, and parent `proof_deps` agree with the delivered code.
   The statement is not a restatement of the target and no existing declaration duplicates it.
4. **Pruning and route.** The proof uses the intended degreewise affine-local calculation,
   and the parent node now records that intermediate node as its sole proof dependency. No
   prior import or DAG dependency is unused, and the unit remains `sk-thm-picard-duality`.
5. **Axioms and delivery scope.** The compiled proof introduces no axioms beyond those allowed
   by the project; the unresolved lower theorem is explicitly split off with a source and
   natural-language proof. The delivery contains only the target module, the new lower module,
   its node, and this report.

Changed after this reading: added this review record; no Lean statements, definitions, or proof
content required repair.
