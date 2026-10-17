## What changed

Restored the exact original signatures and complete proofs of
`AlgebraicGeometry.Scheme.ideal_power_evaluation_eventually_zero` and
`AlgebraicGeometry.Scheme.ideal_power_quotient_local_lifting_section`, which the
e47efb5a5 sync had commented out. The item's unchanged theorem
`AlgebraicGeometry.Scheme.ideal_power_quotient_local_lifting` now proves its two
conjuncts using these theorems and upstream quasi-coherent cokernel closure.

The second reading found M4's restored, proved
`ideal_power_local_maps_eventually_agree`. Global evaluation vanishing applies
it to `phi.over(top)` and zero on the compact top open; naturality gives equal
evaluation and componentwise extensionality gives the global zero equation.
Section lifting uses it directly on each compact affine overlap before gluing.
This removes all copied private affine and overlap proofs.
No statement, definition, public import or target signature changes.

All three final files compile locally through `lcompile.py`. Scratch copies
with `#print axioms` appended show only `propext`, `Classical.choice` and
`Quot.sound` for all three public theorems (3.7, 35.9 and 5.3 seconds).
Change record: `coord/changes/ideal-power-local-lifting-upstream-repair.md`.

## Proved and sorry left

Closed 1 of 1 item holes:
`AlgebraicGeometry.Scheme.ideal_power_quotient_local_lifting`
(node `lem-weil-pbc-ideal-power-quotient-local-lifting`).
Added 0 holes; split off 0 statements. No `sorry` remains in any delivered module.
The two supporting theorems restored from commented text are not counted as
additional holes closed. Their nodes are
`lem-weil-pbc-ideal-power-evaluation-eventually-zero` and
`lem-weil-pbc-ideal-power-quotient-local-lifting-section`.
The axiom checks also establish that these three proofs have no imported
`sorryAx` dependency.

## No longer needed

Global evaluation vanishing no longer directly uses these old proof dependencies:

- `lem-weil-pbc-ideal-power-evaluation-affine-eventually-zero`
  (`Sheaf.AlgebraicGeometry.IdealPowerEvaluationAffineEventuallyZero`);
- `lem-weil-pbc-formal-polynomial-power-lifts`
  (`Sheaf.AlgebraicGeometry.FormalPolynomialPowerLifts`);
- `lem-weil-pbc-glue-sheaves-of-modules`
  (`Sheaf.Topology.GlueSheavesOfModules`).

Its only proof import and proof dependency is now the proved local eventual-agreement
module/node. It also removes the direct proof import of
`Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
The power-lift and gluing modules remain needed elsewhere in this delivery.

Section lifting removes its unused direct imports of
`Sheaf.AlgebraicGeometry.IdealPowerEvaluationEventuallyZero`,
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage` and
`WeilConjectures.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings`.
It retains every old proof-dependency node, including the now restored local
agreement theorem. The second reading also removed its redundant direct
quasi-compact proof import, after verifying that Mathlib's quasi-separated module
publicly imports it. All proof-only imports use plain `import`; no `import all`
is needed.
The item retains its three proof imports. No whole-library pruning count is claimed.
The unit's realized route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The upstream sync commented out both supporting declarations and cleared their
node attachments, so the item alone could not compile. The signatures preserved
in the source and `lean_before_upsync_e47` are restored unchanged.
The first worker's replacement local calculations were valid, but M4 has since
restored local eventual agreement, making those calculations redundant. Its
application on the top open also avoids the separate affine-vanishing module.
The proof records and this report now describe the resulting shorter route.

## Second reading by H1

1. Compared all three delivered modules with the repository using `diff` and
   exact signature extraction. The item's signature and both restored signatures
   are byte-for-byte identical to their original source text; public imports are
   identical. No definitions or target statements change. The restoration and
   consumer review are declared in the change record. Verdict: pass.
2. Compiled all final files and separate scratch copies with appended axiom checks.
   Every delivered theorem has only `propext`, `Classical.choice`, `Quot.sound`;
   there is no `sorry`, prohibited declaration, hollow definition or arbitrary
   data construction. Verdict: pass.
3. No statements or holes are split off and no new declarations or nodes are added.
   Checked the reused theorem's exact hypotheses and its standard-axiom proof.
   The top-open specialization needs compactness only; section lifting supplies
   compact overlaps from quasi-separatedness. Empty schemes/overlaps, zero and
   unit ideals, and degree zero need no extra assumption. Verdict: pass.
4. Read the proof downward from the item, searched the source with different
   terms and ran LeanFinder for extending ideal-power maps vanishing on the
   complement. The Mathlib hits concern structure-sheaf localization, not this
   module-valued result. Reused the restored library eventual-agreement theorem,
   removed duplicated calculations and unused proof imports. Checked
   `dag/units/sk-thm-p1.json`: no realized statement or step is bypassed.
   Every removed old proof dependency is listed above. Verdict: pass after repair.
5. Checked the three Lean attachments, proof steps, proof-dependency unions and
   origins. Restored the two original attachments, changed evaluation's route
   to local agreement against zero, and restored section lifting's original
   dependency list and finite-cover gluing route. Only the stage-3-owned node
   fields change. No new node is required. Verdict: pass after repair.

Second-reading changes: reuse the restored public local-agreement theorem in
both supporting proofs; remove all duplicate private helpers and their imports;
update the DAG, report and change record. The item's proof remains unchanged.
