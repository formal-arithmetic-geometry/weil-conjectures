## What changed

Repaired return E2 from reviewer X-6e9d2 (head 6e9d2963b). Deleted the false
helper theorem
`AlgebraicGeometry.Scheme.picard_residue_homology_geometric_naturality_fixed_per_index_for_map`
and its node
`new-picard-residue-homology-geometric-naturality-fixed-per-index-for-map`.
Restored the original theorem's proof to `by sorry`, preserving its signature,
imports, and docstring. Restored the original node record; no replacement route is claimed.
Added a STATEMENT-DISPUTED comment at the original declaration.
Removed the previous delivery's obsolete second-reading assessment from this report;
the repaired delivery needs a fresh independent reading.

## Proved and sorry left

Proved 0 of the original 1 sorry; split off 0 statements. The sole remaining sorry is
`AlgebraicGeometry.Scheme.picard_residue_homology_geometric_naturality_fixed_positive_per_index`,
node `new-picard-residue-homology-geometric-naturality-fixed-per-index`.
The previous claimed closure is withdrawn: the target proof is restored to sorry,
and the false helper's sorry is deleted. Relative to the repository baseline,
no holes are closed or added. This repair claims no proof or decomposition progress.

## No longer needed

Deleted the rejected helper theorem and node
`new-picard-residue-homology-geometric-naturality-fixed-per-index-for-map`.
No imports or existing dependency modules are pruned; the original proof remains open.

## Where the brief, the DAG or earlier work was wrong

The previous helper asserted the fixed geometric equation for every chain map and
its derived image. Taking the chain map to be zero makes its induced residue
homology map zero; the helper would then force the geometric cohomology pullback
applied to every `eK z` to be zero. Since `eK` is surjective, this forces that
pullback to vanish, including identity-pullback cases with nonzero first cohomology.
The target's existential choice of derived arrow does not permit replacing it by
an arbitrary arrow or by zero. Thus the claimed reduction was invalid and has
been removed exactly as E2 requests.

STATEMENT-DISPUTED: the original target takes arbitrary additive equivalences
`eK` and `eC` without compatibility hypotheses relating them to the geometric
comparison. No proof of the original target is claimed, and its statement is
unchanged. The earlier report and second reading incorrectly accepted the false
helper as a valid reduction; their proof and progress claims are withdrawn.

## Second reading by H3

1. **Visible interface: PASS for the repair.** Compared the sole delivered Lean
   module with the repository using `diff -u`. The only difference is the
   STATEMENT-DISPUTED comment. The existing theorem's signature, visibility,
   imports, docstring and `by sorry` body are byte for byte unchanged. There are
   no definitions, new declarations, change records or adapted modules.
2. **Proof and trust: OPEN, correctly reported.** The module compiles locally
   through `lcompile.py` without errors or warnings. There is exactly one sorry,
   the original named per-index theorem listed above; no proof is claimed.
   The scratch-copy `#print axioms` check shows exactly `propext`,
   `Classical.choice`, `Quot.sound` and `sorryAx`. No forbidden
   declaration forms or data chosen from an unproved existence theorem occur.
3. **Split statements: PASS (none).** The rejected universal represented-map
   helper and its node are absent from the sandbox. No replacement helper or
   restatement is introduced. The zero-map obstruction refutes the universal
   helper when geometric pullback is nonzero; it does not by itself refute the
   original existential arrow statement. Arbitrary additive equivalences remain
   a compatibility concern, not a certified counterexample to that statement.
4. **Route and pruning: PASS for rollback, no progress claimed.** Read the
   imported residue quotient/map constructions and the geometric proof
   dependencies, and searched the library for homology maps and the per-index
   declaration. No existing result inspected establishes the equation for
   arbitrary fixed equivalences. Applying the parent fixed-family theorem would
   be circular: its proof already uses this per-index theorem. The unit
   `sk-prop-av-cube` and its `realized` fields are unchanged. No replacement
   route is asserted and no existing imports or proof dependencies are pruned.
   The original docstring is only a proof plan, not a completed proof; this
   pre-existing obligation remains open and this repair does not certify it.
5. **Nodes: PASS for rollback.** The sole delivered node is byte for byte equal
   to the repository record. Its empty `proof_deps` and original geometric
   construction plan are restored rather than claiming a proof through the
   rejected helper. No new nodes remain.

Second reading changed only this report: added the independent assessment and
explicitly distinguished the false universal helper from the unrefuted,
unchanged existential target. The repair exactly follows return E2 from
X-6e9d2; it delivers a withdrawal/dispute, not a proof or decomposition.
