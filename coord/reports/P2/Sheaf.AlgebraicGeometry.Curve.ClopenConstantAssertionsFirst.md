## What changed

Proved `AlgebraicGeometry.IsCurve.clopen_first_four` directly from
`Etale.finiteCoproductCohomologyAssembly`, constant-sheaf pullback isomorphisms,
geometric-stalk pullback isomorphisms, and constructible pullback. The product
coordinates are bijective in every degree. Component assertions prove the three
vanishing clauses and finite-product finiteness. Added only proof imports:
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
`WeilConjectures.ConstructibleSheaf.Pullback`, and
`Sheaf.Paper.FiniteCoproductCohomologyAssembly`.

## Proved and sorry left

Closed `AlgebraicGeometry.IsCurve.clopen_first_four`, the only original hole.
No holes remain in the delivered module; no holes are added elsewhere.
The second reader also closed the provisional
`AlgebraicGeometry.IsCurve.clopen_vanishing_transfer` and
`AlgebraicGeometry.IsCurve.clopen_finiteness_transfer`, then incorporated their
arguments into the original theorem and removed their new modules and nodes.
This is a proof, not a decomposition: one original hole closed, zero added.
`#print axioms AlgebraicGeometry.IsCurve.clopen_first_four` returned exactly
`[propext, Classical.choice, Quot.sound]`; the delivery probe also passed.
The final module compiled without warnings in 17.9 seconds. The delivery dry
run passed with review class `CODEX: changes a node file`.

## No longer needed

The old direct proof dependencies no longer used are
`lem-weil-pbc-etale-sheaf-clopen-product`,
`lem-weil-pbc-finite-pushforward-cohomology`, and
`lem-weil-pbc-cohomology-pullback-functorial`. They have been removed from this
node's `proof_deps`; the first can still occur transitively in cohomology assembly.
The repository version has no imports to remove: its sole public import remains.
No claim is made that any old module leaves the targets' import closure.
The provisional `ClopenTransferVanishing` and `ClopenTransferFiniteness` proof
imports, modules, and their two new decomposition nodes have been removed.

## Where the brief, the DAG or earlier work was wrong

The first delivery unnecessarily replaced one hole by two. Existing finite
coproduct cohomology assembly suffices, with explicit transport of coefficients
and the conditional hypotheses. Both new nodes also copied the parent's full
statement and an unrelated old review record; removing them resolves those faults.
The old node's plan omitted the explicit stalk comparison needed for the primary
and invertible-order torsion conditions. The corrected proof records that step.

## Second reading by P2

1. Compared the delivered module with the repository using `diff`. The original
   declaration signature and public import are byte-for-byte unchanged. No public
   definition or other module is changed. Only its proof and proof imports change;
   the node changes only its owned proof fields and Lean provenance.
2. Compiled the final module with `lcompile.py`. No errors or warnings, no `sorry`,
   no forbidden declaration forms, and no hollow definitions. Explicit axiom check
   and delivery probe verify only the three permitted axioms.
3. No split-off statements remain. Checked the provisional clauses against C1-C4:
   closed pieces of an affine scheme are affine; primary and invertible-order
   torsion transport through linear stalk isomorphisms; constructibility pulls
   back; finite products preserve subsingleton and finite types. Empty index,
   empty pieces, singleton partition, zero coefficients, and characteristic-zero
   (vacuous C3) cases cause no extra hypothesis. Independent LeanFinder, Loogle,
   Mathlib grep, and library searches located the coefficient comparisons and
   finite-product route. LeanSearch was unavailable; no conclusion was inferred
   from that service failure.
4. Replaced the two provisional holes with actual arguments, consolidated their
   shared product coordinates into the original theorem, and removed both new
   modules and nodes. The remaining imports each supply a used declaration.
   Listed every removed old direct dependency above. Read
   `dag/units/sk-thm-p1.json`, including `realized`: the curve-calculation route
   is preserved, and no unit realization is bypassed or changed.
5. Updated the existing node's proof steps and `proof_deps` to the finite
   coproduct, constant pullback, stalk comparison, and constructible pullback
   declarations actually used. There are no new nodes to validate.

Second reading changed the proof from a decomposition into a direct proof,
removed the two provisional modules and nodes, corrected the node's dependency
route, and rewrote this report to record one hole closed and zero added.
