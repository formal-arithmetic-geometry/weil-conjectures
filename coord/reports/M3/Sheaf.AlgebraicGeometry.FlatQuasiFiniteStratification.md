## What changed

Replaced the target theorem's `sorry` with a proof using the bounded flat locally quasi-finite stratification theorem. The proof defines the global strata by fibre degree, proves the filtration, disjoint cover, universal finite-locally-free criterion, and compactness by induction. Added `Sheaf.AlgebraicGeometry.QuasiFiniteDegreeUpperLocusCompact` for the affine successor compactness step.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.Hom.exists_closed_stratification_of_flat_quasiFinite`.
The new theorem `AlgebraicGeometry.Scheme.Hom.isCompact_successor_degree_locus_inter_affine` remains `sorry`; it is a strict affine descent substatement and has node `lem-weil-pbc-qf-degree-successor-affine-compact`.

## No longer needed

The proof does not use the modules for explicit open-preimage pasting, residue-field factorization, or finite locally free descent directly; the bounded stratification theorem packages the first three quarters of the argument. The original imports retained for statement compatibility are otherwise unchanged.

## Where the brief, the DAG or earlier work was wrong

The DAG treated the global gluing and compactness argument as one direct ten-step proof. The usable Lean route packages the global gluing in the bounded stratification theorem and isolates the genuinely missing affine inverse-limit descent as one new theorem.

## Second reading by M3

1. Compared the delivered module and node with the repository. The target theorem signature is unchanged; the new affine theorem is a strict helper statement.
2. Compiled both delivered modules with `lcompile.py --all`; the target has no sorry and the helper has its single named sorry. No forbidden declarations or hollow definitions were found.
3. Checked the helper statement against the affine descent step in Tag 07RZ and searched the library for duplicates; it is true, smaller than the target, and needed by the compactness induction.
4. Checked the proof route and imports. The bounded stratification theorem supplies the affine strata; the target proof retains the unit route and isolates only the missing affine descent. The bounded module is imported with `import all` because its closed-locus auxiliary theorem is private and required by the proof.
5. Checked the target node proof, dependencies, origin, and the new helper node against the Lean declarations. The target statement text was restored byte-for-byte.

Changed the bounded-stratification import only while checking minimality; it must remain `import all` for the private auxiliary declaration used by the proof. Restored the exact target statement text in the node record.

## New nodes

`lem-weil-pbc-qf-degree-successor-affine-compact` records the affine successor compactness theorem and the remaining `sorry`.
