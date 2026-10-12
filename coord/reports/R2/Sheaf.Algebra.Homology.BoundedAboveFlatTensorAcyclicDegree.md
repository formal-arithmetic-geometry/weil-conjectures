## What changed

Proved `CochainComplex.isZero_homology_mapBifunctor_of_boundedAbove_flat_sheaf` with
its existing signature and visibility unchanged. Flip the tensor double complex;
flatness gives exact tensor-right functors, so its columns are acyclic. Convert
both upper bounds to strict support bounds and apply the existing bounded-above
columnwise total-comparison theorem to the map from the zero double complex.
The source total is zero, and the signed total flip isomorphism transports
exactness back to the original tensor total.

Replaced the proof import of
`WeilConjectures.Mathlib.Algebra.Homology.TotalComplex` by
`WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns`, and added the proof
imports `Mathlib.Algebra.Homology.TotalComplexSymmetry` and
`WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`.
The latter supplies exact-functor preservation of acyclicity; the former
supplies `totalFlipIso`. Both original public imports remain necessary for
the statement and the sheaf tensor zero-morphism instances. Updated the
existing docstring and DAG proof to describe the actual route.

Single-file compilation succeeds. A temporary `#print axioms` probe reported
exactly `propext`, `Classical.choice`, and `Quot.sound`; it has been removed.
Removing the symmetry import failed with an unknown `totalFlipIso`, confirming
its necessity. The exact-functor import was also checked for necessity.
The unit `sk-thm-picard-semicon` has no realized nodes in its statement or steps;
this change is below the unit level and preserves its route.

## Proved and sorry left

Closed the sole original hole:
`CochainComplex.isZero_homology_mapBifunctor_of_boundedAbove_flat_sheaf`
(node `lem-pc-bounded-above-flat-tensor-acyclic-degree`).
One of one original holes proved; zero holes added or split off.
There are no remaining `sorry` declarations in the delivery, and the proved
theorem has no transitive `sorry` dependency, as certified by its axiom probe.
No signature, definition, instance, or target statement changed.

## No longer needed

Removed proof import:
`WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`.
Removed planned proof dependency:
`thm-sp-double-complex-spectral-sequences`.
The current proof also needs neither of that spectral-sequence module's
proof imports, `Sheaf.Algebra.Homology.DoubleComplexVerticalSpectralObject`
and `Sheaf.Algebra.Homology.DoubleComplexVerticalWindowHomology`.
These modules and the spectral-sequence node are unnecessary on this route;
they may remain needed by other users, so no global unreachability is claimed.
The original flatness and acyclicity definition dependencies are retained.
No other original direct proof imports or proof dependencies were removed.

## Where the brief, the DAG or earlier work was wrong

The original fixed-degree node says to truncate both complexes, translate
to the first quadrant, and use spectral-sequence convergence. A lower stupid
truncation of an acyclic complex can create homology at its boundary; mere
translation of a double complex bounded above in both indices does not make
it first-quadrant. That route therefore needs more truncation infrastructure
than its single step states. The theorem itself is correct and unchanged.
The complete existing comparison theorem in `BicomplexColumns` avoids that
gap using finite column filtrations and stabilization in degrees n-1,n,n+1.
Its name includes `isStrictlyGE`, but its actual hypotheses are uniform
strict upper bounds in both directions, which fit this item exactly.

Searches: LeanFinder returned generic exactness/support results, Loogle
returned no hits, and LeanSearch was unavailable. Source grep found the
complete existing bounded-above total comparison. Whole-DAG and blueprint
searches found the first-quadrant comparison node, whose lower-bound
hypotheses differ, and no node for the existing bounded-above comparison.
Read Stacks Tags 06YQ and 0132 online and the complete source Lean proof.

## New nodes

`lem-pc-bounded-above-double-complex-total-comparison` records the ALREADY
PROVED declaration
`HomologicalComplex₂.total.quasiIso_map_of_isStrictlyGE_of_isStrictlyLE`
in `WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns`.
It has an `existing: true` Lean record, a complete natural-language proof
by finite-column induction and stabilization, and the three search kinds.
No new Lean module, new unproved statement, or change record is needed.
The node is used as the generic closed comparison tool in the item's last
proof step. Its source is Stacks Tag 0132 and the existing source Lean proof.

## Second reading by R2

1. PASS: diffed the only delivered Lean module against the repository. The existing
   theorem signature is byte for byte identical, including all hypotheses, universes,
   conclusion and visibility. No definition, instance or target statement changed.
   The existing node differs only in proof, proof_deps and proof_origin.
2. PASS: independently compiled the module with lcompile.py, with no warnings or
   errors. A scratch-copy `#print axioms` reports exactly propext, Classical.choice
   and Quot.sound. The delivered source contains no sorry or forbidden declaration.
   The chosen zero double complex comes from the proved zero-object instance; this
   is a uniquely determined zero object up to isomorphism, not an arbitrary witness
   from an unproved existence statement.
3. PASS: no statements were split off and no holes were added. The sole new node
   records an already proved upstream comparison theorem, whose signature and
   finite-column induction/stabilization proof were checked against its source.
   Zero complexes, single columns, empty finite column intervals, and degrees above
   the sum of the bounds satisfy the comparison; the degree n cutoff n-y0-1 keeps
   all potentially nonzero summands in degrees n-1, n, n+1. Independent searches
   for quasi-isomorphism/acyclicity totalization and totalFlipIso in Mathlib and
   lean/Sheaf found no shorter applicable theorem for bounded-above sheaf tensors.
4. PASS: the proof follows exact tensor columns, finite-diagonal comparison, and
   the signed flip isomorphism. Checked the comparison source and
   [Stacks 0132](https://stacks.math.columbia.edu/tag/0132) against the bounded-above
   clause of [Stacks 06YQ](https://stacks.math.columbia.edu/tag/06YQ).
   Both public imports supply statement types or the tensor zero-morphism instances.
   Removing each new symmetry/exact-functor import independently fails compilation
   at totalFlipIso/Acyclic.map respectively; BicomplexColumns supplies the comparison
   and support-to-total construction. The removed spectral-sequence dependency is
   the only old proof dependency pruned. The unit's realized statement and step
   lists are empty and its route is unchanged.
5. PASS: checked both node files against the Lean declarations. The old node's
   proof_deps is exactly the union of its steps' uses, with the unused spectral
   sequence removed. The new node has provenance, source, searches, blueprint,
   chapter/unit and an existing Lean declaration record; it adds no Lean statement
   or axiom. Its proof and proof_origin describe the existing comparison source.

Second-reading change: corrected the introductory docstring sentence that still
called the implemented proof a first-quadrant spectral-sequence argument. It now
identifies the bounded-above case of Tag 06YQ and the actual finite-column total
comparison. The proof, signature, imports and nodes needed no repair.
