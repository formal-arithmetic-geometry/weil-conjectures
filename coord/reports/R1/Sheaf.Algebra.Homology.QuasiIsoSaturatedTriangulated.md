## What changed

Proved `HomotopyCategory.quasiIso_saturated_triangulated` in
`Sheaf.Algebra.Homology.QuasiIsoSaturatedTriangulated`, preserving its entire signature.
Removed the proof-only import of
`WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`.
The four public imports supply the statement's types and are retained.
Updated the existing node's proof, proof_deps and proof_origin to the actual route.
Added the proof-only import
`WeilConjectures.Mathlib.Algebra.Homology.Localization` to reuse its proved
two-out-of-three instance. No public interface changed and no new declaration was introduced.

The two fraction calculi and triangulation compatibility follow by rewriting to the
acyclic subcategory's `trW` and inferring Mathlib's instances. MS6 follows degreewise:
one invertible composite makes the middle homology map monic, the other makes it epic,
and the abelian category is balanced. Two-out-of-three uses the proved upstream instance
`HomotopyCategory.hasTwoOutOfThreeProperty_quasiIso`. Retract stability uses the image retract under each homology
functor. The cone criterion is `ObjectProperty.trW_iff_of_distinguished`; the last two
clauses are existing localization and triangulated-functor instances.

## Proved and sorry left

Closed the sole original hole:
`HomotopyCategory.quasiIso_saturated_triangulated`
(node `lem-pur-quasi-isos-saturated-triangulated`).
One of one holes closed; zero holes added; zero split off; no sorry remains in the module.
Local single-file compilation succeeds without warnings. The delivery dry run checks
axioms and compilation on the server as well.

## No longer needed

Removed import:
`WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`.
Its node `lem-pur-quasi-iso-cone-acyclic` is unnecessary for this proof: Mathlib's
criterion applies directly to every distinguished triangle in the homotopy category.

Removed proof dependencies:
`def-weil-triangulated-category` (the required structure is already supplied by the
retained Mathlib instances), `lem-sf-derived-homology-long-exact`,
`lem-weil-pbc-derived-cohomology-ladder`, `lem-weil-pbc-five-lemma`, and
`lem-pur-quasi-iso-cone-acyclic`.
The abstract-derived-category definition, fraction-calculus result and triangulated
homotopy-category result remain represented by the Mathlib declarations used.
No Sheaf proof-dependency modules were imported for the longer cohomology-ladder route.
This reports pruning from this proof only, not global unreachability through other users.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The existing docstring and original DAG give
an unnecessarily long MS5 proof through the derived cohomology ladder and five lemma.
Mathlib's triangulated-subcategory infrastructure proves compatibility directly after
identifying quasi-isomorphisms with the acyclic subcategory's trW.
The unit `sk-def-sf-operations` has no realized statement or steps to bypass; its route
is unchanged. All universes and assumptions, including HasDerivedCategory, are preserved.


## Second reading by R1

1. Compared the complete module against the repository version and checked the theorem
   signature byte for byte. Verdict: unchanged, including universes u/v/w, Abelian A,
   HasDerivedCategory.{w} A and all nine conjuncts. There are no new definitions,
   statements or change records. The only import added in this reading is proof-only.
2. Compiled locally without errors or warnings. A scratch copy with
   `#print axioms HomotopyCategory.quasiIso_saturated_triangulated` reports exactly
   propext, Classical.choice and Quot.sound. No sorry, axiom, unsafe, opaque,
   implemented_by or extern occurs in the delivered module. Verdict: a complete proof.
   Checked the MS6 composition directions: H(f) ≫ H(h) gives Mono H(f), whereas
   H(g) ≫ H(f) gives Epi H(f); abelian balancedness applies without extra assumptions.
3. No split-off statements or new nodes exist, so no additional truth or edge-case
   obligations arise. Searched the project and upstream homotopy-category declarations.
   Found the existing two-out-of-three instance in
   WeilConjectures.Mathlib.Algebra.Homology.Localization and reused it instead of
   duplicating its proof. Retract stability uses the mapped arrow retract, in the
   correct direction. Verdict: zero holes added and zero statements split off.
4. Read Mathlib HomotopyCategory/Acyclic.lean, DerivedCategory/Basic.lean and
   Triangulated/Subcategory.lean: quasiIso_eq_trW_subcategoryAcyclic identifies the
   properties, the generic trW instances supply both calculi and triangle compatibility,
   and trW_iff_of_distinguished supplies the cone criterion for every distinguished
   triangle. Qh's localization and triangulated-functor instances supply the last
   conjuncts. All retained public imports define notions occurring in the signature;
   the upstream Localization import is plain import. The five old proof dependencies
   removed are all listed under No longer needed. Read sk-def-sf-operations.json:
   realized.statement and realized.steps are empty, and no unit route is bypassed.
   Verdict: direct route and pruning retained.
5. Compared the node JSON with the repository: only proof, proof_deps and proof_origin
   differ. The proof dependencies are precisely the union of the step uses; retained
   nodes record the Mathlib fraction calculi, triangulated homotopy category and derived
   localization. Updated the two-out-of-three step to name the actual upstream instance.
   Verdict: the node and Lean route agree; no new-node metadata is required.

Second reading changed only the two-out-of-three proof to infer_instance with its
proof-only upstream import, the corresponding DAG step, and this report.
