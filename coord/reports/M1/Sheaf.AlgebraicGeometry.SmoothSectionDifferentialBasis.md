## What changed
Proved `AlgebraicGeometry.exists_smooth_section_differential_basis` from a new
free-stabilization theorem and the existing smooth conormal sequence. The proof
chooses a finite basis, lifts its vectors through the surjective cotangent complex,
and lifts the resulting conormal classes to actual kernel elements. All signatures
of existing declarations are unchanged.

## Proved and sorry left
Closed the original hole in `AlgebraicGeometry.exists_smooth_section_differential_basis`.
Added one hole: `AlgebraicGeometry.exists_smooth_section_differential_data`, node
`lem-weil-pbc-smooth-section-stabilization-free`. This is a decomposition, with one
hole closed and one added, not a complete proof of the stabilization construction.
The new statement supplies free reduced differentials but no basis or kernel lifts.
No sorry remains in the original module.

## No longer needed
Removed proof imports `Sheaf.AlgebraicGeometry.LiftProjectiveModuleEtale` and
`Sheaf.RingTheory.SymmetricAlgebraSmooth` from the original module; their results
belong to the new stabilization item and remain required there.
Removed `Mathlib.RingTheory.Kaehler.TensorProduct` from the original module; its
base-change ingredients are needed only in the new construction item.
No original mathematical dependency node has been pruned globally: the new
stabilization node retains the construction dependencies. No unit realization is bypassed.
The original proof now directly needs only the stabilization node and
`lem-weil-pbc-smooth-conormal-sequence-exact`.

## Where the brief, the DAG or earlier work was wrong
The construction dependencies do not already give a theorem constructing the
stabilized algebra with free reduced differentials. That portion of the plan is
now a separate item. The remaining basis-lifting step is completely formalized.
A quotient can be the zero ring, so `Module.finBasis` cannot be used without an
extra rank-condition instance. Reindexing `Module.Free.chooseBasis` by its finite
index type handles this edge case without changing hypotheses.

## New nodes
`lem-weil-pbc-smooth-section-stabilization-free` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-smooth-section-stabilization-free.json`
is the construction part of Tag 07M7, first paragraph. Its module is
`Sheaf.AlgebraicGeometry.SmoothSectionDifferentialData` and it leaves one named sorry.
The docstring gives the construction, the reduced differential decomposition, and
checks the zero-quotient and rank-zero cases. No change record is needed.

## Second reading by M1

1. Compared the delivered basis module with the repository version. Existing declaration signatures are byte-for-byte unchanged; only proof imports and the proof body changed. Verdict: pass.
2. Compiled both sandbox modules with `lcompile.py --all`; compilation succeeds. The only remaining `sorry` is the named stabilization-data theorem, and no forbidden declarations occur. The basis theorem's axioms include `sorryAx` only through that explicitly split theorem. Verdict: pass.
3. Checked the split statement and node against the Lean declaration and docstring. The stabilization-data statement is strictly weaker than the basis target (it supplies free reduced differentials but no basis or lifts), is sourced at Stacks Tag 07M7, and handles zero-quotient/rank-zero cases. No duplicate declaration was found in the repository. Verdict: pass.
4. The proof uses the stabilization-data theorem, the smooth conormal exact sequence, `Module.Free.chooseBasis`, and cotangent surjectivity. The removed imports are no longer needed by the basis proof and are retained where needed by the split module. Verdict: pass; no further pruning found.
5. DAG proof, proof dependencies, proof origin, Lean records, and unit route agree with the delivered code. The unit `sk-thm-p1` remains realized through the stabilization and basis nodes. Verdict: pass.

Changed during second reading: no mathematical changes; verified the report and compilation. The delivery closes `exists_smooth_section_differential_basis` and leaves the explicitly named `exists_smooth_section_differential_data` split.
