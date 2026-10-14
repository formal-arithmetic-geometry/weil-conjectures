## What changed

Copied the existing module proof into the sandbox and retained the quotient-lift
proof of `sectionRing_veronese_fraction_core`. The final definitional step is
written as `exact rfl` and compiles against the current green library.

## Proved and sorry left

The theorem `AlgebraicGeometry.Scheme.Modules.sectionRing_veronese_fraction_core`
is fully proved. No `sorry` remains in the delivered module, and no new holes were
introduced.

Holes closed: none (the declaration was already proved in the repository).
Holes added: none. Net hole reduction: zero; zero of zero originally holed
declarations proved, zero split off. This delivery validates an existing repair.

## No longer needed

None. The module's existing import of
`Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionKernel` is used by the proof.

## Where the brief, the DAG or earlier work was wrong

The repository already contains this module with a completed proof and the node is
marked as reviewed proof. The assigned item therefore had no remaining sorry to
close; this delivery only rechecks and recompiles the proof.

## Second reading by F1

1. Compared the sole delivered module against the repository with `diff -u`.
   Both existing declaration signatures and the canonical-map definition are byte
   for byte unchanged. The only differences are type inference for the local
   `hker` and `exact rfl` in place of `rfl`. No interface change record is needed.
2. Compiled the module locally with `lcompile.py`: no errors or warnings.
   Scanned for forbidden declarations and sorry: none. Compiled a scratch copy
   with `#print axioms` for `sectionRingVeroneseFractionCanonicalMap` and
   `sectionRing_veronese_fraction_core`: both list exactly `propext`,
   `Classical.choice`, and `Quot.sound`. The map is an explicit quotient lift;
   it chooses no arbitrary witness from an existence assertion.
3. No statements are split off, and no new statements or nodes are introduced.
   Read the numerator map, its surjectivity and cancellation lemmas, and the
   kernel computation. Degree zero, the zeroth generator, and zero or nilpotent
   denominators require no additional hypotheses: the quotient-kernel argument
   applies uniformly, and the generator equality is definitional after cancelling
   the tensor-power identification.
4. The proof already takes the direct Mathlib quotient-lift route, using
   `QuotientAddGroup.injective_lift_iff` and
   `QuotientAddGroup.lift_surjective_of_surjective` (checked in Mathlib's
   `GroupTheory/QuotientGroup/Defs.lean`). The sole public import supplies the
   explicit canonical-map construction and its well-definedness certificate;
   it is needed. No old proof dependency or import is omitted. The unit
   `sk-thm-curveestimate` realizes its statement with `thm-sc-proper-cohomology`
   and has no recorded steps; this below-unit proof changes none of that route.
5. Read `lem-sc-section-ring-veronese-fractions-core.json`. Its two proof steps,
   proof dependencies (kernel and explicit numerator-map node), and proof origin
   accurately describe the delivered proof. Its recorded Lean statement agrees
   with the unchanged signature. No node update is needed.

Second reading changed no Lean code: the proof is correct as delivered.
This is validation of an already completed repair, not additional proof progress.
The current repository still lists this module in `coord/repairs.txt` for review
#1428, although its canonical-map bijectivity and generator formula are already
present and proved.

Hole accounting: zero holes closed and zero holes added in this delivery;
zero of zero originally holed declarations proved, zero split off. The existing
proved declaration verified is
`AlgebraicGeometry.Scheme.Modules.sectionRing_veronese_fraction_core`.
