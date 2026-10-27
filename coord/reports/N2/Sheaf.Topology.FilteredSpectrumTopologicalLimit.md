## What changed

Prove `AlgebraicGeometry.filteredSpectrumTopologicalLimit` in
`Sheaf.Topology.FilteredSpectrumTopologicalLimit` by the compatible-prime construction of
Stacks Tags 0CUE and 0CUF. Membership independence uses Mathlib's elementwise filtered-ring
colimit theorem; common upper stages prove the ideal and primality laws. The comparison is
bijective, continuous, and open because every principal open is represented at a stage.
Mathlib's quasi-compactness of affine morphisms proves the compact-open preimage clause.
Only proof imports of `Mathlib.Algebra.Category.Ring.FilteredColimits` and
`Mathlib.AlgebraicGeometry.Morphisms.Affine` are added.

Correct the missing relative size condition by adding `[Small.{v} I]` to the theorem.
The change record is `coord/changes/N2-filtered-spectrum-relative-smallness.md`.
No existing Lean theorem calls this declaration. No consumer adaptation is necessary.
The node records the same correction, its complete citer audit, and the implemented proof.

## Proved and sorry left

The single original hole is in `AlgebraicGeometry.filteredSpectrumTopologicalLimit`
(node `lem-a1-filtered-spectrum-topological-limit`). Its full proof is written after the
necessary size correction. This is a statement repair followed by a proof of the corrected
statement. Zero `sorry` remain and zero holes or new lemmas are added.
This does not prove the original overgeneral signature: the record explains its failure.
Validation: the delivered module compiles cleanly through `lcompile.py` in 7.1 seconds.
Zero warnings or errors; zero `sorry` in the source. The delivery runs the independent
axiom probe and preflight. No global build is run by this worker.

## No longer needed

No existing imports are removed. The proof uses Mathlib directly and introduces no imports
from `Sheaf` or `WeilConjectures`.

`lem-weil-pbc-principal-localization-open-immersion` is removed from this node's proof
route: `QuasiCompact.isCompact_preimage` for the affine scheme morphism already proves
the complete compact-open preimage clause. No separate use or import of
`Mathlib.AlgebraicGeometry.OpenImmersion` is needed. This is a local dependency pruning;
that node remains available for other consumers. `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact` is also no longer a direct
dependency: the compactness proof is supplied by the existing Mathlib leaves
`lem-weil-pbc-affine-morphism-permanence` and
`lem-weil-pbc-quasi-compact-morphism-preimage-qc-open`.
The elementwise colimit and affine-spectrum dependencies are retained.
No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original Lean declaration quantified over unrelated index and ring universes, despite
the source requiring a small set-indexed colimit. A colimit in the category of small rings
need not compute a larger set-indexed colimit. The rational-function-field counterexample
in the change record demonstrates the failure of the original conclusion. The corrected
Lean assumption makes the intended smallness relative to the coefficient universe explicit.
The conclusion is unchanged, and the source construction is followed throughout.

The five DAG citers retain their mathematics:
- `det-pe-wc-cover-second-stage`: Finite partitions and clopen neighbourhoods are small in the common ring/space universe; the current Lean proof in fact uses an independent direct construction.
- `lem-a1-quasi-affine-chart-limit-topology`: Its Lean index I and coordinate rings are in universe u, so Small I is automatic.
- `lem-sfb-wlocal-directed-limit-topology`: Its Lean index D and all rings are in universe u, so Small D is automatic.
- `lem-sfb-wstrict-common-component-hypercovers`: The finite-clopen-partition diagrams use the common small-site universe explicitly assumed in its statement.
- `lem-sfb-field-geometric-fibre-covering-test`: Finite subalgebras of the given small algebra form a small index poset in the algebra universe.

Edge cases: the proof assumes no nonzero stage or nonempty spectrum. A compatible family
itself supplies proper stage ideals. If there is a zero stage, it has no prime, hence no
compatible family; if the colimit is zero, the constructed proper ideal rules out a family.
Noninjective transition maps are handled by common-stage representative equality. The
empty principal open and empty compact open require no separate nonemptiness hypothesis.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
