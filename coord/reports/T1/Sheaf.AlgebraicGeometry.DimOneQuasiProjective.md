## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.DimOneQuasiProjective` with a proof
following the existing three-step plan. Transport the dimension bound by
`Scheme.dim_eq_topologicalKrullDim`, obtain an ample invertible module, apply
`IsAmple.exists_immersion_affine_base`, and factor the resulting immersion with Mathlib's
`IsImmersion.isImmersion_iff_exists`. Define the intermediate structure morphism by
composition with the projective-space projection and prove its compatibility by associativity.
All signatures, docstrings, definitions, and imports are unchanged.
Checked the source proof at https://stacks.math.columbia.edu/tag/0A25; it follows exactly
the ample-sheaf and projective-space immersion route used here.
Updated the node's proof and dependencies to include the dimension comparison.

## Proved and sorry left

Proved `AlgebraicGeometry.exists_closed_open_immersion_projectiveSpace_of_dim_le_one`
(node `lem-sc-dim-one-quasi-projective`). No sorry remains in the delivered module;
no new sorry or module is added. The proof uses the existing statements
`AlgebraicGeometry.Scheme.dim_eq_topologicalKrullDim`,
`AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_dim_le_one`, and
`AlgebraicGeometry.Scheme.Modules.IsAmple.exists_immersion_affine_base`, which still
have sorry in their existing modules. Those dependencies remain future stage-3 items.

## No longer needed

None. Both existing proof imports are used; all existing proof dependencies remain needed.
The tensor-power isomorphism supplied by the ample-to-immersion theorem is unused, but its
module and node remain needed for the immersion itself. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG omitted `lem-pc-scheme-dimension-local-rings` from proof dependencies even though
this theorem states its bound using `Scheme.dim` and the ample-existence theorem uses
`topologicalKrullDim`. The existing dimension comparison closes that gap without new
statements. Added that dependency and described the Lean factorization and compatibility
calculation explicitly. No false or disputed statement was found.

## Second reading by T1

1. Compared the delivered module with the repository version: the theorem signature,
definitions, docstrings, and imports are unchanged; only the proof body differs.
Verdict: pass.

2. Compiled the module with `lcompile.py`; it has no errors and no local `sorry`,
`axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The target's axiom report
contains only the permitted axioms together with `sorryAx` from still-open dependencies.
Verdict: pass.

3. Checked the node and library declarations for duplicate split-off results and tested
the dimension transport used by the proof. No new statement was introduced, and the
existing theorem is unchanged and true. Verdict: pass.

4. Reviewed the route from the target downward: the ample-sheaf theorem, affine-base
immersion theorem, and immersion factorization are all used, with no shorter available
route found. Imports are needed for the statement or proof, and no old dependency can
be pruned. Verdict: pass.

5. The node proof steps and `proof_deps` match the Lean proof, including the dimension
comparison dependency; the unit route and its realized steps remain intact. Verdict:
pass.

Changed only this second-reading report section; no Lean or DAG repair was needed.
