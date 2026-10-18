## What changed

Proved `DerivedCategory.rlim_perfect_complete` in
`lean/Sheaf/RingTheory/RlimPerfectComplete.lean`, with the existing signature and all
five existing definitions unchanged. The import and local-command change record is
`coord/changes/r1-rlim-perfect-complete-imports.md`. The reconstruction module is
held by B4 and is unchanged. A proved private helper projects its generic result
to `InitialReductionModel`, a private record containing just the bounded-above
finite-free model, its marking and its first reduction. This avoids expensive
elimination of the concrete adic tower's eleven nested existential witnesses.
Updated the item's proof steps and dependencies in
`lem-weil-pbc-rlim-perfect-complete.json` to match the Lean argument.

The proof constructs the unique compatible quotient lift from adic completeness,
checks the square-zero transition kernels, and applies the stated pseudo-coherent
inverse reconstruction. A bounded finite-projective complex is pseudo-coherent by
the existing finite-cone free-model theorem: the cycles of each eventually exact
finite-projective cone are finite by the proved source-library lemma
`CochainComplex.projective_finite_ker_d_of_exactAt`.

For perfectness, the reconstructed finite-free model and the bounded projective
model of the first quotient have the same residue-fibre homology. The proof uses
bounded-flat K-flatness, invariance of scalar-extension homology between K-flat
models, iterated scalar extension, and the source library's derived tensor model.
The uniform interval is `[min a b, b]`, so no unproved ordering of the original
support bounds is assumed. The stated maximal-fibre criterion then gives
perfectness. Scalar annihilation on quotient complexes gives the hypotheses of the
stated nilpotent-torsion completeness theorem. Transition compatibility follows
directly from the first two arrows of the Roos triangle and the adjunction unit
formula. All local helpers are proved; none introduces a postponed statement. The final
single-module server compile passed cleanly in 18.8 seconds.

The existing generic tools `lem-pc-ring-finite-cone-free-model`,
`lem-pc-module-bounded-flat-kflat`, and
`lem-sc-kflat-scalar-extension-derived-iso` are used for module-complex operations;
no proper-base-change unit statement or unit proof step is bypassed. Their
cross-unit tool use is reported here for the maintainer's review; no new approval
has been written into `tool_uses`.

## Proved and sorry left

Closed the single original hole:
`DerivedCategory.rlim_perfect_complete`
(`lem-weil-pbc-rlim-perfect-complete`). Added zero holes and split off zero
statements. No `sorry` remains in the item module. The proof uses the existing
declared reconstruction, maximal-fibre criterion and torsion-completeness theorems;
their upstream obligations are unchanged. No other Lean module is delivered.

## No longer needed

Removed these direct imports:

- `Sheaf.Algebra.Homology.KFlatTelescopeClosure`: replaced by the bounded-flat
  module-complex criterion (`lem-pc-module-bounded-flat-kflat`). The broader
  `lem-pc-kflat-closure` is no longer a proof dependency of this item.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`: replaced by
  `Sheaf.Algebra.Homology.KFlatScalarExtensionDerivedIso` and ordinary extension
  composition; no independent sheaf coefficient construction is required.
- `Sheaf.Algebra.Homology.DerivedChangeOfRings`: no sheaf scalar-extension theorem
  is used. Removed `lem-pur-derived-change-of-rings` from this item's proof
  dependencies and withdrew its old tool approval, while preserving the node's
  unchanged statement dependencies.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`: the statement
  already uses the source library's `DerivedCategory.IsPerfect`; the separate
  generalized-universe predicate is not used by the proof.

Both obsolete top-level tool approvals, `lem-pc-kflat-closure` and
`lem-pur-derived-change-of-rings`, were withdrawn. Other nodes may still need the
removed modules: this report claims pruning of this item's direct requirements,
not global unreachability. `tools/downstream.py` reported zero downstream modules
for the item, so removing its unused public sheaf change-of-rings import requires
no consumer adaptation.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or public definition changed. Eliminating the concrete
reconstruction witnesses exceeded the single-file time limit. The private helper
instead performs that projection with generic rings and ring maps, then specializes
the resulting small record to the adic tower. It introduces no arbitrary global
object: both the record and its projection helper are private proof support, and
the helper proves existence directly from the stated reconstruction theorem.
The planned sheaf-level K-flat and
change-of-rings tools are unnecessary because existing module-complex declarations
provide precisely the scalar-extension homology comparison used here. The final
compatibility clause needs only the supplied Roos triangle, not the additional
strict-model comparison from reconstruction. These simplifications are reflected
in the node copy. The target statements and the proper-base-change unit route are
unchanged.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
