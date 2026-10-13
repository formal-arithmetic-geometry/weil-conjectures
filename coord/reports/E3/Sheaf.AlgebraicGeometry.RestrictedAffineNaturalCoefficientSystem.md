## What changed

Replaced the target theorem's `sorry` with the concrete restricted affine construction from
`RestrictedAffineCoefficientSystem`. The construction supplies the pullback diagram, limit,
compactness, affine transitions, degree-zero complexes, cone comparison, and coefficient colimit.
Added the stage-arrow clause as `restricted_affine_stage_naturality`; it remains a named intermediate
statement because its expanded naturality proof is not completed in this session.

## Proved and sorry left

The target `exists_restricted_affine_natural_coefficient_system` is reduced to the concrete
construction and the stage-arrow intermediate theorem. The remaining `sorry` is
`restricted_affine_stage_naturality` in the item's module, with node
`lem-sbc-restricted-affine-natural-coefficient-system-stage`. The import visibility change is recorded in `coord/changes/imports.md`.

## No longer needed

No additional imports beyond `Sheaf.AlgebraicGeometry.RestrictedAffineCoefficientSystem` are used
by the target proof. The lower single-coherence modules are reached through that import.

## Where the brief, the DAG or earlier work was wrong

The DAG plan treats the stage-arrow equation as part of the same construction, but the existing
concrete coefficient-system theorem only proves the cone-leg equation. The missing stage equation
therefore had to be split into a strictly smaller named intermediate theorem.

## New nodes

`lem-sbc-restricted-affine-natural-coefficient-system-stage` records the missing stage-transition
naturality statement and its source/proof plan.

## Earlier second reading (a previous round; superseded)

The target signature was checked against the DAG node: all scheme, directedness, coefficient,
cone, colimit, complex, lower-bound, comparison, cone-leg, and stage-arrow clauses are retained.
The new intermediate statement is strictly the stage-arrow equality and is exactly the missing
clause used by the target reduction. The unit route through the concrete restricted coefficient
construction is preserved.

## Second reading by E3

1. **Statements and interfaces:** Compared the delivered module with the repository version. The
   target theorem signature is byte-for-byte unchanged; only its proof and proof-only imports were
   changed. The new stage theorem states exactly the missing stage-transition equality.
2. **Proof and axioms:** Compiled the module with `lcompile.py`; it compiles cleanly. The target
   proof contains no `sorry` and delegates the construction to the existing concrete coefficient
   system. The stage-transition theorem remains the sole documented split-off `sorry`, with its
   source and blueprint node.
3. **New statements:** Checked the stage theorem's hypotheses and conclusion against the target's
   final conjunct. It is a strict intermediate clause, rather than a restatement of the complete
   target, and its node records the Stacks Project source and proof plan.
4. **Pruning and imports:** The concrete coefficient-system module is the only proof dependency
   used by the target proof. Its import is private; the raw cohomology import remains public for
   the declarations. The import change is recorded in `coord/changes/imports.md`.
5. **DAG and route:** The construction continues through
   `exists_restricted_affine_coefficient_system`, preserving the unit route; the stage clause is
   represented by `lem-sbc-restricted-affine-natural-coefficient-system-stage`.

No further changes were needed in this second reading.
