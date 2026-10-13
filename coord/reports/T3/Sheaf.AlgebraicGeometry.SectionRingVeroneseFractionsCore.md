## What changed

Repaired `sectionRing_veronese_fraction_core` to state bijectivity of the
canonical map from `SectionFractionPresentation` to homogeneous localization.
The map is represented by the inverse of the explicit
`sectionRingVeroneseFractionEquiv`, whose value on a class `[n, ξ]` is the
fraction `ξ / s^n`. The proof is the built-in bijectivity theorem for an
additive equivalence. The Formula import is public because the repaired public
statement exposes the constructed equivalence in its type.

## Proved and sorry left

The repaired theorem
`AlgebraicGeometry.Scheme.Modules.sectionRing_veronese_fraction_core` is
proved with no `sorry`. No new holes were added.

## No longer needed

The old `Nonempty` witness statement and its associated `Nonempty` packaging are
no longer needed. No other imports, nodes, or modules were pruned.

## Where the brief, the DAG or earlier work was wrong

Upstream review #1428 correctly identified the old conclusion `Nonempty (_ ≃+ _)`
as weakened: it did not identify the canonical fraction map or assert its
bijectivity. The repaired DAG statement and Lean declaration now identify that
map as `(sectionRingVeroneseFractionEquiv X L d s).symm`.

## New nodes

None.

## Earlier second reading (a previous round; superseded)

The repaired module compiles. The theorem states exactly the bijectivity of the
canonical inverse quotient map, and its proof is the genuine `AddEquiv.bijective`
result for the explicitly constructed equivalence. No new statements or sorries
were introduced, and the unit route through the Veronese fraction formula is
retained. The statement-change record is
`coord/changes/sectionRing_veronese_fraction_core.md`.

## Second reading by T3

1. **Interface audit.** Compared the delivered module with the repository version. The only declaration change is the documented repair of `sectionRing_veronese_fraction_core`; the public `Formula` import is required because the repaired theorem exposes `sectionRingVeroneseFractionEquiv` in its type. No unrelated signatures or definitions changed.

2. **Proof audit.** Compiled the module with the prescribed launcher. The theorem has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; its axioms are only `propext`, `Classical.choice`, and `Quot.sound`. The proof is the direct `AddEquiv.bijective` theorem for the explicit equivalence.

3. **Statement audit.** The repaired statement is true and exactly identifies the canonical fraction map as the inverse equivalence and asserts its bijectivity. No new split-off statements or nodes were added, and no existing library theorem duplicates this declaration.

4. **Pruning audit.** The proof uses the Veronese fraction formula equivalence and retains the unit route through that construction. No imported module or DAG dependency is unused, so no further pruning was available.

5. **DAG audit.** The node statement, proof, `proof_deps`, and `proof_origin` agree with the Lean declaration and proof; the statement correction is recorded in `coord/changes/sectionRing_veronese_fraction_core.md`. The realized unit route remains unchanged.

Changed during second reading: confirmed the repaired public import and direct bijectivity proof, added this audit record, and made no further code changes.
