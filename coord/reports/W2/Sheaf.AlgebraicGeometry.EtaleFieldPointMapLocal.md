## What changed

Completed `AlgebraicGeometry.etaleFieldPointMap_local` in
`Sheaf.AlgebraicGeometry.EtaleFieldPointMapLocal`, preserving its statement and visibility.
Added the proved private helper `singleton_chart`. It constructs the singleton open as
Spec of the residue field directly over K, using existing quasi-finiteness, reducedness,
and residue-field étaleness results. The main proof realizes the embedding map using
`FieldTheory.finite_separable_extension_galois_classification` and transports it through
Spec. All new data is constructed explicitly or extracted from proved theorems.

Replaced the proof import `Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`
with `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale`. Kept the public geometric
action import and the proof-only Galois classification import. Updated the item's DAG
proof, proof dependencies, and proof origin to match this route. No interface or target
changes, no new nodes, and no forced adaptations.

The sources were checked at [Stacks 03QR](https://stacks.math.columbia.edu/tag/03QR)
and [Stacks 02GL](https://stacks.math.columbia.edu/tag/02GL).

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.etaleFieldPointMap_local`
(node `lem-exc-etale-field-point-map-local`). This is a proof, not a decomposition:
zero holes added or split off. The private helper `AlgebraicGeometry.singleton_chart`
is proved. No `sorry` remains in any delivered module.

The module compiles without warnings through `lcompile.py`.
The delivery dry run performs the declaration axiom probe and mechanical preflight.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints` and
proof dependency node `lem-weil-pbc-etale-fibre-discrete-separable-points` from this item.
The proof no longer needs the general fibre decomposition, canonical field-base fibre
transport, or its planned affine-product decomposition route. Other consumers may still
need those modules; no claim is made that they leave the entire targets' closure.

The prior sandbox-only `Sheaf.FieldTheory.EtaleFieldGaloisClassificationCorollary` was
unused and syntactically malformed; it was removed from the delivery. The existing
classification's surjectivity clause is applied directly, so no corollary module or node
is necessary. The Galois classification remains needed. No realized unit statement or
proof step is bypassed (`sk-prop-h2` has no realization attached to this local lemma).

## Where the brief, the DAG or earlier work was wrong

The general-fibre specialization and transport in the earlier DAG plan were unnecessary:
the existing residue-field and quasi-finiteness tools give singleton charts directly.
The prior attempt had not changed the item's `sorry` and had no report or completed
reduction. Its unused corollary contained a missing parenthesis in a binder and reused
the classification node rather than defining an independent needed step. It is omitted.

The statement is unchanged and handles the edge cases: an empty source supplies no x;
a nonempty source supplies an embedding and its image geometric point, so the target
component is nonempty. No finiteness assumption on either whole scheme is used, only
on each singleton residue-field extension. The identity is proved for every geometric
point p with every supplied proof hp, using extensionality in the over category.

## Second reading by W2

1. Compared the delivered module with the repository version. The theorem signature,
visibility, and all existing declarations are byte-for-byte unchanged; only imports,
the private helper, and the proof body differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds without warnings. There are no
`sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations. The
helper constructs its data explicitly, and the theorem's proof uses only the stated
classification and étale-reducedness results. Verdict: pass.
3. Checked the helper and main argument against the edge cases and source declarations.
The singleton chart is obtained from discreteness, reducedness, and residue-field
étaleness; finite separability and the Galois Hom classification are applied with the
correct variance. No new statement or node was added, so there is no split-off claim
to validate. Verdict: pass.
4. The proof follows the shortest available route: direct singleton residue-field
charts replace the old fibre transport, while retaining the unit's Galois
classification step. The removed fibre-discrete import and dependency are unused.
The remaining imports are required by the proof. Verdict: pass.
5. The DAG proof, proof dependencies, and proof origin now match the Lean proof; the
unit route is retained, and the existing node's statement is unchanged. Verdict: pass.

Changed in this reading: no further Lean or DAG changes; this section records the
independent checks above.
