## What changed

Proved `AlgebraicGeometry.exists_affine_open_invariant_component_descent` in
`Sheaf.AlgebraicGeometry.InvariantComponentAffineDescent` without changing its statement or
any existing definition. Four proved private helpers implement affine shrinking, the cartesian
restriction square, compactness of the restricted section component, and overlap compatibility.
The main proof applies the existing fpqc open-subscheme descent theorem to the singleton
cover, proves the descended open is the continuous image of the compact restricted component,
and uses the descent theorem's uniqueness clause.

The proof follows Stacks Tag 057I, `lemma-descent-connected-fibres`, from the affine shrinking
paragraph through the final quasi-compactness paragraph, with Tag 03N0 for open descent and
Tag 055M for section-component base change. The DAG's five proof steps and dependency list
now describe these actual Lean arguments. No source-library module was changed. The unused public import of BaseChangeConventions was
removed and the geometric-integrality import was narrowed to geometric reducedness; no live
or quarantined Lean module directly imports this item. The import change is documented in
`coord/changes/invariant-component-affine-descent-imports.md`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_affine_open_invariant_component_descent`
(node `lem-trf-invariant-component-affine-descent`).

Holes closed: 1. Holes added: 0. Split off: 0. Sorries remaining in the delivery: 0.
All four new helpers are private and completely proved. This is a proof from existing
library declarations, not a decomposition into new admitted statements.

Validation: the complete proof compiled through `lcompile.py` in 6.2 seconds. A temporary
`#print axioms AlgebraicGeometry.exists_affine_open_invariant_component_descent` reported
exactly `propext`, `Classical.choice`, and `Quot.sound`; the audit command was removed from
the delivered source. Delivery preflight recompiles the final import cleanup.

## No longer needed

Removed `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: no declaration from that
module is referenced; scheme pullbacks and fibres already come from the remaining statement
imports. Replaced `Mathlib.AlgebraicGeometry.Geometrically.Integral` with its smaller dependency
`Mathlib.AlgebraicGeometry.Geometrically.Reduced`, which supplies the actual hypothesis.
No integral or irreducible geometric-fibre result is used. These public import changes have
no direct Lean importers in either `lean/` or `quarantine/`; no consumer adaptation is needed.

Removed the direct proof import `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`:
no quasi-finiteness or finiteness-of-fibres theorem is used. The required finite closed-map
property instead comes from properness of finite morphisms.

`lem-galois-fpqc-covering-base-change` is no longer a proof dependency: each singleton fpqc
membership follows directly from flatness, quasi-compactness, and surjectivity of its morphism.
`def-pc-geometrically-irreducible` is no longer a proof dependency; it remains a statement
dependency because the unchanged theorem retains its geometrically reduced hypothesis.
No module is withdrawn, and no global unreachability is claimed.

## Where the brief, the DAG or earlier work was wrong

The plan's separate argument transporting geometric reducedness through residue-field
extensions is unnecessary. The actual declaration
`AlgebraicGeometry.isCompact_setOf_mem_connectedComponentIn_preimage_singleton` requires only
local finite presentation, quasi-compactness, and compact/quasi-separated total and base
spaces. The affine restricted base and base-change instances give these hypotheses.

For the component identification, the source library already proves
`AlgebraicGeometry.preimage_setOf_mem_connectedComponentIn_preimage_singleton` (Tag 055M).
This is the canonical-pullback specialization of the existing section-component cartesian
node `lem-sbc-section-component-cartesian`, now named in the DAG. It is used as a general
base-change tool, without changing or bypassing the unit route. No new node is needed.

The empty multisection case cannot satisfy the nonempty distinguished-fibre hypothesis.
For an identity multisection the same shrinking, component restriction, and uniqueness
arguments apply. The proof does not assume that the original multisection is surjective:
shrinking into its open image is essential and is proved explicitly. Uniqueness is for the
chosen affine open, exactly as in the statement. No section component is replaced by a
whole fibre, so disconnected fibres are allowed.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
