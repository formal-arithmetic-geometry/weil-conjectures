## What changed

Reduced `AlgebraicGeometry.strictEtaleExceptionalTransport_comp` to the geometric
inverse compact-support projection cocycle. The actual assembly is a categorical
proof using injectivity of the third adjunction Hom equivalence, the counit-mate
identities for the three comparisons, and naturality. Its private general lemma is
`CategoryTheory.coefficientMate_composition`.

Added `Sheaf.Paper.StrictEtaleCompactSupportComposition`, whose single theorem
`AlgebraicGeometry.strictEtaleCompactSupportTransport_composition` states the
remaining geometric step without exceptional adjoints. It constructs normalized
composition identifications and proves only the compact-support projection cocycle;
the exceptional mate equality is proved in the assigned module.

To avoid an import cycle, relocated 38 existing coefficient-change and geometric
transport declarations unchanged to `Sheaf.Paper.EtaleCoefficientTransportInterfaces`.
The old module publicly re-exports them. Compared every moved signature and body
with the old source using `stage3_delivery.decl_table`: all are identical. The
exceptional-adjoint records remain in the assigned module. No other existing module
was edited, and all prior public imports remain. The extraction is for dependency
separation, not the compile-time limit.

The private mate-composition lemma compiled alone in 2.5 seconds. The normal
`lcompile.py --all` run completed successfully for all three modules (result
`2e4301c16d4ab043214923d1`, exit 0); no profiler or trace option remains. Private
tensor/restriction additive-instance aliases avoid repeated inference during record
elaboration. The identity mate proof explicitly normalizes composite objects and
removes its now-redundant final `rfl`; its statement is unchanged.

Change record: `coord/changes/J7-strict-etale-coefficient-transport-interfaces.md`.
The record includes every textual consumer found by the project downstream scan,
with its current holder and the unchanged effect through the public re-export.

## Proved and sorry left

One of the three original holes is closed in the assigned module:
`AlgebraicGeometry.strictEtaleExceptionalTransport_comp`. This is a decomposition,
not a net proof: one strictly simpler geometric hole is added, so the net hole
count is unchanged. The general categorical mate-composition lemma is proved.

The original holes left unchanged are:

- `AlgebraicGeometry.etaleCoefficientSystemAdjoint_scalar`, node
  `lem-pur-etale-coefficient-system-adjoint`.
- `AlgebraicGeometry.etaleCoefficientSystemAdjoint_cofinal`, the same node.

The sole new hole is:

- `AlgebraicGeometry.strictEtaleCompactSupportTransport_composition`, node
  `lem-pur-strict-etale-compact-support-composition`.

The interface module has zero holes. All earlier proved declarations and the
original scalar/cofinal statements and proof plans are retained.

## No longer needed

No module is withdrawn and no original dependency is claimed globally pruned.
The composition proof no longer needs the exceptional scalar-coherence theorem as
its immediate geometric premise: it needs the compact-support projection cocycle
and generic Mathlib mate calculus. The scalar/cofinal holes still retain their
original DAG plans, including scalar-mate and cofinal-mate dependencies.

No original import was removed from the assigned module. The new interface module
uses only its three public imports: `StrictEtaleSystemInterfaces`, Mathlib mates,
and `KFlatIndependentCoefficients`; no adjoint existence theorem is imported there.
The new geometric module imports only the interface module.

## Where the brief, the DAG or earlier work was wrong

The earlier DAG `lean.note` describes a prior attempted relocation of exceptional
interfaces, while current source still defines those records in the adjoint module
and the named interface wrapper imports that theorem module. This delivery uses the
actual source and leaves the exceptional records where they are; its new definition
node records the separate coefficient/geometric interfaces it actually relocates.

The main node's prose still mentioned four transport holes although identity
coherence is already proved. There are three starting holes, with the two scalar
and cofinal holes unchanged here.

The latest blueprint's `def-weil-exceptional-inverse-image` now defines integral and
rational exceptional operations through condensed Brown representability, rather
than its former adic-stage paragraph. The assigned strict-system statement and its
unit route are preserved; this delivery does not alter a target or retire the node
on the strength of that blueprint change.

Edge-case review of the new geometric step: the coefficient rings may be zero,
indices may repeat and need not be cofinal, and the maps need not be flat. The
proof uses only the supplied exact transports and their tensor-unit normalization.
Left-adjoint uniqueness does not cancel a scalar or require a nonzero rank.
Representative localization, rather than faithfulness of derived evaluation, is
used to compare maps. Both identity coefficient maps and repeated-index composites
retain the displayed unit normalization. No arbitrary data is chosen from the new
unproved theorem: it is only eliminated inside the proof of the proposition.

## New nodes

`def-pur-strict-etale-coefficient-transport-interfaces` owns the verbatim-relocated
coefficient maps, exact transports, quotient and inverse-image squares,
compact-support projections, and identity/composition normalization records. These
are existing definitions, not duplicate notions or arbitrary choices.

`lem-pur-strict-etale-compact-support-composition` states the geometric projection
cocycle before any exceptional adjoint is chosen. It is strictly a part of the
original composition argument. Its full proof in words explains ordinary tensor
associators, successor compatibility, localization, geometric inverse-image
normalization, open/proper mates and projection pasting. Mathlib searches
(LeanSearch, Loogle/LeanFinder and grep) found scalar-adjunction and generic mate
lemmas but no exact strict-system projection statement. The blueprint search found
no existing node with this exact geometric statement.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
