## What changed

Proved `AlgebraicGeometry.affine_chart_normalized_section_models` with its original
signature. The proof applies two strictly separate intermediate results, then proves
the Hom-coordinate portion directly. `AffineChartSectionRingPresentations` handles
only scheme/ring geometry, without modules. `AffineIsomorphicSourceNormalizedModels`
handles normalized scalar extension for an arbitrary affine destination, without
limits, upper tails, covers, or Hom comparisons.

The main proof chooses the starting section equivalences once, applies the same
model family at the limit chart and every stage, and constructs α and β by conjugating
section maps. The private `affine_hom_of_section_coordinates` proves both directions
and their inverse laws. Its affine existence/uniqueness helpers reuse the proofs in
`WeilConjectures.AlgebraicGeometry.Modules.AffineHom`, using the smaller spectrum APIs
in `WeilConjectures.AlgebraicGeometry.Modules.FaithfullyFlatDescent` and a proved
isomorphism-pushforward quasi-coherence helper. All three added imports in the main
module are proof-only. No definition or existing public signature changes.

Read Stacks Tags 01I7, 01I9, 01IA and 01IB in Section 01I6, and Tags 01ZR and 01YW.
The new docstrings give the full arguments. Small cases checked mathematically:
zero rings, zero modules, empty affine charts, identity base change, and distinct
but equivalent indices in a preorder. The initial index has equivalent representatives,
so its transition and pulled-back second projection are isomorphisms; no antisymmetry
of the original preorder is assumed.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.affine_chart_normalized_section_models`
(node `lem-pc-affine-chart-normalized-section-models`). No sorry remains in the item.
The four private helpers for quasi-coherence, affine Hom existence/uniqueness, and
coordinate conjugation are proved with no sorry.

Added two holes, each exactly a named public theorem with a new module and node:

- `AlgebraicGeometry.affine_chart_section_ring_presentations`
  (`lem-pc-affine-chart-section-ring-presentations`).
- `AlgebraicGeometry.affine_isomorphic_source_normalized_models`
  (`lem-pc-affine-isomorphic-source-normalized-models`).

This is a decomposition: one original hole closed and two strictly smaller independent
holes added, net minus one hole. The Hom equivalences and their section formulas are
proved, rather than included among the new obligations. No arbitrary data is defined
by choosing from an unproved existence result; witness extraction occurs only inside
the proof of the original existential theorem.

## No longer needed

No original import removed; no module claimed as pruned. All original public imports
support the unchanged statement or its public interface. The new three proof-only
imports are used. The original plan's affine reconstruction and pullback comparison
are still needed for the scalar-model obligation. The upper-tail limit result remains
needed for the ring-presentation obligation. `pqf-def-coherent` remains a statement
dependency for the quasi-coherence notion, but its `Coherent` module is not imported
for the proof: the quasi-coherence instances used are Mathlib's.

The full `WeilConjectures.AlgebraicGeometry.Modules.AffineHom` module is unnecessary
as an import; the smaller cycle-free spectrum APIs suffice for the local proofs.
This is an avoided import, not a claim that the module leaves the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The original plan's stated dependencies give spectrum-level affine reconstruction
and scalar extension, not the simultaneous canonical-chart ring identifications.
The two new statements make the missing geometric transport and normalized
single-destination reconstruction explicit. The original statement is unchanged.

`import_direction.py` reports that `WeilConjectures.AlgebraicGeometry.Modules.AffineHom`
already reaches this item through its broad cohomology imports, so importing it
would create a cycle. Its proofs were reused as private helpers against the smaller
`FaithfullyFlatDescent` spectrum APIs, whose import-direction check passes.

An early proof using a large nested `obtain` exceeded 60 seconds. Profiling smaller
prefixes showed that destructuring the geometric assertion was expensive. Keeping
the theorem's existing let-bound expressions local and using projections and
existential witness/specification extraction eliminated that expansion. No file,
statement or definition was split to evade the compile limit, and the limit was
not changed.

## New nodes

`lem-pc-affine-chart-section-ring-presentations` is the module-independent part of
step 1 of the original plan. It supplies ring isomorphisms, affineness, the initial
chart isomorphism, and the projection/cocone equations needed by scalar reconstruction.

`lem-pc-affine-isomorphic-source-normalized-models` is the scalar-extension portion
of step 2 of the original plan, formulated for an arbitrary affine destination and
an isomorphic starting chart. It fixes δM and δN before the destination is selected.
It makes no Hom assertion and has no inverse-system or cover hypotheses.

Both nodes preserve the original chapter/unit and trace through the existing item
to `lem-pc-rf-perfect-base-change`. The unit's `realized` arrays are empty and no unit
statement or proof step is bypassed. Their three search kinds were run through
msearch; LeanSearch's server error is recorded as unavailable. The blueprint searches
for normalized affine sections and 01ZR found no duplicate. No change record or
forced adaptation is necessary.

## Second reading by Q4

1. Compared the delivered item module with the repository version. The target declaration and all existing declaration signatures are unchanged byte for byte; only proof-only imports, private helpers, and the target proof changed. Verdict: pass.
2. Compiled all three sandbox modules with `lcompile.py --all`. There are no compiler errors, forbidden declarations, hollow definitions, or unlisted `sorry`s; the two remaining `sorry`s are the named split-off public theorems and have matching nodes and docstrings. Verdict: pass.
3. Checked the two split-off statements against the source route and small cases. They are true, strictly smaller than the original target, and needed for the geometric ring presentation and normalized scalar-model portions; neither duplicates the item. Verdict: pass.
4. Checked the proof from the target downward and reviewed imports. The proof uses the stated geometric and scalar-model results plus the smaller spectrum APIs; no unit step is bypassed, and no removable import was found. Verdict: pass.
5. Compared the DAG nodes with the Lean declarations and proof dependencies. The existing node records the new proof route, both new nodes have matching statements, sources, proof steps, and `lean` records, and the unit `realized` route is preserved. Verdict: pass.

Changed after this reading: added this second-reading record only; no Lean declarations, statements, definitions, imports, or DAG records were altered.
