## What changed

Proved `AlgebraicGeometry.Scheme.finiteEtale_normalIntegral_generic_hom_full` in
`Sheaf.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull` with its exact original signature
and visibility. Added the proof-only import
`WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`; all three public imports are needed by
the original statement and remain.

The normalization of the generic-point morphism of B is B because its local rings are integrally
closed. Mathlib's smooth base-change theorem identifies the normalization of the generic
restriction of X with X. View the given generic morphism as a generic section of the finite
morphism Y ×_B X → X. The universal property of normalization extends this section and proves
its uniqueness. Project the section to Y. The pullback isomorphism handles the arbitrary
cartesian presentation Xη; hY supplies the structural equation. No connectedness, nonemptiness,
finite-type-over-a-field or Noetherian hypothesis is used.

Updated the item's node to this route and registered two already proved Mathlib tools as leaf
nodes. No existing definition or statement changed; no adaptations or change records are needed.
The unit's spreading route is unchanged: this remains the generic-action extension input.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.finiteEtale_normalIntegral_generic_hom_full`
(node `lem-sbc-normal-integral-generic-hom-full`).

No holes remain or were added. This is a complete proof, not a decomposition.
Single-file compilation succeeds. `#print axioms` reports exactly `propext`, `Classical.choice`
and `Quot.sound`, with no dependency on an unproved theorem.

## No longer needed

No imports were removed and no previously imported module or proof-dependency node was pruned:
the item's original node had no proof dependencies. The separate affine-chart construction,
componentwise integral-closure description of finite etale algebras, and manual overlap gluing
are unnecessary as new proof obligations; existing normalization results supply them.
All original public imports remain necessary for the theorem's statement.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically valid, but misses a shorter route through existing relative
normalization. The source library already proves the required normal-locus isomorphism without
any finite-type hypothesis. The blueprint node `lem-sc-normalization-over-normal-locus` mentions
finite type over a field, but its recorded, already proved Lean declaration has the general
interface needed here. This proof uses that declaration directly and changes no statement.

The initial searches found no direct full-faithfulness theorem. Mathlib's universal property and
smooth base-change theorem nevertheless close the whole argument. LeanSearch returned Internal
Server Error for both new leaf searches; this is recorded as unavailable, not as absence.

## New nodes

`lem-sbc-relative-normalization-universal-property`: an existing Mathlib leaf for
`normalizationDesc`, its two compatibility equations, and `normalization.hom_ext`. No new module
or hole. Its source is Stacks Tag 035I and the existing Mathlib construction.

`lem-sbc-relative-normalization-smooth-base-change`: an existing Mathlib leaf for
`instIsIsoNormalizationPullbackOfSmooth` and `normalizationPullback_snd`, Stacks Tag 03GV.
No new module or hole. Both nodes inherit the item's chapter and unit and refer to the same
spreading ancestor. Whole-blueprint and DAG searches found no duplicate of either tool statement.

## Second reading by Y2

1. **Visible interface — pass.** Independently diffed the delivered module against the
   repository version. The only changes are the proof body and a plain, proof-only import.
   The existing theorem signature is byte-for-byte identical; its visibility and docstring
   are unchanged. No definitions, other modules, or change records are introduced.
2. **Proof and trust — pass.** Independently compiled the module with `lcompile.py`, without
   errors or warnings. A scratch copy with `#print axioms` reports only `propext`,
   `Classical.choice`, and `Quot.sound`. Scanning the delivered Lean found no `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, `extern`, or explicit `sorryAx`. Read the section
   construction and both projection calculations, including the cancellation argument for
   uniqueness. Normalization and its descent map are actual constructions; no data is
   chosen from an unproved existence theorem.
3. **Split statements and existing tools — pass.** No statements or holes were split off.
   Read the Mathlib universal-property and smooth-base-change declarations against both new
   leaf nodes: the qcqs, integral-target, affine-target and smooth hypotheses match exactly.
   Empty and disconnected covers cause no exception: the argument uses neither a point of
   X or Y nor their integrality. With B a field it specializes to the pullback identity;
   with X empty the same universal-property uniqueness still applies. Repeated searches with
   the different query "Extend a map from the generic fibre of an etale scheme into a finite
   scheme over a normal integral base" and local searches found the normalization tools,
   but no shorter generic-extension theorem. The existing relative-normalization node
   records the construction and its properties, not these two new tool statements.
4. **Route and pruning — pass.** Read the normal-locus theorem and verified that its actual
   interface has no finite-type or Noetherian assumption. The direct normalization route
   already uses proved library/Mathlib tools and has no lower proof obligation to shorten.
   The three public imports expose the function-field, etale and finite notions used in
   the unchanged signature; the added normalization import is plain and used only by the
   proof. The original node has empty `proof_deps`, so the report's pruning list is complete.
   Read `dag/units/sk-prop-input-spreading.json`: this remains the generic-action extension
   input and changes no spreading step or unit record. Its currently empty `realized` arrays
   are existing state, not a modification made by this delivery.
5. **DAG agreement — pass.** Compared the existing node: only `proof`, `proof_deps` and
   `proof_origin` change. The three dependencies describe precisely normal-locus triviality,
   smooth base change and normalization descent/uniqueness used in Lean. Both new Mathlib
   leaves have their source, complete argument, searches, creation provenance, ancestor,
   chapter, unit and existing Lean declarations. Their statements match the source types;
   neither introduces a new Lean statement or duplicates the item.

Second reading changed only this report and appended independent search evidence. No repair
of the Lean proof or DAG was needed. Independently confirmed one original hole closed and
zero holes added, with no dependencies pruned.
