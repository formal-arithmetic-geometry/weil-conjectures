## What changed

Reduced `AlgebraicGeometry.exists_finitePresentation_affine_chart_object_models` to two
strictly smaller obligations, each in its own new module: algebraic descent of the
sections module on the chosen chart, and general affine realization of a supplied
algebraic model with a supplied scalar-extension comparison. The target proof proves
both charts affine, establishes quasi-coherence of the restriction by pullback, and
applies realization to the algebraic stage model. Existing signatures and visibility
are unchanged. The existing node records this route.

The new realization theorem applies to arbitrary morphisms of affine schemes and
contains no inverse-limit or stage selection argument. The new descent theorem only
produces an algebraic module and an algebraic isomorphism, with no sheaf model or
sheaf isomorphism in its conclusion. This is a decomposition, not a complete proof
of the descent mathematics. No object is defined by choosing data from an unproved
mere existence theorem.

## Proved and sorry left

Closed the sole original hole in
`AlgebraicGeometry.exists_finitePresentation_affine_chart_object_models`
(node `lem-pc-fp-affine-chart-object-models`). Two new holes are added:

- `AlgebraicGeometry.exists_finitePresentation_affine_chart_sections_model`
  (`lem-pc-fp-affine-chart-sections-model`).
- `AlgebraicGeometry.exists_finitePresentation_affine_sections_realization`
  (`lem-pc-fp-affine-sections-realization`).

Thus one original hole is decomposed into two; the net hole count is minus one.
Both remaining statements have complete natural-language proofs and sources in
their docstrings. Edge cases include zero rings, zero modules, and empty affine
charts. The index type need not be globally nonempty because the specified i gives
a nonempty upper tail. No faithfulness or flatness of transition ring maps is needed.

## No longer needed

Removed the direct proof import `Sheaf.Algebra.FinitePresentationColimit` from the
item module. Its node `lem-pc-fp-module-map-descent-affine` remains part of the
algebraic sections descent plan, so its module is not globally pruned by this
delivery. No further existing nodes or modules are shown unnecessary.

## Where the brief, the DAG or earlier work was wrong

The DAG supplies the algebraic colimit descent result but no geometric sections
interface connecting it to this chart, nor a general affine sheaf realization
interface. The reduction isolates those two missing parts. The unit has no realized
statement or steps attached to these nodes, and the unit's route is preserved.

An initial scratch interface asserting comparison for an arbitrary finitely
presented stage sheaf was false: unrelated modules can have different ranks.
That interface and its nodes were deleted and are absent from this delivery.
The final realization interface instead requires the actual algebraic comparison
isomorphism and therefore has the necessary compatibility hypothesis.

## New nodes

`lem-pc-fp-affine-chart-sections-model`, in
`lean/Sheaf/AlgebraicGeometry/FinitePresentationAffineChartSectionsModel.lean`,
is the algebraic sections part of the original chart descent argument.

`lem-pc-fp-affine-sections-realization`, in
`lean/Sheaf/AlgebraicGeometry/FinitePresentationAffineSectionsRealization.lean`,
is the general affine sheaf realization and scalar-extension comparison part.

Validation: all three modules compiled in the final dry run without warnings.
The first final preflight requested an additional LeanSearch record; both
queries returned an unavailable service (Internal Server Error), now recorded
in the nodes. The independent second reading follows below.

## Second reading by X3

1. Compared the delivered chart-model module with the repository version. The
   original theorem signature is unchanged byte for byte; only proof imports and
   the proof body changed. The two split-off modules are new declarations and
   are recorded by matching DAG nodes.
2. Compiled all three modules with `lcompile.py --all`; compilation succeeds
   without errors or warnings. A scratch axiom probe for all three declarations
   reports only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The only remaining `sorry`s are the two named
   split-off theorem proofs, with no `sorry` in any definition, and no forbidden
   declarations were introduced.
3. Checked the split-off statements against their uses. The sections-model
   theorem supplies exactly a finite-presentation module and section
   comparison; the realization theorem requires that comparison and returns
   exactly the sheaf object and isomorphism needed by the target. Their
   docstrings give sources and complete proof plans, and both have DAG nodes.
   Independent LeanFinder, Loogle, and grep searches used affine global sections,
   tilde, scalar extension, and associated sheaves as alternative terms. Mathlib
   provides tilde and its quasi-coherent equivalence, while upstream provides
   Spec pullback comparisons; none states either full split-off result. The
   existing coherent tilde presentation requires Noetherianity and does not
   assert the supplied scalar-extension comparison. No short closure was found.
4. Checked pruning and route data. The removed direct import of
   `Sheaf.Algebra.FinitePresentationColimit` is unused by the new proof; the
   node remains an indirect dependency of the sections descent plan. The
   target node's proof and proof dependencies match the Lean proof, and the
   unit route is retained.
5. Checked that node proofs, dependencies, origins, and Lean signatures agree
   with the delivered declarations; repaired the new nodes to store the
   multiline Lean signatures verbatim. Checked edge cases and interface hygiene: empty
   charts, zero rings, and zero modules are covered by the stated constructions;
   no extra hypotheses or weakened conclusions were added to the existing
   target.

Changes made during second reading: restored the original indentation in the
existing theorem signature, stored verbatim new signatures in the new nodes,
and added this review record and independent search/axiom evidence. No proof
body or mathematical statement edits were necessary.
