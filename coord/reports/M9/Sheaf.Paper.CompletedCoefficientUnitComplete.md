## What changed

Filled `WeilConjectures.completedCoefficientUnit_completionUnit_isIso` in
`Sheaf.Paper.CompletedCoefficientUnitComplete`, preserving its signature and public imports.
All helpers added to the item module are private and proved. No existing definition,
instance, attribute, target statement, other module, or other node changes.

The proof first shows the single coefficient unit is Good, using the monoidal unitor,
the site-tensor comparison, and bounded-above flat K-flatness. It reuses the proved
ordinary coefficient-cone and normalized scalar-extension helpers from
`Sheaf.Paper.CompletedFreeCellOrdinaryLimit` directly on the unit. Epimorphic
augmentations prove successor naturality of the resulting levelwise isomorphisms;
postcomposition transfers the limit property and degreewise epimorphic transitions.
The proved degreewise surjective-tower, product-comparison, kernel, and cocone-lift
helpers from `Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic` then show that the
specified `(quotients, 0)` Roos augmentation is a quasi-isomorphism. The actual
`completionUnit_existsUnique` normalization and cancellation of
`completionComparison` give exactly the required completion-unit isomorphism.

The node's proof, proof dependencies and proof origin now describe these steps.
Private imports expose existing proved implementation helpers only to this proof.
The extra tensor-colimit comparison and Milnor helpers are general tools for the
already specified argument; the unit record has no realized steps to bypass.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.completedCoefficientUnit_completionUnit_isIso`
(node `lem-sf-completed-coefficient-unit-complete`).

Holes added: zero. Split-off statements: zero. Holes left in the delivery: zero.
This is a proof, not a decomposition. Its existing library dependencies retain their
own independently tracked proof status.

Validation: `lcompile.py` compiled the final module cleanly in 54.7 seconds,
within the 60-second limit. Source checks confirm the exact original public
theorem signature and public imports, zero `sorry` tokens, and 100-column lines.

## No longer needed

No original public import is removed and no module is withdrawn.
The rank-one finite-product transport and the auxiliary finite-field datum from
the planned route are unnecessary: the existing proved coefficient-cone and
normalized-unit helpers apply directly to the unit. The general
`completedFreeCell_ordinaryLimit` theorem itself is not applied: its existing
coefficient-unit helpers give the specialization directly. The module
`Sheaf.Paper.CompletedFreeCellOrdinaryLimit` remains needed for those helpers.

The specific theorem `proEtale_surjectiveTower_derivedLimit`
(node `lem-weil-proetale-surjective-tower-derived-limit`) is not invoked;
the proved degreewise epimorphic-tower helpers in
`Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic` supply exactly the needed
complex-level argument. The surjective-tower module remains a transitive import
for its sheafification instances, so no module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was wrong. The planned auxiliary finite-field choice and
rank-one product are avoidable with existing proved implementation lemmas.
The published assumptions on T are retained verbatim; these helpers actually work
without using compactness, quasi-separatedness, or the invertibility hypothesis.

Short-route searches used the required leanfinder, loogle and grep services, plus
local source searches. Mathlib's completion search hits concerned unrelated ring
or uniform completions; the useful local results were the normalized scalar-unit
and generic kernel-to-mapping-fibre lemmas described above. No replacement notion
of completion or unnamed existence witness is introduced. The current blueprint's
Milnor proof was read at
`literature/blueprint/latest/blueprint/sec-proetale-coefficients/sk-prop-pe-milnor/`.
The source argument includes empty schemes and zero sheaves; no nonzero object or
sectionwise surjectivity of arbitrary sheaf epimorphisms is assumed.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
