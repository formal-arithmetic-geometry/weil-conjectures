## What changed

Completed `WeilConjectures.sfOpenClosedTriangle_qbar_weil` without changing its signature.
The actual common-stage geometric Frobenius receives its exact shift structure from
`automorphismConstructibleStage_qbar`. The normalized rational triangles transport
along exact stage inclusion to the given common-stage presentation. The existing
normalized descent theorem supplies shifted cross-object orthogonality, transferred
using the literal object normalizations. The existing triangle-morphism-extension
helper then supplies the third square and uniqueness of both outer Weil structures.

Added the proved helper module `Sheaf.Paper.SfNormalizedCommonStageWeilSquares`.
Its first-two-squares theorem uses the existing simultaneous finite realization
of a Weil pair, the rational square theorem, and the natural stage/Frobenius
comparison. Two proved private categorical lemmas transport these squares through
stage inclusion and through an isomorphism of middle Weil pairs. The finite
realization theorem is used only as a generic finite-diagram tool; the source
unit's localization and exchange argument is retained. The iteration conclusions of the finite-realization source module are not used.
The stage comparison is proved privately from the defining common-stage pullback
arrow formula, reusing the published calculation in `ExtensionByZeroPunctual`
without importing that module: its broader punctual dependency route points back
to the parent theorem. No existing upstream declaration is changed or removed.

Updated the parent DAG proof and added a node for the proved helper. No existing
public definition, theorem statement, attribute, or public import was changed.
Proved private scalar helpers preserve the rational presentation formulas
while avoiding concrete inherited-module expansion. A proved generic triangle
transport helper isolates the normalization isomorphism calculation.
`Mathlib.Algebra.CharP.CharAndCard` is a private proof import for the base field
coefficient-prime unit calculation. The exactness witness is normalized to the
Frobenius wrapper before constructing the dependent existential; this avoids
repeated expansion of the large common-stage pullback. Its definition is locally
marked irreducible for the two Weil proofs, without changing its exported attribute.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.sfOpenClosedTriangle_qbar_weil`
(node `prop-sf-open-closed-triangle-all-stages`).

Added zero holes. The new declaration
`WeilConjectures.sfNormalizedCommonStageRecollement_weil_squares`
(node `lem-sf-normalized-common-stage-recollement-weil-squares`) and both private
transport helpers have complete proofs. The item and the added module have no
remaining `sorry`. Existing imported statements may still depend on `sorry`. The final main-module compile passed in 29.4 seconds. The helper also compiled
successfully. Diagnostic options were removed before this check.

## No longer needed

The qbar Weil proof no longer directly needs
`lem-sf-qbar-localization-common-stage`
(`Sheaf.Paper.SfQbarLocalizationCommonStage`) or
`lem-sf-open-closed-weil-mate-structures`
(`Sheaf.SixFunctors.OpenClosedWeilMateStructures`). They were plan dependencies
without direct imports in the original item. The first is replaced by the
already normalized descent and rational triangle declarations. The second is
used indirectly through the existing normalized rational square theorem;
its declarations remain in the library and are not withdrawn.

The attempted proof import `Sheaf.Paper.ExtensionByZeroPunctual` was removed;
its broad punctual-weight node is not needed by this argument.
No original direct import was removed. No unit statement, unit step, source
library declaration, or module was withdrawn. The parent proof dependency list
now follows its actual assembly instead of retaining the unfinished qbar plan.

## Where the brief, the DAG or earlier work was wrong

The parent DAG described the qbar Weil clause as an unfinished original hole.
The rational argument already provided the categorical uniqueness/third-square
helper; only common-stage realization and normalization were needed to apply it.
The current blueprint's Weil-structures paragraph supplies precisely this route.
The unit route is unchanged, including the exact localization sequence and
exchange-unit/counit equations. The proof also covers zero objects, empty open
or closed complements, and Weil maps represented at a larger coefficient stage.

## New nodes

`lem-sf-normalized-common-stage-recollement-weil-squares`, in the parent's chapter
and unit, records the first two Frobenius squares only. It makes no assertion
about a connecting arrow, distinguished triangles, Hom vanishing, or uniqueness,
so is strictly a part of the parent's argument. It is proved from existing
finite-realization, rational-square and stage-naturality declarations.

The private rational presentation was factored through the same generic scalar
construction to avoid costly concrete module-instance comparisons. All existing
interfaces remain unchanged. Change record:
`coord/changes/R2-sf-private-rational-presentation.md`.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
