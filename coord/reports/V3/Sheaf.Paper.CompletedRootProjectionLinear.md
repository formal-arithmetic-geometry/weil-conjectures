## What changed

Proved `AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedRootProjection_linear`
in `Sheaf.Paper.CompletedRootProjectionLinear`, retaining its statement and public import.
All other existing modules and node files are untouched. Added private proof imports of
CondensedZlReduction, ProEtaleFiniteReductionPullback,
IntegralModelsEmbeddedCompletionDiagram and ConstantZModScalarTensor,
using their already proved normalization, constant-presentation and additive-to-linear helpers.
All four are already in the original public import dependency closure; these proof
imports introduce no additional holed modules into that closure.
The auxiliary section-ring comparison is constructed locally using the ordinary ring-object
and constant-sheaf APIs; it changes no ring or module data.

The proof first shows that the finite coefficient ring is annihilated by its defining
power. The cokernel universal property of normalized reduction factors the actual
coefficient map through the constant cyclic ring. Cancellation after tensoring proves
that the factor preserves multiplication. The existing cyclic scalar lift makes the
free-module unit linear over this finite ring. The normalization he and coordinate
formula for the completed root action then give the required linear section maps.
Naturality supplies the module morphism, with the specified underlying map by definition.
Every helper introduced here is private and proved.

The existing node's proof, proof_deps and proof_origin now record this route.
Validation: lcompile.py compiled the full proof without errors or warnings in
39.5 seconds. Final cleanup and delivery checks follow.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedRootProjection_linear`
(node `lem-diagonal-completed-root-projection-linear`).
No holes added, no split-off statements, and zero sorry left in the delivered module.

## No longer needed

No original Lean import is removed; DiagonalCoefficientMaps is needed by the signature.
The former proof dependency `def-sfb-diagonal-coefficient-diagrams` is not used: no
Family, diagram or integral root-limit comparison is needed. The actual coefficient-map
definitions are used directly via `def-sfb-diagonal-coefficient-maps`. The original
statement dependency remains unchanged.

The planned proof dependency lem-diagonal-completed-coefficient-ring-comparison is also
unnecessary: its existence/uniqueness assertion is not invoked, since e and he are
parameters. Its statement dependency is retained. No private proof import of that
module is needed.

The planned bottom-field quotient isomorphism is unnecessary for this argument.
Only a ring map from the cyclic residue sheaf to the finite coefficient ring is needed;
the normalized cokernel comparison constructs it for every finite coefficient field.
The proof does not use BottomFiniteRootUnitIsIso, local freeness, a primitive-root cover,
or an inverse-limit comparison for the integral line. No module is withdrawn and no
claim of global unreachability is made for these other obligations.

## Where the brief, the DAG or earlier work was wrong

The original proof plan requested identification of the bottom coefficient quotient
with ZMod. That is stronger than what finite-projection linearity needs. Factoring the
coefficient map through normalized reduction suffices and avoids that arithmetic step.
The existing proved normalized cokernel and cyclic linearity APIs supply the reduction;
there is no further decomposition.

Existing nodes from other units are used only for generic coefficient tools: the normalized quotient
comparison `lem-pur-condensed-zl-reduction-mod-ell-power` supplies its proved cokernel
helper, and `lem-sp-constant-zmod-scalar-tensor` supplies its proved additive-to-linear
helper. The current unit has no generic replacements for these scalar-descent facts.
The proof also uses the proved generic constantPresentation, constantPresentation_mon,
constantPresentation_unit and constantSheafRingMonObj helpers of
IntegralModelsEmbeddedCompletionDiagram; its embedded integral-model theorem is not
applied. The proved constantRingAb_unit helper from ProEtaleFiniteReductionPullback fixes
the normalization on the constant-sheaf unit. These helpers identify the existing
constant sheaf representation and its unit.
This preserves the diagonal-tower unit route. No maintainer tool approvals are edited.

The proof includes n=0 and the empty scheme. It uses no nonempty-site or root-generator
assumption. Its intermediate annihilation and factorization calculation works for any
finite intermediate E. No existing statement, definition, shared interface or source-library
module is changed. The proof-context record is
`coord/changes/V3-completed-root-projection-proof-context.md`; no consumer adaptation
is required.

The shared build did not expose the recently written private ringSections and
constantRingIso helpers visible in CompletedCoefficientRingComparison. The delivery
uses a local section-ring construction with the older compiled constant-presentation API.
No public declaration is duplicated or waiting for replacement by a new build.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
