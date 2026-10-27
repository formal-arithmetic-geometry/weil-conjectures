## What changed

Proved `AlgebraicGeometry.ProEtale.RationalP1.diagonalTensorMap_isIso` in the
item module, retaining the existing canonical morphism and all public signatures,
definition bodies, attributes, and public imports. Added three private proof imports:
`Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula`,
`Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization`, and
`Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalCartier`.

The private argument first proves that the complement of an invertible ideal is
an affine immersion: locally it is a principal open in an affine scheme. Applied
to the existing Cartier diagonal, this supplies the required quasi-compact open
complement over every base scheme.

The existing localization theorem makes closed direct image fully faithful after
transport to the published derived functors. The existing support projection
formula puts its tensor with any ambient complex in its essential image. Thus
the actual derived adjunction unit on that tensor is invertible. The canonical
projection mate is then a composite of that unit, the normalized invertible
pullback tensor comparison, and the invertible closed counit. Its two braidings,
section comparison, coefficient-unit comparison and right unitor are invertible,
which proves the original diagonal tensor statement.

Only the item Lean module and its own diagonal-comparison node are changed.
The node now records this proof and its actual dependencies. The existing
naturality proof is retained. No new nodes, public declarations, definition data,
or change records are needed.

## Proved and sorry left

Original holes: 1. Closed: 1. Added: 0. Split off: 0. Remaining: 0.

Closed: `AlgebraicGeometry.ProEtale.RationalP1.diagonalTensorMap_isIso`, node
`def-sfb-internal-diagonal-tensor-comparison`.

All four added private helpers are proved. No `sorry` remains in the delivered
module and none is added elsewhere. The proof uses existing declared support
lemmas; it does not claim that their complete transitive dependency closure has
already been proved.

## No longer needed

None. No existing import, node, module or declaration is withdrawn. The unit's
closed/open support argument for the diagonal comparison is preserved. Its
previous node had no proof dependencies to prune.

## Where the brief, the DAG or earlier work was wrong

The diagonal node recorded its definition and the source argument but had an
empty proof plan and no proof dependencies, despite its named invertibility
obligation. Its proof fields now name the existing support projection and
localization declarations actually used.

`lem-amb-p1-diagonal-cartier` supplies the existing geometric diagonal result.
`lem-sfb-condensed-support-projection-formula` and
`lem-sfb-condensed-support-derived-localization` are reused as tools from the
internal-Hom development. They state precisely the closed/open support results
needed here, without boundedness, constructibility, or a global qcqs assumption.
The unit route is unchanged. The proof does not require a new canonical-map
comparison theorem: existence of the supported tensor isomorphism establishes
essential-image membership, after which the published adjunction unit/counit
formula proves invertibility of the published canonical mate itself.

Empty schemes, the zero coefficient ring, zero modules and unbounded complexes
are allowed throughout. The complement is affine locally even when the base is
not quasi-compact. No arbitrary isomorphism is used to define any public data.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
