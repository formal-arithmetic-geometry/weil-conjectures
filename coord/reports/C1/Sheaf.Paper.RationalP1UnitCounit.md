## What changed

Proved `AlgebraicGeometry.ProEtale.RationalP1.counitInversion` in
`Sheaf.Paper.RationalP1UnitCounit`, with its statement unchanged. The proof applies
`localizingPreservation` to the coefficient unit to obtain the shifted Tate line in
Loc(Dbc), then applies the rational projection formula to that line and K.

Added two proved supporting modules. `RationalP1LineFromPreservation` constructs a
rank-one finite constant model for the coefficient unit and transports its preserved
image along the derived unit and tensor unitor comparisons. It requires only the
preservation hypothesis, so it does not depend on the item theorem.
`RationalP1LocalizingProjection` instantiates the existing two-variable localizing
extension argument with the actual selected coefficient, then transfers invertibility
from the native right projection through braidings to the fixed left projection.
These are proof-only imports in the item. No existing declaration signature,
definition, instance, public import, or attribute was changed.

Updated proof step 11, proof dependencies, and proof origin of the item's node.

Validation: `lcompile.py --all` compiled all three delivery modules without warnings or
errors and accepted each under its enforced single-file Lean runtime limit. Temporary
profiling options were removed before this final compile.

## Proved and sorry left

Closed one of the four holes present in the current item source:
`AlgebraicGeometry.ProEtale.RationalP1.counitInversion`.
Added zero holes. Both new public helper theorems and all their private helpers have
complete proof bodies. This is a proof from existing project declarations, some of
which remain sorry; it is not a claim that the target is axiom-free already.

Three holes remain unchanged, all at
`det-prop-p1-adjunction-rational-unit-counit`:

- `AlgebraicGeometry.ProEtale.RationalP1.localizingPreservation`.
- `AlgebraicGeometry.ProEtale.RationalP1.unitInversions`.
- `AlgebraicGeometry.ProEtale.RationalP1.unitCounit_exact`.

The already proved `unitCounit_existsUnique` was retained unchanged.

## No longer needed

None. No existing module, node, or import was withdrawn. The other three clauses still
need their original proof plans. In particular, deriving the shifted Tate line from
preservation for this counit clause does not remove the need to establish preservation.

## Where the brief, the DAG or earlier work was wrong

The shared source synchronized during the initial reading: the preceding C1 naturality
delivery had landed, leaving four holes rather than five. This delivery starts from
that synchronized source and retains its existing proof.

The published finite-extension localizing projection theorem quantifies a coefficient
field in the ambient universe, while the selected finite intermediate coefficient is
native to its own universe and uses `continuousMapRingObj`. Rather than changing that
interface or a shared definition, the new helper specializes the existing proved generic
two-variable extension argument directly to the selected coefficient. Its bounded input
is the existing rational proper projection theorem.

## New nodes

`lem-sfb-rational-p1-line-from-preservation`, in
`Sheaf.Paper.RationalP1LineFromPreservation`, is a proved consequence of preservation
applied to the rank-one coefficient unit. The argument includes empty schemes and the
zero line and imposes no finite-presentation hypothesis on an arbitrary input L.

`lem-sfb-rational-p1-localizing-projection`, in
`Sheaf.Paper.RationalP1LocalizingProjection`, proves invertibility of the fixed left
projection for rational localizing objects by the existing generator-extension theorem
and normalization. It keeps both finite intermediate and closure coefficients.

No change record is needed: only the item's proof and node, and new proved helper
modules and their nodes, were changed.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
