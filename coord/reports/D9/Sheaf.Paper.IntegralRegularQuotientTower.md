## What changed

Restore `Sheaf.Paper.IntegralRegularQuotientTower` from its quarantine archive and
prove `AlgebraicGeometry.ProEtale.integral_regular_quotient_tower` from existing
Mathlib cone APIs and the source-library principal reduction comparison. The
original theorem signature and all public imports are preserved. The ordinary
short exact quotient sequences are mapped by the additive equivalence, compared
with derived quotients, and assembled into one natural tower isomorphism. The
cone inclusion identity proves the augmentation equation.

The fully proved coefficient comparison is in the new module
`Sheaf.Algebra.Homology.RegularPrincipalQuotientTower`, imported privately by the
presentation comparison. It works over a commutative coefficient ring with a
non-zero-divisor and requires compatible short exact quotient sequences. The new
`Sheaf.Paper.RegularQuotientPresentationTower` contains the fully proved exact
transport through the additive equivalence, privately imported by the item.
Abstract private helpers separate exact transport over arbitrary abelian
categories from the scalar coefficient comparison, avoiding repeated comparison
of their expanded concrete instances.
The node proofs describe the actual Lean argument. No shared definition changes.

## Proved and sorry left

Close the one hole in
`AlgebraicGeometry.ProEtale.integral_regular_quotient_tower`
(`lem-sfb-integral-regular-quotient-tower`). The new theorem
`AlgebraicGeometry.ProEtale.regular_principal_quotient_tower`
(`lem-sfb-regular-principal-quotient-tower`) and
`AlgebraicGeometry.ProEtale.regular_quotient_presentation_tower`
(`lem-sfb-regular-quotient-presentation-tower`) are also fully proved.
Holes closed: 1. Holes added: 0. No `sorry` remains in any of the three delivered modules.
The new modules are proved extractions, not a decomposition into further holes.

Server `lcompile.py` accepts all three modules in import order and enforces the
60-second limit per file. The clean coefficient module takes 54 seconds. After
separating abstract exact transport from the coefficient comparison, the
presentation module has about 10 seconds of kernel checking and the integral
specialization also passes. The temporary profiler options were the only
warnings and are removed from the packet before delivery. All three node
signatures match their Lean statements; every proof dependency list equals the
union of the recorded step dependencies. The original public signature and
public imports match the shared source exactly.

## No longer needed

No original public import, mathematical dependency, or node is pruned. Removed
redundant direct proof imports from the new coefficient module:
`Mathlib.Algebra.Homology.HomotopyCategory.ShortExact` and
`Mathlib.CategoryTheory.Functor.OfSequence`; both are already publicly exposed
through the imported source-library `Complete.AdicTower`. All steps
of the existing node and the unit route are retained, now recorded through the
two proved extraction nodes. The original SES and derived-category dependencies
remain in their proofs. The coefficient comparison
uses the proved source-library reduction-cone, transition and augmentation APIs;
no extra K-flatness assumption on the input complex is needed. No source-library
declaration is removed or changed.

## Where the brief, the DAG or earlier work was wrong

At the start the item source was quarantined under
`quarantine/Sheaf/Paper/IntegralRegularQuotientTower.lean`; it has since also
been restored in the shared source. The original attachment and dependencies
are preserved. Its initial absence from `lean/` was not treated as a withdrawal.
The existing proof route suffices to close the obligation without another
decomposition.

The first complete proof checked without errors but exceeded 60 seconds because
of elaboration and kernel checking of concrete category expressions. Generalizing
private helpers and extracting the two fully proved comparison modules reduce
that cost per file. The original public statement is unchanged.

## New nodes

`lem-sfb-regular-principal-quotient-tower` realizes
`AlgebraicGeometry.ProEtale.regular_principal_quotient_tower` in
`lean/Sheaf/Algebra/Homology/RegularPrincipalQuotientTower.lean`. This is the
coefficient-level comparison, naturality and augmentation step, fully proved
from the existing cone and principal reduction APIs. It is strictly a part of
the assigned argument: exact transport through the additive equivalence and
identification with the specified ordinary quotient presentation are proved in
the presentation comparison module. Its edge cases include the zero complex,
zero coefficient ring and invertible scalar; exactness forces the corresponding
zero quotients, and the cone comparison still applies.

`lem-sfb-regular-quotient-presentation-tower` realizes
`AlgebraicGeometry.ProEtale.regular_quotient_presentation_tower` in
`lean/Sheaf/Paper/RegularQuotientPresentationTower.lean`. Its complete proof maps
the specified quotient sequences through the additive equivalence, invokes the
coefficient comparison and transports its augmentation identity. This proved
extraction keeps kernel checking of the presentation comparison separate from
its integral specialization. It has no new hole or additional assumption in the
integral theorem. Zero input and invertible scalar cases follow from the same
short exact sequence and cone argument.

No change record is needed because no existing statement, definition or public
interface is changed.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
