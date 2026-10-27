## What changed

Filled `WeilConjectures.integralMappingLimitProjections` by assembling the actual
adjunction and calculus maps. Added private categorical helpers for naturality of
the enriched adjunct, its composite with the unit, and tensoring adjuncts through
the counit-defined lax tensor map. The finite H-zero formula is proved for arbitrary
ambient derived inputs, which also proves the shifted-Hom clause.

Added the separate target-shift comparison
`Sheaf.Paper.CoefficientEnrichedGlobalShift`: it concerns only the target-shift
square of the enriched global
reconstruction comparison, for arbitrary ambient integral inputs. The actual
unit appears explicitly in its formula, so the main shift clause applies it
directly using the three unchanged map definitions. Those three definitions move
verbatim to the new module,
publicly imported from the item; all names, signatures and formulas are unchanged.
See `coord/changes/integral-mapping-shift-interface.md`.

The isomorphism clause uses the already stated intrinsic/legacy completeness
comparison and actual reconstruction theorem. Invertibility of l on X is obtained
from its actual finite-field structure map on global sections. The unit and gamma
are the existing maps throughout; no lift is selected from its finite projections.

## Proved and sorry left

Closed the original hole of `WeilConjectures.integralMappingLimitProjections`,
node `lem-coef-integral-mapping-limit-projections`, by decomposition. Its eight
clauses now have explicit proofs: unit/gamma isomorphism, naturality, actual scalar
projection, H-zero reduction, evaluated triangle, all-integer shifted Hom,
the separate target-shift square, and the internal enriched composition square.

Added one hole: `WeilConjectures.coefficientEnrichedGlobalShift`, node
`lem-coef-enriched-global-shift`. This is strictly the target-shift bookkeeping
step for arbitrary ambient inputs; it asserts none of the original
isomorphism, projection, Hom, triangle or composition conclusions. Its docstring
and node give the representative calculation and descent argument. There are no
other holes in the delivered modules and no holes in definitions. Thus this is
one original hole closed and one separate hole added, a decomposition with net
zero holes closed, not a fully proved result. Both delivery modules compile
without errors or warnings; the new lemma is the only retained `sorry`.

## No longer needed

No existing public imports removed and no modules withdrawn. Added one public
import to preserve the API of the three extracted definitions. The proof does not
use `def-weil-derived-complete`, `def-weil-integral-derived-reduction`,
`def-pur-derived-internal-hom`, or `lem-pur-rhom-global-sections` as direct proof
steps: it uses the concrete calculus, the fixed H-zero equivalence and the
intrinsic/legacy completeness comparison instead. Their definitions and
normalizations remain needed transitively and through the unchanged statements;
no withdrawal of these nodes is proposed.

## Where the brief, the DAG or earlier work was wrong

The original step 4 calls mapping-complex shift compatibility elementary, but
the calculus does not provide an explicit shift clause. The H-zero formula for
shifted morphisms alone does not prove equality of maps into a derived inverse
limit. The retained separate lemma uses actual Hom-complex and simultaneous-limit
normalizations, without assuming joint faithfulness of finite derived projections.

The constructible predicate and `IntegralOnSlice.IsComplete` use different
presentations of completeness; the existing legacy comparison is required to
apply the reconstruction theorem. Its auxiliary finite-field datum must live in
universe zero, independently of the given geometric base field.

## New nodes

`lem-coef-enriched-global-shift` in
`dag/nodes/sec-six-functors/lem-coef-enriched-global-shift.json` owns
`WeilConjectures.coefficientEnrichedGlobalShift`. It extracts the genuine target
shift calculation from step 4, on arbitrary ambient P and Q. Zero inputs,
r=0, negative shifts and incomplete Q give the same representative square;
there is no claim that the comparison is invertible for incomplete Q.
The interface-move change record is
`coord/changes/integral-mapping-shift-interface.md`; it records verbatim old/new
definitions, consumers and the absence of forced adaptations.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
