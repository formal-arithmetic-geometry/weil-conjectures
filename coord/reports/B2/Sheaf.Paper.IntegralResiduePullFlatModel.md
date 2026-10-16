## What changed

Proved `residueExchangePull_flatModel` with its exact original signature. The proof
uses flat preservation to compute the reduction counit, factors the derived units,
transports the exact restriction/pullback square through localization, and combines
these equations through the adjunction hom equivalence and the inverse-mate unit
identity.

Also proved the needed ordinary homotopy-category unit compatibility in
`Sheaf.Paper.IntegralResiduePullOrdinaryUnit`. Its proof identifies the explicit
restriction/pullback comparison on underlying sheaves, proves its geometric unit
identity, applies iterated inverse mates, and passes the scalar identity degreewise
to homotopy categories. No flatness hypothesis is needed for this ordinary statement.

Scope commands and the new ordinary statement are documented in
`coord/changes/B2-integral-residue-flat-model-proof-scopes.md`.
Canonical module-category structures are cached privately and installed only in
proof scopes; the target signature uses the original canonical instances.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.ProEtale.CondensedRing.residueExchangePull_flatModel` (1 of 1).

New supporting theorem also completely proved:
`AlgebraicGeometry.ProEtale.CondensedRing.residueExchangePull_ordinary_unit`.

Holes added: zero. Holes left in the delivery: zero. Every private helper is proved;
all private structure caches use existing canonical constructions. No existing
public definition or theorem signature changed. This is a proof, not a decomposition.

Validation: both modules compile cleanly. The fresh canonical-signature and axiom
audit passes as described in the second reading. The required
`deliver3.py B2 Sheaf.Paper.IntegralResiduePullFlatModel --no-push` prints OK:
commit `8a5fca34be` compiles and passes preflight. The subsequent report-only update
records that result; the final delivery repeats the required checks.

## No longer needed

No original dependency or module is withdrawn. In the new ordinary-unit module,
replaced the public import `Sheaf.Paper.IntegralResiduePullSquareData` by
`Sheaf.Paper.ContinuousIntegralCoefficients`: its statement and proof need only
the coefficient definitions and ordinary change-of-coefficients API. No module
leaves the target import closure. The direct balanced-tensor
calculation suggested by the original node is replaced by adjunction uniqueness,
underlying-sheaf comparison and iterated mates. It had no separate dependency node
to prune. All proof-only imports in the delivery are used.

## Where the brief, the DAG or earlier work was wrong

The node omitted the existing flat-pullback dependency; it is now recorded explicitly.
The second comparison equation does not need the flatness hypotheses: flatness is
used only for the first clause. The shared source snapshot initially lacked the
new item and node; the current copies were read from the project meeting point.
The published compiled dependencies became available during the session. The returned
import-prune error identified a duplicate of the private `moduleUnit_forget` theorem
from `ProfinitePointPullback`. Adding an unused `True` parameter did not genuinely
generalize it. This second reading deletes that helper entirely, changes the
proof-only import to `import all Sheaf.Paper.ProfinitePointPullback`, and uses the
existing theorem at both call sites. No upstream module is edited.

## New nodes

`new-integral-residue-pull-ordinary-unit`:
`Sheaf.Paper.IntegralResiduePullOrdinaryUnit`, declaration
`AlgebraicGeometry.ProEtale.CondensedRing.residueExchangePull_ordinary_unit`.
This supporting theorem is proved. Its node records the underlying-sheaf comparison,
iterated-mate argument and degreewise homotopy passage.

## Earlier second reading (a previous round; superseded)

The earlier review is superseded by the independent checks below. In particular,
its claim that an unused `True` argument generalized a duplicate theorem was wrong;
the duplicate has now been removed and the existing library theorem reused.

## Second reading by B2

1. **Interfaces: pass.** Compared both complete delivered sources with the shared
   repository. The ordinary-unit module is new. The existing flat-model theorem's
   signature is byte-for-byte identical, including both hypotheses and both
   conjuncts. Its canonical-instance signature remains outside the private cache
   section. No existing public definition, selected data, or other module changed.
   The scope commands and new public theorem are recorded in
   `coord/changes/B2-integral-residue-flat-model-proof-scopes.md`.

2. **Proof and trust: pass.** Read the complete ordinary and
   derived proofs: the first conjunct uses flat preservation and the K-flat
   colimit criterion; the equality uses the derived unit factors, exact-square
   localization factors, ordinary unit equation, and injectivity of the adjunction
   hom equivalence after cancellation of an invertible localization factor.
   Scanned both sources: no proof holes, forbidden declarations, or hollow data.
   Private caches are canonical constructions or proofs of existing instances.
   Both modules compile cleanly (ordinary unit: 28.3 s; flat model: 38.3 s).
   The fresh scratch audit applies the delivered theorem to the repository's exact
   original signature under canonical instances and compiles. `#print axioms`
   gives only `propext`, `Classical.choice`, `Quot.sound` for the ordinary theorem,
   square maps, scalar adjunction and both counits. The flat-model theorem also
   reaches `sorryAx` through the pre-existing `inverseImageModule_preservesFlat`,
   confirmed by checking that declaration and `integralResidue_pullback_preservesFlat`.
   This delivery adds no axiom or hole; it closes the local obligation conditional
   on that existing open dependency.

3. **Supporting statement: pass after duplicate repair.** No unproved statements
   are split off. The new theorem is only ordinary unit compatibility, with arbitrary
   homotopy input and no flatness assertion, and is strictly part of the derived
   argument. Its docstring gives the module-level mate argument and passage through
   the homotopy quotient. Zero complexes make both sides zero; identity coefficient
   or geometric maps give the adjunction-unit identity. Fresh LeanFinder, Loogle,
   Mathlib grep, and local source searches found the generic mate lemmas already
   used and the existing private `moduleUnit_forget`. Deleted its local duplicate
   (the unused `True` parameter was no generalization), reused the original through
   `import all`, and retained the actual scalar-square/mate proof.

4. **Route and pruning: pass.** Read the original node plan, its dependency
   declarations, square-data constructions, and the proper-base-change unit's
   `realized` statement and three steps. These calculations are below that unit;
   no unit step is replaced or bypassed. The original square-data proof dependency
   remains used; none is withdrawn. Each main-module proof import is used.
   Narrowed the new module's public import from derived square data to
   `ContinuousIntegralCoefficients`; `ProfinitePointPullback` stays proof-only.
   No module is pruned from the targets' import closure.

5. **DAG agreement: pass after repair.** The existing node describes the flat
   counit calculation and the derived-unit/localization/mate assembly and lists
   their square-data, flat-preservation, and ordinary-unit dependencies. The new
   node has its exact Lean statement, own module, source, complete proof, searches,
   origin, creation data, chapter/unit and blueprint link. Its dependencies match
   the coefficient API and underlying-sheaf comparison used. Updated its proof and
   search record to state that the existing `moduleUnit_forget` is reused.

Second reading changed the duplicate-helper reuse, the new module's public import,
the matching node proof/search metadata, and the report/change-record documentation.
Original holes closed: 1; holes added: 0; holes left in delivered modules: 0.
No decomposition. The local compile and canonical-signature/axiom audit pass.
The required delivery dry run prints OK (commit `8a5fca34be`), with no preflight errors.
