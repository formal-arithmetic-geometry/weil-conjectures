## What changed

Completed the earlier sandbox attempt without changing the existing theorem's signature or
public imports. The item proves weak regularity by cancellation on each prefix quotient.
It imports the new proof-only module
`Sheaf.RingTheory.PolynomialLocalIdealRelationFiniteStage`, whose public theorem
`RingTheory.Sequence.exists_finiteType_subring_local_ideal_relation` is also fully proved.
The item's private `regular_quotient_iff_ideal_cancel` identifies quotient regularity with
ideal cancellation. The new module's private `finite_polynomials_stage` constructs a finite
type subring by adjoining a finite union of polynomial coefficient sets.

The finite-stage proof represents a fraction as z/d, uses the localization ideal-membership
criterion to obtain t outside Q and a polynomial relation, expresses that relation as a
finite sum, and adjoins precisely the finitely many coefficients needed. Injectivity of the
polynomial coefficient map transfers this equality to the stage; the localization criterion
there establishes the lifted ideal membership. The original theorem then cancels at that
stage using hstage and maps ideal membership back. No arbitrary data definition depends on
an existence theorem, and no flatness or injectivity of the localization map is assumed.

Both modules compile cleanly together through lcompile.py. The empty-list case is handled
by an empty finite sum and an empty family of regularity conditions. The construction works
with zero variables and with rings having zero divisors. In the zero ring no prime ideal
instance exists, so it produces no extra exceptional case. Updated the item's DAG proof
and dependencies and added a node for the proved finite-stage theorem. The unit record
sk-thm-p1 and all its realized statements and steps stay unchanged.

## Proved and sorry left

Closed the item's one original hole:
`RingTheory.Sequence.isWeaklyRegular_polynomial_local_of_finiteType_subrings`
(node `lem-weil-pbc-polynomial-local-weak-regular-sequence-descent`).

Also proved the new theorem
`RingTheory.Sequence.exists_finiteType_subring_local_ideal_relation`
(node `lem-weil-pbc-polynomial-local-ideal-relation-finite-stage`), together with both private
helpers. There are no sorries in either delivered module, no holes added, and no outstanding
intermediate statement. Net change: one original hole closed, zero holes added.

## No longer needed

Pruned the DAG proof dependency
`lem-weil-pbc-filtered-colimit-abelian-groups-exact`:
Mathlib's `Mathlib.Algebra.Category.Grp.AB` and the categorical construction of filtered
colimits and quotient comparison maps are not needed by this proof. That Mathlib module
was not imported in the repository version; this is a DAG dependency removal, not a
removed Lean import, and it makes no claim about its other users.

No existing Lean import was removed. The four public Mathlib imports supply the unchanged
statement's types and classes. The only new item import is the finite-stage relation
module, written without public. All remaining original definition nodes continue to be
used in the statements or the direct proof. No other original statement/module is pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had a compiling cancellation argument but left its finite-stage relation
as sorry and supplied no node or report. This delivery completes that relation directly and
supplies both missing artifacts. The original mathematical statement is sound; there is no
statement correction or forced adaptation. The DAG's colimit argument can be implemented
more directly by witnessing one relation, cancelling at its finite stage, and mapping back.

Read Stacks Tag 00SV's general-ring paragraph and both displayed colimit identities at
https://stacks.math.columbia.edu/tag/00SV. The direct argument expands their finite-support
content. Searched Mathlib and both library roots for coefficient-stage and ideal-relation
results. LeanFinder found IsLocalization.mem_span_map and related localization results;
Loogle found Subalgebra.FG and the finite-adjoin API. The grep located smooth Noetherian
descent, whose proof uses the same finite-coefficient technique but whose statement does
not provide the required localized ideal relation. LeanSearch returned Internal Server
Error and is recorded as unavailable. No identical result was found. Blueprint searches
for 00SV, ideal membership, and coefficient subring returned no matching imported node.

## New nodes

`lem-weil-pbc-polynomial-local-ideal-relation-finite-stage` records the fully proved theorem
in `lean/Sheaf/RingTheory/PolynomialLocalIdealRelationFiniteStage.lean`. It concerns a single
localized ideal relation, without weak regularity or any universal stage regularity
hypothesis, and is strictly a part of the original argument. Its node gives the explicit
finite sum, the coefficient adjoin construction, localization compatibility, and descent
of the polynomial relation. Three actual search kinds are recorded in searches.jsonl.
No change record is needed because no existing interface or statement changed.

## Second reading by X2

1. I compared the delivered weak-regularity module with the repository version. The theorem
signature and all existing declarations are unchanged; only the proof, a proof-only import, and
DAG proof metadata differ. The finite-stage theorem is a genuinely smaller intermediate claim,
with a separate node and unchanged target statement.

2. Both delivered modules compile with `lcompile.py --all`. There are no `sorry`, `axiom`,
`unsafe`, `opaque`, `implemented_by`, or `extern` declarations. The quotient cancellation helper
was reduced to Mathlib's `isSMulRegular_quotient_iff_mem_of_smul_mem`; this also removes a
redundant bespoke induction. The proof uses only ordinary classical constructions and the
allowed library axioms.

3. I searched Mathlib and the Sheaf sources for finite-coefficient localization ideal descent,
weak-regular-sequence descent, and equivalent quotient-cancellation declarations. No existing
declaration states the finite-stage relation theorem or the target theorem. The new theorem is
strictly weaker than the target: it handles one ideal relation and supplies one finite stage.
Its empty-list and zero-variable cases are covered by the finite-sum and polynomial APIs.

4. The route keeps unit `sk-thm-p1`: the target is still proved through regularity on each
prefix quotient and the finite-stage relation step. The old filtered-colimit exactness
 dependency is not used by the elementwise proof and remains pruned in the node. Public imports
are retained for statement dependencies; the finite-stage module is imported privately because
only the proof uses it.

5. I checked that both DAG nodes' proof steps and `proof_deps` match the Lean proof, including
Mathlib quotient cancellation and the finite-stage relation node. The unit's `realized` record
is unchanged. I changed the private helper to the shorter Mathlib proof and corrected the DAG
step/dependency metadata to record the finite-type and quotient lemmas actually used.
