## What changed

Replaced the remaining sorry in AlgebraicGeometry.Etale.etaleCompactScalarCoherence
by a proper/open projection calculation. The new private
compactScalarProjection_factorization cancels the intermediate signed symmetry
against its inverse. The new private orderedDirectProjection_naturality uses the
naturality field of the concrete orderedDirectProjectionNat. The projection
clause pastes the constituent scalar squares using scalarMate naturality and
projection naturality. The invertibility and compactification-comparison clauses
apply existing proved helpers, retaining both bounded-below hypotheses.

Added proof imports Sheaf.Paper.EtaleDirectScalarProjection and
Sheaf.Paper.EtaleOpenScalarProjection. The former constructs
orderedDirectProjectionNat from the source symmetry, the flipped counit
projection and the image of the target symmetry. Its component is
orderedDirectProjection, with the proved orderedDirectProjection_eq equation.
The latter constructs compactOpenProjection from the open projection and
pullback compositor. Each module has one remaining scalar-square theorem,
listed below. The maps have explicit source and target types and are irreducible.
Their concrete formulas are exposed only where the factorization needs them.

All existing public
signatures, constructions and public imports are unchanged. The parent node now
records the actual factorization and naturality proof.

## Proved and sorry left

Original holes: 1. Original hole replaced: AlgebraicGeometry.Etale.etaleCompactScalarCoherence
(node lem-pur-etale-compact-scalar-coherence). Remaining holes in the item: 0.
This is a decomposition, not a complete proof of the original hole: two strictly
smaller constituent squares remain, rather than the whole compact-support square.

Added holes: 2, each exactly the whole proof of its named public theorem:

- AlgebraicGeometry.Etale.etaleDirectScalarProjection,
  node lem-pur-etale-direct-scalar-projection, in
  Sheaf.Paper.EtaleDirectScalarProjection.
- AlgebraicGeometry.Etale.etaleOpenScalarProjection,
  node lem-pur-etale-open-scalar-projection, in
  Sheaf.Paper.EtaleOpenScalarProjection.

The new projection definitions contain no holes and choose no witnesses. The new
private helpers and the combining proof contain no sorry. Existing dependencies
may retain their previously recorded holes. Net textual hole change: +1.

## No longer needed

No Lean imports or modules were removed and no module is withdrawn. No global
pruning is claimed. The parent no longer directly cites
lem-amb-proper-coproducts-projection, lem-coef-etale-open-scalar-coherence,
lem-pur-etale-open-derived-tensor or
lem-weil-pbc-ringed-exchange-tensor-coherence in proof_deps. The direct-image
projection map is now sourced from
def-kun-projection-formula-map; the other three results are needed by the
constituent nodes. The parent's statement still cites the existing proper
projection interface. None of these modules is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. Earlier work had already proved all other public
theorems, as well as the main theorem's isomorphism and compactification-comparison
helpers. Only its projection clause needed a new reduction. The new lemmas have
no coefficient finiteness, flatness or boundedness assumptions: their equalities
follow from the normalized mates and tensors before invoking any proper
projection isomorphism. At the identity coefficient map they reduce to the
ordinary normalized projection; for a zero input, zero ring or empty open every
composite is the unique zero map. Nonflat scalar extension does not alter the
argument, since it uses flat K-flat representatives rather than underived tensor.
The unit route is retained.

## New nodes

lem-pur-etale-direct-scalar-projection is the proper/direct-image constituent of
parent proof step 2, for arbitrary morphisms and derived inputs. Its source is the
counit calculation in Stacks 07A4 and the coefficient square in 0GL6. Its actual
ordered projection is a concrete conjugate of the existing counit projection.

lem-pur-etale-open-scalar-projection is the open constituent of parent proof
step 2, including the pullback compositor of the compactification. Its source is
the mixed open scalar/tensor square and Stacks 0GL6/07A4. Its projection factor is
constructed from the existing open tensor map and canonical geometric compositor.
It contains no proper direct image and no compactification-independence claim.

Searches for both nodes used Lean Finder, Loogle, Mathlib grep, the project
sources and blueprint_refs.py. The field-system proper/open squares and the
pro-etale ringed projection pasting result have different coefficient categories
and do not supply these constant-module equalities by a one-line specialization.
No change record is required: only new declarations and proof bodies/imports of
the item were added; no existing interface or definition changed.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
