## What changed

Kept the signature of `AlgebraicGeometry.Scheme.sfbAdicImmersion_liftingInput` and
its slice-category abbreviation verbatim. Its proof now assembles a concrete
etale residue model, its bounded and finite-lisse cohomology, its field tensor
bounds, and completed restriction comparisons.

`AdicImmersionResidueTransport` constructs the residue by the actual AsSmall
precomposition equivalence, the inverse of the normalized constant-scalar
restriction equivalence, termwise etale inverse image, and standard localization.
No witness of an arbitrary existence statement defines its data. Exactness gives
a proved homology-bound theorem.

`ConstantFieldResidueTensorBounds` proves the tensor clause for every complex
representing the bounded derived object, even without K-flatness. It uses the
existing proved `isFlat_constantFieldModule`, the site/monoidal tensor comparison,
and the total-with-single-complex comparison. Thus the field-tensor argument is
completed here rather than moved into a new hole.

`AdicImmersionResidueLisse` proves finite-lisse transport for every commutative
coefficient ring: discard empty cover members, identify the remaining constant
values with geometric stalks, and use finite generation of those stalks. It then
uses the existing AsSmall, constant-ring, and commutative/ring model comparisons.
Its second theorem transports this property through exact homology. Proof-only
`import all` imports expose existing private comparison lemmas; no adopted source
file was edited.

`AdicImmersionCompletedTransport` isolates completion, the normalized residue
projection, and slice comparisons for the fixed residue model. It contains no
bounds, local constancy, maximality, or completeness assumption on the coefficient
ring. This is steps 1, 4 and 5 of the original plan, a proper part of the argument.
The original module imports all four additions privately. No existing definition
or statement changed, and no consumer adaptations or change record are needed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.sfbAdicImmersion_liftingInput` by a complete Lean
assembly. This is a decomposition, not a net hole reduction.

Proved `sfbImmersionResidue_bounded`, `constantFieldResidueTensor_bounds`,
`sfbEtaleResidueModel_finiteLisse`, and `sfbImmersionResidue_lisse`, together with
the exactness instances of the explicit residue functor.

Added one hole, and no others:
`AlgebraicGeometry.Scheme.sfbAdicImmersion_completedTransport`, node
`lem-sfb-adic-immersion-completed-transport`, in its own new module. It retains the
completion-unit normalization and compatibility of the same transported M with
both kinds of slice comparisons. It is not an arbitrary M characterized only by
its residue: residue equivalence alone would not imply those slice comparisons.

The item started with one hole and ends with zero; the packet has one new hole.
The original signature was checked textually against the shared source. All new
imports were checked for cycles. Full sandbox compilation validated all five modules, including both lisse
transport proofs, in at most 19 seconds per file. Final compilation and axiom
checks are recorded by deliver3.py.

## No longer needed

No existing public import was removed, and no module is withdrawn. No global
pruning is claimed. The original direct dependency on
`lem-sfb-etale-field-tensor-bounds` / `Sheaf.Paper.AdicResidueFieldTensor` is no
longer needed for this route: constant field module flatness directly proves the
stronger assertion for all representatives in the actual ringed category.

The original completion, comparison-pullback, localized-module exactness, and
site/scalar equivalence dependencies remain needed by the completed-transport
subargument or the proved explicit residue construction. They were not pruned
merely because they are absent from the short final assembly. The original
node's proof dependencies now name the four concrete subarguments instead.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The existing finite-locally-constant module-values
*public* equivalence assumes a finite coefficient ring and cannot be applied to
an arbitrary residue field. Its private stalk comparison does not have that
assumption. The proof here uses that comparison and finite generation of stalks
instead of assuming that the residue field is finite.

The existing constant-field flatness theorem gives a shorter tensor route than
the original plan's transfer from etale tensor bounds. K-flatness is unnecessary
for tensor with a degree-zero sheaf over a constant field, although the original
signature is preserved.

Searches used leanfinder, loogle and Mathlib grep, with the queries and results
recorded on the new nodes. Project search found the constant-field flatness and
private site/scalar local-model comparison proofs used here. Blueprint searches
for constant field tensor, immersion complete and locally constant module did
not locate another statement of these exact normalization interfaces. The unit
`sk-lem-integral-models` and every realized unit step remain intact.

## New nodes

`lem-sfb-adic-immersion-residue-transport` records the explicit exact coefficient
model and its proved homology bounds.

`lem-sfb-constant-field-residue-tensor-bounds` records the proved tensor interval
for every representative over a constant field sheaf. It uses the existing
constant-field flatness theorem from another unit as a tool; no node of this
unit provided its direct ringed-site flatness statement.

`lem-sfb-adic-immersion-residue-lisse` records finite-lisse model transport and
its proved cohomological consequence. It reuses private proved generic helpers
from the existing finite-values and local-model modules.

`lem-sfb-adic-immersion-completed-transport` is the one remaining theorem: it
keeps the normalized completed coefficient, residue and slice comparisons for
the fixed explicit residue. Its source and full natural-language proof are in
both its module and node. No change record is required.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
