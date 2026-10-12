## What changed

Proved `Algebra.exists_popescu_height_zero_auxiliary_witnesses` without changing its
signature or its existing docstring. The empty-set case uses C directly. For a nonempty
set, the proof obtains an A-presentation of C from Mathlib, constructs the actual
polynomial quotient, descends its evaluation map, proves finite presentation and
factorization, and calculates the two witness images.

Added `Sheaf.RingTheory.PopescuAuxiliaryQuotientSmooth`, with five explicit construction
abbreviations/definitions and the proved theorem
`Algebra.popescuAuxQuot_smooth_localizations`. Its private helpers reindex the quotient
to the existing auxiliary localization theorem, transport the presentation quotient to
C, apply smooth base change and composition, and identify iterated localizations.
The extra singleton universe lift ensures B has exactly the required carrier universe.
No algebra data is chosen from an unproved existence theorem.

Both modules compile together through lcompile.py without warnings. Checked the
nonempty hypothesis before using the existing localization theorem's r >= 1 premise;
empty variable and relation lists, zero localization elements, zero rings, and exponent
zero require no extra assumptions. The existing target signature and visibility are
unchanged. No other existing module was adapted.

## Proved and sorry left

Closed the sole original hole:
`Algebra.exists_popescu_height_zero_auxiliary_witnesses`
(node `lem-weil-pbc-popescu-height-zero-auxiliary-witnesses`).

Also proved the new theorem `Algebra.popescuAuxQuot_smooth_localizations`
(node `lem-weil-pbc-popescu-auxiliary-quotient-smooth`) and all private helpers.
There are no sorries in either delivered module. Holes closed: 1; holes added: 0.
This is a proof from existing stated dependencies, not a decomposition into new holes.
The existing auxiliary localization declarations remain dependencies; this delivery
does not claim to close their underlying holes or the whole target import closure.

## No longer needed

Removed the item's direct proof imports of
`Sheaf.RingTheory.PopescuAuxiliaryAlgebraLocalizations` and
`Sheaf.RingTheory.SingularIdeal`. The former is used through the new smoothness module;
the latter is already visible through the unchanged public import of PopescuResolution.
Neither module is pruned from the targets' import closure.

The item's old direct geometric proof dependencies (auxiliary localizations, polynomial
smoothness, principal localization smoothness, tensor-localization, smooth base change
and composition, and iterated localization) now belong to the proved smoothness node.
They remain needed, and are recorded there rather than falsely reported as pruned.

The old node `lem-weil-pbc-finite-type-noetherian-finite-presentation` is not used by
this proof: finite presentation over A comes from the existing node
`lem-weil-pbc-finite-presentation-over-finite-type-algebra`, and finite presentation of
B from `lem-weil-pbc-finite-presentation-quotient-fg-ideal`. No existing Sheaf module is
claimed to leave the target closure.

The new module's imports were reduced after compilation: Smooth.Basic supplies the
statement vocabulary, while its proof uses the auxiliary localizations and
Localization.BaseChange. No unused standalone import of MvPolynomial.Equiv, Eval,
Ideal.Quotient.Operations, or Localization.Away.Basic remains in the new module.

## Where the brief, the DAG or earlier work was wrong

No statement correction was necessary. The original plan's first Noetherian argument
can be shortened to Mathlib's finite-presentation restriction-of-scalars theorem.
The empty-set case can use C, so no separate empty-index localization calculation is
needed. The existing corrected distinction between smoothness over C and over R in
Stacks 07FA is essential and is preserved: we invert z times the lift of c.

The local checkout has no literature/stacks-project/smoothing.tex; read the cited
source at https://stacks.math.columbia.edu/tag/07FA. LeanSearch returned an internal
server error, recorded as unavailable; LeanFinder and source grep were also run.
The blueprint search found no matching auxiliary-quotient node. The ancestry tool
returned None for the existing item's module-valued created.item; the new node instead
inherits that item's explicit blueprint ancestor and extends its via list.

## New nodes

`lem-weil-pbc-popescu-auxiliary-quotient-smooth`, in
`dag/nodes/sec-proper-base-change/`, records the explicit quotient and its proved
smoothness localizations. It is strictly the geometric part of the argument: it has
no Lambda, annihilators, exponents, factorization into Lambda, or witness-image
conclusions. It includes its complete proof, source, searches, and Lean record.
No change record is needed: all existing interfaces and public imports stay identical.

## Second reading by G2

1. Compared the delivered item module against the repository version. The existing theorem
   signature, visibility, and docstring are byte-for-byte unchanged; only proof imports and
   proof text differ. The added smoothness module and node are new declarations.

2. Compiled both delivered modules with `lcompile.py --all`; compilation completed without
   errors or warnings. There are no `sorry`s, forbidden declarations, or hollow definitions.
   The construction is explicit and does not choose data from a mere existence theorem.

3. Read the new theorem and its node. The quotient, smooth-localization conclusion, universe
   lift, hypotheses, source, proof dependencies, and Lean declaration agree. The theorem is
   strictly the geometric intermediate needed by the witness proof; no duplicate declaration
   was found in the repository.

4. Checked the proof route from the target downward. The empty finite-set case is handled
   directly, while the nonempty case uses the explicit quotient and the existing auxiliary
   localization equivalences. Imports removed from the target are recorded above; the
   geometric dependencies remain used through the new module. The unit route is preserved.

5. Checked the DAG records and report against the Lean declarations. The existing node's proof
   dependencies are updated only by the new intermediate node's use, and the new node has a
   complete source, proof, search, blueprint, chapter, unit, and Lean record. No statement or
   definition change record is required.

Changed after review: no proof repair was needed; this section is the complete second-reading
record.
