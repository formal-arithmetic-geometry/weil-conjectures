## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/det-uniform-constructible-ext-rational.json` (the item; no new nodes; split status).
- `citations.json` (verbatim statement quotes for every cited node in every proof step).
- `searches.jsonl` (the Mathlib searches used by the interrupted repair).

Attachments: none.  WANTED: none.

The imported rational-coefficient statement was corrected in the existing item before this
repair.  A source-stratified lisse rational sheaf need not have a global lattice, so the
integral cutoff for a refined stratum is `c_{a_k}` and the uniform source cutoff is
`d_{a,L}=max({0} union {c_{a_k}})`.  The original `c_a` assertion is retained only when the
chosen finite model has a lattice on all of `S`.  This is the pinched-node obstruction recorded
in the item's `source_error`; it is a correction of the imported blueprint route, not a weakened
target statement.

The earlier return identified the old scalar-localization and finite-model descent paragraphs
as non-elementary steps longer than 2000 characters.  I replaced those paragraphs by short
steps: scalar adjunction, the coefficient telescope and tensor-colimit identification, integral
continuity and vanishing, the two filtration inductions, finite-field Hom descent, restriction
through the closed/open lower-shriek factors, finite-free restricted local models, and termwise
vanishing.  Each of these steps cites the existing node that states the fact it uses; no hidden
comparison was copied from a proof of a cited node.

## Review by Q131

I read the item's statement and proof source in
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-uniform-constructible-ext/`,
the unit section, and the existing torsion, integral, dévissage, lattice, continuity, scalar
change, lower-shriek comparison, filtration, exact-Ext, and finite-coefficient nodes.  I also
checked the read-only slopmaster2 source for the item tag and found no declaration to attach.

Step 1 uses the finite-type-over-Noetherian, open/closed exact-sequence, and constructibility
statements.  I checked that the standing finite-type schemes are Noetherian, that the locally
closed factor has the required quasi-compact open and closed pieces, and that its restrictions
are the lisse sheaf and zero on the three pieces.  Step 2 uses the stratified-lattice,
common-refinement, and filtration statements; I checked that the source refinement is fixed
before the target and that every graded piece has a lisse integral lattice.

Steps 3–5 use the coefficient-localization, scalar-six-pullback, coefficient-change adjunction,
filtered-colimit tensor, constructible-continuity, and integral-bound statements.  Their
hypotheses match the finite locally free source lattice and the common lower degree bound of the
multiplication-by-ell telescope.  Step 6 uses the covariant and contravariant six-term Ext
sequences and the Ext definition; the zero bases and both finite inductions give the maximum of
the stratum cutoffs.

Steps 7–10 use the two-colimit theorem, scalar transitivity, the closed lower-star and open
lower-shriek restriction comparisons, exact restriction of scalars, finite-field flatness and
finite-free coefficient comparison.  I checked that a finite common coefficient field contains
the source and target models, that restriction preserves the lower-shriek factorization and
lissity, and that every finite-field Hom term is killed by the fixed source cutoff.  The source
partition therefore remains independent of the target and the final filtered colimit vanishes.

Finally, `citations.json` was checked against the current statement text of every cited node;
each quote is copied verbatim, and `proof_deps` is the union of the step uses.  The server
`check_dag` preflight reports no introduced finding.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

## What remains

Nothing remains for this item.  The parent unit's imported `c_a` wording still needs the
maintainer action recorded in the item's review metadata; this delivery keeps that issue visible
and does not edit the parent node.
