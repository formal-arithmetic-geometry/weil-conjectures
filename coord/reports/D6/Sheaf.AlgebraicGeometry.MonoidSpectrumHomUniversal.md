## What changed

Proved `AlgebraicGeometry.Monoscheme.spectrum_hom_universal` without changing its
statement or either public fraction construction. The bijection and two naturality
clauses use `affine_hom_universal` through its definitionally identical
`affinePullback`. All point and fraction formulas are proved here.

Private helpers construct evaluation from local fractions to the face localization,
extend it to the sheaf using the skyscraper sheaf and sheafification universal
property, and descend to the stalk. This evaluates each numerator germ to p/1.
An inverse in that localization gives p*q=f outside the prime; injectivity into the
group completion and the ideal axiom show p is outside the prime. Conversely the
actual section 1/p supplies an inverse germ. Germ compatibility and locality then
recover the point map. Multiplication of the actual section p/a by a gives p,
and multiplication by the inverse of the given target unit gives the stalk formula.
No cancellation or integrality of the target stalk is used.

Both the assigned module and its unclaimed affine dependency required conversion
to Lean's module format. The dependency changes only in that conversion, preserving
all signatures, definitions, theorem proofs and existing import visibility. See
`coord/changes/D6-monoid-spectrum-module-format.md`. There are no preexisting direct
importers of either module; the assigned theorem is the new dependency consumer.

Searches: msearch LeanFinder for monoid-spectrum local morphisms/global sections
found ring-spectrum localization results, not this monoid statement. Loogle
`"PresheafedSpace.stalkMap"` found the analogous generic germ compatibility;
CommMonCat here has only the filtered colimits needed for the explicitly constructed
stalk, so that equation is proved directly from the colimit. Grep found no direct
Mathlib/source match. A further LeanFinder skyscraper search found the generic
stalk/skyscraper adjunction, which requires all colimits; the proof instead constructs
only the needed cocone and uses the existing skyscraper sheaf and sheafifyLift.

Source checked: ILO VIII, printed pp.98--99, 3.1.2--3.1.6 and Lemma 3.1.8(i).
Edge cases retain the empty prime, group monoids, the trivial monoid, empty source,
a=1 and p=1, and nonintegral target stalks. No unit-level route is changed.

## Proved and sorry left

Closed 1 of the item's 1 holes:
`AlgebraicGeometry.Monoscheme.spectrum_hom_universal`
(node `lem-trf-monoid-spectrum-hom-universal`). No sorry remains in the item.
Validation: the final assigned module compiled cleanly in 12.4 seconds through
lcompile.py; the converted affine dependency compiled cleanly in 5.4 seconds.
All original public signatures and fraction/affinePullback definition bodies were
checked verbatim against the shared sources.
Added 0 holes and split off 0 statements. All private helpers have complete proofs.

The converted dependency retains its preexisting sorry, unchanged:
`AlgebraicGeometry.Monoscheme.affine_hom_universal`
(node `lem-trf-affine-monoscheme-hom-universal`). The proof uses its existing
statement as intended by stage 3. This is the only textual sorry in the delivery.

## No longer needed

`lem-trf-monoid-prime-minimal-neighborhood` and
`Sheaf.AlgebraicGeometry.MonoidPrimeMinimalNeighborhood` are unnecessary for this
proof and are not imported. Evaluation into the face localization and the explicit
inverse fraction establish the needed unit criterion directly, without constructing
a minimal neighborhood or identifying the entire stalk. The node proof and
proof_deps now record this route. No existing import or declaration is removed,
and no module is withdrawn: other consumers may still need that lemma.

## Where the brief, the DAG or earlier work was wrong

Both item and affine dependency were still non-module files, despite the current
module-file requirement. Importing the affine theorem from the converted item
failed with `cannot import non-module ... from module`; converting the unclaimed
dependency repairs this without changing its interface.

The old proof plan's full minimal-neighborhood stalk calculation is stronger than
needed. The existing theorem docstring records that valid source argument; the
updated DAG and the Lean proof use the shorter evaluation/inverse argument above.
There is no disputed statement, target change, new node, or forced adaptation of
a module held by another group.

## Forced adaptations

### Sheaf.AlgebraicGeometry.AffineMonoschemeHomUniversal
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
