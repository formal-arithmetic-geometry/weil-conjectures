## What changed

Filled `AlgebraicGeometry.Etale.derivedEtaleStalkSpecialization_restriction` in
`Sheaf.AlgebraicGeometry.DerivedSpecializationRestriction` without changing its statement,
definitions, public imports, or existing docstring. Added a private proof import of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeNaturality`
for its homotopy left-whiskering formula. Private categorical helpers identify the
exact right-derived comparison on a localized complex, and prove compatibility with a
restriction, a left-whiskered germ, and an inverse-image stalk isomorphism. Localization
extensionality reduces the latter identity to the termwise composite. The public theorem
then applies that identity to the defining underived specialization and cancels the adjacent
global-sections comparison isomorphisms.

The argument follows the existing node's two steps and Stacks etale-cohomology.tex,
section-specialization and remark-alternative-sp (Tag 0GJ2). It retains every original
hypothesis, including arbitrary geometric test points and arbitrary bounded-below complexes.
No new mathematical assumptions or public declarations are introduced.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.derivedEtaleStalkSpecialization_restriction`
(node `lem-weil-pbc-derived-specialization-restriction`): one original hole.
Added: none. Remaining in the item module: none. Split off: none.
All private helpers have complete proofs. Remote single-file compilation accepted the complete
proof in 13.8 seconds; the final unused-simp-argument warning was removed before delivery.

## No longer needed

None. Both original public imports supply declarations in the theorem's statement. The
proof uses the existing specialization, restriction, exact strict-local sections, and
comparison APIs, and preserves the node's existing dependency route. In particular this
proof does not use `derivedFiberMap_restriction`, the separate remaining theorem in
`Sheaf.AlgebraicGeometry.DerivedFibreRestriction`; that module is still needed for
`derivedGlobalGermAt` and `derivedPullbackStalkIso` in the statement and is not withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repair was needed. The stated termwise proof can be implemented
using the existing localization and right-derived unit comparison formulas. The remote
search returned generic `rightDerivedNatTrans_comp` results, while Loogle did not recognize
the project's exact-comparison declaration; direct source reading supplied the necessary
bounded-below comparison formulas. There is no new node or change record.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
