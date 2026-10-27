## What changed

`WeilConjectures.PoincareDuality.Verdier.isIso_verdierBiduality` now reduces the
unchanged canonical biduality map to the sheaf case using bounded truncation.
The assembly uses the two components of the bounded-constructible object's
property and reflection of isomorphisms by the full-subcategory inclusion.
A proved private generic helper handles that inclusion without expanding the
large derived monoidal structure. Reducibility is changed only locally during
elaboration; no library definition or instance body changes.

Added `Sheaf.PoincareDuality.BidualityTruncation`, whose public theorem
`CategoryTheory.MonoidalClosed.biduality_of_bounded_heart` is fully proved.
The proof establishes shift invariance using the invertible shifted unit,
checks extension closure with two applications of internal Hom and the
triangulated five lemma, and applies the existing bounded t-structure induction.
Added `Sheaf.PoincareDuality.ConstructibleSheafBiduality` for the separate
geometric input in degree zero. Its source, evaluation normalization, coefficient
passage, proof in words and edge cases are recorded with the statement.

The item adds only private proof imports and a proved private helper. Every
existing public import, declaration signature, attribute and non-theorem body
is preserved. No other existing module is adapted. Change record:
`coord/changes/S6-verdier-bounded-truncation.md`.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_verdierBiduality`.
Its proof from the geometric sheaf input is complete.

Added and proved, with no holes:
`CategoryTheory.MonoidalClosed.biduality_of_bounded_heart`
(node `lem-pd-biduality-finite-truncation`). All its private helpers are proved.

Exactly one new hole remains:
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_biduality_constructible_sheaf`
(node `lem-pd-constructible-sheaf-biduality`). This restricts the geometric
assertion to a constructible module sheaf placed in degree zero; it does not
quantify over arbitrary bounded complexes or assume biduality as a hypothesis.
The nontrivial formal step from this restricted assertion to the original
bounded-complex assertion is proved in this delivery. This is a decomposition:
one hole closed, one hole added, net zero. No sorry remains in the item itself;
there is one sorry in all delivered Lean files, and none in definitions.

Validation: both new modules compiled together against the published library
(the formal reduction in 31.2 seconds and the geometric statement in 57.9
seconds). After correcting the private inclusion helper, the original item
compiled cleanly in 39.0 seconds with the new module artifacts. No compile
limit was raised. The required delivery command runs its own final checks.

## No longer needed

No existing node or module is withdrawn. All original public imports are kept
under the source-library boundary. The new finite-truncation module retains its public
`WeilConjectures.SixFunctors.Etale.Derived.DoubleDual` import: testing its
privatization exposed native derived monoidal instances needed to elaborate
the public signature. The geometric sheaf module has only the imports used
by its statement.

The proof does not import `Sheaf.SixFunctors.CoefQbarVerdier` or
`Sheaf.Paper.SfBidualityClass`: their fixed finite-field and coefficient-model
interfaces do not directly express the arbitrary-field condensed assertion.
They remain needed elsewhere and are not claimed as pruned. The original
lisse and open-closed declarations in the adopted source module are preserved.
No realized unit statement or realized unit step is bypassed; the unit record
has no separate realized steps. The geometric leaf retains the finite-stage,
integral and field coefficient-duality route in its proof in words.

## Where the brief, the DAG or earlier work was wrong

The current source module has one hole but no node whose lean.module attaches
to this module; it is therefore given an explicit new attachment in this
packet. The existing `thm-coef-qbar-verdier` is not a drop-in proof: its field
is the fixed algebraic closure of a finite field, while the current source
statement permits any field of positive prime characteristic different from
ell. The stronger existing finite-coefficient source theorem over arbitrary
algebraically closed fields is useful inside the geometric coefficient
argument, but does not itself supply its condensed coefficient transports.

The old upstream-statement-exception entries about relative biduality on a
singular base concern the superseded statement. The current source already
requires the structure morphism to Spec k; it is preserved. The new sheaf
lemma explicitly requires its target to map isomorphically to Spec k, so it
cannot reintroduce the singular-relative-base counterexample. Empty schemes,
zero sheaves and shifts require no positive-rank or nonempty hypothesis.

No tool is bypassed or patched, and no source declaration is removed. Slow
elaboration was handled by a generic proved inclusion lemma and a locally
irreducible derived closed structure, without increasing the compile limit.

## New nodes

`lem-pd-biduality-finite-truncation` records the fully proved generic reduction
from the heart to bounded complexes, with the actual shifted-unit, exactness,
five-lemma and truncation proof.

`lem-pd-constructible-sheaf-biduality` records the one remaining geometric
sheaf input, its precise normalized exceptional dualizing object, the integral
finite-reduction proof, and the rational/algebraic-closure coefficient passage.
The cited potential-duality nodes retain the general excellent-scheme scope;
the finite-field-only wrapper is not applied to an arbitrary field.

`lem-pd-condensed-verdier-biduality` attaches the unchanged item theorem and
records exactly the sheaf input, constructibility transport and proved finite
truncation used by the Lean proof. All new nodes record the three required
kinds of searches and their results. The relevant new interface record is
`coord/changes/S6-verdier-bounded-truncation.md`.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
