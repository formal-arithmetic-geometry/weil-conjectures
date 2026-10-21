## What changed

Proved `AlgebraicGeometry.Etale.scalarSupportTriangle_mate_identification` in
`Sheaf.Paper.SupportedTriangleMateIdentification`, preserving every existing public
signature and definition. Added five proved private helpers: additivity and
triangulatedness of scalar extension, reflection of isomorphisms by derived
restriction, preservation of open vanishing by scalar extension, and supported/open
orthogonality after restriction. Updated the existing node's proof and dependencies
to follow this argument. No new module or statement is needed. The local transparency commands have the
preflight-requested change record
`coord/changes/B9-supported-triangle-proof-transparency.md`; they affect only proof
elaboration within this file.

The alternative route uses the existing proved tools
`prop-openclosed-lowerstar-fully-faithful` and
`lem-exc-kinjective-derived-fully-faithful` to reflect isomorphisms through closed
direct image. These are the existing sheaf and K-injective derived full-faithfulness
APIs, rather than new assumptions or changes to the unit route.

The orthogonality argument uses the scalar/pullback isomorphism twice and the
restriction/pullback isomorphism once. The composite scalar/open adjunction transfers
the Hom group to maps out of a zero object. The existing triangle cancellation lemma
then identifies the first component by its counit equation. Naturality gives the
transported equality. Triangle two-of-three, cohomology conservativity of restriction,
and full faithfulness of derived closed direct image give the isomorphism conclusion.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Etale.scalarSupportTriangle_mate_identification`
(node `lem-pur-supported-triangle-mate-identification`).

The final item compiled cleanly through `lcompile.py` in 10.4 seconds.
No holes remain in the item. No holes are added, and none are split off. All five
private helpers have complete proofs. The proof uses the existing library APIs;
this report does not assert that all their transitive dependencies are sorry-free.

## No longer needed

Removed these private imports:

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint` (already public through
  `EtaleClosedSupportTriangle`).
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`.
- `Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.

Removed direct proof dependencies and their obsolete tool approvals:
`lem-pur-derived-change-of-rings`,
`lem-trf-oriented-closed-base-localization`, and
`prop-weil-pbc-inverse-image-modules-exact`.
The actual coefficient adjunction gives triangulatedness, and the scalar/pullback
isomorphism gives open vanishing. Fully faithful derived closed direct image reflects
isomorphisms directly. Thus no termwise closed-direct-image/restriction comparison,
bounded-below open direct-image comparison, or descent of the closed counit is needed.

All original public imports stay unchanged. No module is withdrawn; other callers
and transitive public dependencies may still need the listed modules. The blueprint
unit's statement and route stay unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original DAG plan required more comparison machinery
than necessary. Existing scalar/pullback and restriction/pullback isomorphisms prove
the needed orthogonality without comparing direct images with restriction. Existing
fully faithful derived closed direct image also eliminates the separate counit-descent
step. The original boundedness hypotheses are preserved, although this proof does
not need them. The transported equality needs only naturality, not invertibility of
`scalarRestrictionDirectImageMap`.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
