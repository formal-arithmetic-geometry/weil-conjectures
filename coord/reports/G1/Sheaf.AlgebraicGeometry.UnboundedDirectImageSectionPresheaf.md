## What changed

Filled `AlgebraicGeometry.RingedSpace.unboundedDirectImage_sectionPresheaf` with a proof
of the prescribed Leray and normalized sheafification comparisons. All existing public
signatures and constructions are preserved. Added private, proved helpers and proof imports
for Sierpiński topology, stalks, and sectionwise detection of quasi-isomorphisms.
The representative arguments use the published functorial K-injective replacement
already used by the definitions. Two elaborator transparency options avoid expensive
backward inference in the unchanged definitions; the proofs restore stricter inference
and locally keep the chosen derived-functor constructions irreducible, using their API.

The acyclicity argument applies the existing ringed-space direct-image acyclicity theorem
to the continuous Sierpiński classifier of an arbitrary open. The distinguished singleton
is its least neighborhood, so evaluation there equals the exact stalk functor. This gives
all sections of the resolution map at once. Universal-unit factorization then proves the
specified Leray comparison invertible. Naturality of the specified sheafification model
comes from the derived units, exact sheafification, and chain-map lifts into K-injectives.

Change record: `coord/changes/G1-unbounded-section-proof-elaboration.md` documents
the local elaboration commands requested by preflight and all seven downstream users.
No consumer adaptation is required.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.RingedSpace.unboundedDirectImage_sectionPresheaf`
(node `lem-trf-unbounded-direct-image-section-presheaf`).

Holes closed: 1. Holes added: 0. Split off: 0. No `sorry` remains in the delivered module;
all private helpers are proved. Imported dependencies retain their existing proof status.

Validation: the complete item compiled cleanly through `lcompile.py` in 36.4 seconds,
with no warnings or errors. The original theorem statement is unchanged, and all Lean
lines have at most 99 characters. A temporary independent consumer checked all
14 public declarations and confirmed that the completed theorem uses only `propext`,
`Classical.choice`, and `Quot.sound`; the diagnostic source is excluded from delivery.

## No longer needed

Removed these private proof imports:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: unused by the actual constructions and proof.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`: the published
  functorial K-injective replacement is already provided by the source direct-image API.
- `WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen` and
  `WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact`: the Sierpiński
  classifier proves section acyclicity without restricting module categories to opens.
- `Sheaf.AlgebraicGeometry.RingedSpaceSheafificationCohomology`: its existential
  presheaf comparison does not supply the required fixed components. The proof uses the
  explicit exact-sheafification/homology natural isomorphism in the existing definitions.

Removed the corresponding unused proof dependencies and top-level tool approvals:
`lem-sc-derived-k-injective-restrict-open`,
`lem-sc-derived-open-restriction-adjunction-exact`, and
`lem-pc-ringed-space-sheafification-cohomology`.
These are pruned from this proof only; no module or source declaration is withdrawn.
No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The DAG's open-restriction/one-point route is longer
than needed given the already proved arbitrary-ringed-space direct-image acyclicity
statement. The node now records the Sierpiński argument and the direct proof of
naturality for the fixed sheafification model. Edge cases include the empty open,
zero complex, identity morphism, and arbitrary degrees; no boundedness or flatness
hypothesis is introduced.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
