## What changed

Proved `CategoryTheory.isLocallyDerivedRingedIdealComplete_derivedInternalHom`
without changing its statement. The private, fully proved `isZero_nestedHom`
uses three tensor-Hom adjunction bijections and the associator/symmetry to
identify endomorphisms of RHom(A,RHom(B,N)) with maps into RHom(A,N).
The latter is zero, so injectivity equates identity with zero.
The main proof applies this on every slice and transports along
`ringedInternalHom_restriction`. The two implementations of derived internal
Hom agree definitionally when all site/module universes are u; both equalities
were checked by `rfl` in the compiled proof.

Replaced the localization/change-of-rings route by the declared closed
symmetric monoidal structure. Updated the node's proof, proof_deps and
proof_origin accordingly. No new node, definition or public theorem is added.
The private helper is proved in full. The unit's route is unchanged.

Validation: the item compiled with exit code 0 in 7.5 seconds, without warnings.
Both direct importers compiled against the changed module: CompletedProjectionCoherence
(9.8 seconds) and RationalThickEvaluation (5.6 seconds). Neither needed adaptation.
The delivery tool runs the final axiom probe.
Change record: `coord/changes/C9-ringed-internal-hom-completeness-imports.md`.

## Proved and sorry left

Closed one hole:
`CategoryTheory.isLocallyDerivedRingedIdealComplete_derivedInternalHom`
(node `lem-sf-ringed-rhom-derived-complete`).

Holes remaining in the item: zero. Holes added: zero. No split-off theorem.
The proof uses the existing declared restriction comparison and closed
symmetric monoidal structure; their outstanding proofs remain their own items.
This is a proof from those declarations, not a claim that their axioms are closed.

## No longer needed

Removed these imports from the item:

- `Sheaf.CategoryTheory.RingedSiteLocalization` (public): the completeness
  definition already supplies its actual section localization; no telescope
  construction or telescope calculation is used in the proof.
- `Sheaf.Paper.EtaleDerivedScalarTensor`: no scalar tensor implementation is used.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`: scalar extension
  to the localized ring is unnecessary.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`: the proof does
  not use shifts or independent-universe shift comparisons; the actual
  small-site restriction declaration is in RingedInternalHomExactRestriction.
- `Sheaf.SixFunctors.RingedLocalizationRHomOrthogonality`: arbitrary-source
  vanishing follows directly by adjunction and symmetry.

Removed proof dependencies `lem-pur-derived-change-of-rings`,
`lem-sf-ringed-localization-rhom-orthogonality`, and
`def-weil-pbc-ringed-site-section-localization`. The last remains a statement
dependency of the unchanged node; only its role as a separate proof tool is
removed. Added `lem-sf-ringed-derived-closed-symmetric-monoidal` as the actual
proof dependency. The exact-restriction node remains needed for its restriction
comparison, though its shift and currying declarations are unused here.
These are dependencies pruned from this item's route; other parents may still
need them. No library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old plan's localized change of rings and orthogonality theorem are
unnecessary in a closed symmetric monoidal category. A Hom-set bijection
argument proves the required vanishing directly. The original small-site and
independent-universe internal Hom implementations do agree definitionally at
the universes of this statement: the earlier review had left that unverified.
No statement defect or target change was found. The helper works for any A,
including zero, and requires no boundedness or finiteness. Zero objects, a zero
ideal, the unit ideal and an empty site cause no additional cases.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
