## What changed

Proved both theorems in `Sheaf.Paper.OrientationCoefficientTwists`, preserving every
public signature and every definition body. Added private proof imports of
`Sheaf.Paper.IntegralResidueTor`, `Sheaf.Paper.SfIntegralConstructibleTriangulated`
and `Mathlib.Data.Nat.Prime.Infinite`. Added one fully proved private helper for
lifting an ambient isomorphism uniquely after identifying its source object.
Updated the owning node's proof and proof dependencies to match the implementation.

The membership proof uses `sfIntegralTwistingObject_mem`, the standard single-functor
shift comparison, and constructible shift/isomorphism closure. An auxiliary prime
strictly greater than ell supplies the unused finite-field parameter of
`integral_residue_tor`; it imposes no field structure or finiteness condition on X.
Its equality of predicates then supplies uniform finite Tor amplitude.
The scalar lift uses the rational scalar functor's specified object formula and
`ObjectProperty.isoMk`; uniqueness follows from hom extensionality and `Iso.ext`.
Neither proof excludes d=0, empty X, or identity coefficient extensions.

Searches: LeanFinder found `CategoryTheory.ObjectProperty.isoMk`; Loogle confirmed
its signature. Local rg found the existing Tate membership, constructible
triangulation and residue-Tor declarations. The launcher's grep query returned no
hits; the successful local source searches supplied the needed library results.

## Proved and sorry left

Closed 2 original holes:

- `WeilConjectures.sfOrientationIntegralComplex_mem`.
- `WeilConjectures.sfOrientationRationalScalarLine_existsUnique`.

Both belong to `def-sf-orientation-scalar-line-comparisons`.
Remaining holes in the item: zero. Added holes: zero. Split-off statements: zero.
The proofs use existing library declarations; this does not claim that all their
transitive dependencies are sorry-free. Final single-file remote compilation succeeded cleanly in 19.8 seconds.
The delivery preflight checks the complete packet and declaration axioms.

## No longer needed

None. No existing import, declaration, module or node is withdrawn. The original
node had no proof dependencies, so there is no old planned dependency to prune.
The public imports retain the published coefficient and geometric interfaces.

## Where the brief, the DAG or earlier work was wrong

The owning definition node had empty proof steps although its module contained two
proof obligations. The recorded proof now explains both. No statement correction,
definition repair, consumer adaptation or change record is needed. The membership
proof can reuse the general residue-Tor equality instead of rebuilding finite-level
root trivializations and amplitude calculations here. The unit record has no
realized proof steps, and its orientation interface and route are preserved.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
