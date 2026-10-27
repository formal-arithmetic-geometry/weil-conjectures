## What changed

Proved four existing helper theorems in the assigned module, preserving every public
signature, definition body and existing docstring. This is a partial delivery of the
module's five original holes; the final scalar-square theorem remains untouched.

`levelCompatibility` applies the constant-sheaf functor to the given ring-map equation.
`extension_exact` uses the already proved `constantFiniteFree_sectionBasis`: every
coefficient section-ring map is flat, evaluation reflects presheaf limits, and
sheafification is exact. The recorded scalar adjunction gives finite colimits.
The bases need not commute with transitions for this exactness argument.

`restrictionPush_existsUnique` follows from the constant coefficient-ring square and
pushforward composition/congruence. The comparison is identity on every section,
which also proves uniqueness. `betaInv_isIso` identifies open inverse image with
precomposition along the open site map and the inverse transpose ring isomorphism.
Its scalar restriction comparison has an invertible inverse mate, by the site
adjunction unit equation. Two successive mates make the ordinary open-extension
comparison a conjugate of this invertible map. The existing exact-localization
inverse-mate lemma proves invertibility of the specified derived `betaInv`.

All added helpers are private and fully proved. The only added proof dependency is
`lem-pur-constant-finite-free-section-basis`; the node's first two proof steps and
proof origin now describe the formal arguments. No statement or definition repair,
consumer adaptation, new public declaration or new node is included.

Validation: the module compiled through `lcompile.py`, including the final
open-balancing proof. A sandbox compile also checked the exact-localization shift
comparison of `ell`; the scratch module is excluded from delivery. Every Lean line
is at most 100 characters. The delivery command performs the final preflight.

## Proved and sorry left

Closed four of the five original holes (namespace
`AlgebraicGeometry.ProEtale.SemilinearProperOpen.Scalar`):

- `levelCompatibility`.
- `extension_exact`.
- `restrictionPush_existsUnique`.
- `betaInv_isIso`.

Retained, without changing its statement or proof plan:

- `systemProperOpenScalarSquare` (one `sorry`). This contains the intrinsic alpha
  scalar cube after clopen projection, its proper-adjunction mate, direct-image
  composition/identity coherence, and the cochain-shift clauses.

Added holes: none. Split-off statements: none. The file has one actual `sorry`.
This is four holes closed, not a decomposition of the final theorem. Existing
imported theorem assumptions remain as provided by the project.

## No longer needed

Removed the direct proof imports `Sheaf.CategoryTheory.ExchangeMateCube` and
`Mathlib.CategoryTheory.Localization.Predicate`: none of the four closed proofs
uses those imports. The remaining scalar-square proof plan still calls for the
cube and localization tools, so no DAG node or library module is claimed prunable.
An experimental direct import of `Mathlib.RingTheory.Flat.Basic` was also removed;
the required flatness API is already provided by the retained module imports.

The original finite-direct-sum coordinate proof of exactness is unnecessary:
sectionwise flatness and exact sheafification suffice. No separate compatible
basis coordinate-map lemmas are needed for `extension_exact`.

## Where the brief, the DAG or earlier work was wrong

No false statement or process defect was found. The exactness plan was longer than
necessary: positivity of the rank and compatibility of basis vectors are unused
for exactness, although the original public hypotheses remain unchanged.

Open scalar balancing can be proved without building another tensor/open package:
identity-on-sections restriction comparisons, the ringed-site adjunction unit,
iterated mate conjugation and exact localization give the required normalized map.
The remaining theorem still needs a proof on whole derived systems; this packet
does not infer equality from levelwise evaluation or derived scalar restriction.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
