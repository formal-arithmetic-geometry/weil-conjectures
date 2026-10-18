## What changed

Completed `DerivedCategory.isPerfect_of_principal_cover` in
`Sheaf.RingTheory.PerfectPrincipalCoverGlue`, keeping its signature and every public
import unchanged. The proof follows Stacks Tag 066Y: descend pseudo-coherence and a
common Tor interval, then apply the existing finite-Tor perfectness criterion.

For the passage from the supplied left derived functors to ordinary localization,
use Mathlib's exact scalar-extension functor, `mapDerivedCategoryFactors`, and
`leftDerivedNatIso`. Added proof-only imports of ModuleCat.Descent,
DerivedCategory.ExactFunctor, and Functor.Derived.PointwiseLeftDerived for these APIs.
Updated the declaration's proof explanation and the existing node's proof route.

The single file compiled cleanly on the remote compiler in 4.0 seconds. The proof
handles the empty cover without a nonempty index instance: finite empty ranges still
have lower/upper bounds, and widening by zero gives an ordered global interval. Local
bounds are first ordered using min/max, so even zero representatives with reversed
original bounds cause no problem. Read Stacks Tags 066Y, 0658 and 0654 in the local source.

## Proved and sorry left

Closed 1 of 1 existing holes:
`DerivedCategory.isPerfect_of_principal_cover`
(node `lem-weil-pbc-perfect-ring-principal-cover-glue`).

No holes remain in the delivered module. Added zero holes; split off zero theorems.
No new axioms, definitions, statements, or modules. This proves the theorem from the
existing declarations as requested; in particular the imported
`DerivedCategory.torAmplitudeIn_of_principal_cover` is an existing downstream proof
obligation, not a hole newly introduced by this delivery.

## No longer needed

Removed these proof-only imports from the item:

- `Sheaf.Algebra.Homology.DerivedChangeOfRings`
- `Sheaf.Algebra.Homology.KFlatResolution`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`

Removed `lem-pur-derived-change-of-rings` and `lem-pc-kflat-resolution` from this
node's proof dependencies and withdrew their existing tool-use entries. Exact
localization is computed by Mathlib directly, so this proof does not need sheaves on
a one-object site or a K-flat resolution. The statement still mentions derived scalar
extension, so its existing statement dependency is preserved. The general-universe
perfect-complex wrapper is unnecessary here: the unchanged theorem uses the source
`IsPerfect`, already publicly imported, with the same bounded finite-projective data.
These modules may remain needed by other proofs; no files are withdrawn.

Kept all other declared mathematical proof dependencies: the finite-free replacement,
pseudo-coherence definition and descent, projective-flat implication, bounded-flat
Tor model, Tor descent, and pseudo-coherent finite-Tor perfectness criterion. The unit's
realized statement and steps are untouched. Searches run through msearch: LeanFinder
for finite principal-cover perfectness (8 results, no matching descent theorem), Loogle
for Functor.IsLeftDerivedFunctor (unknown identifier, no hits), and grep for
perfect/localization/glue (no hits). Direct source searches found the exact-functor
and derived-uniqueness APIs used in step 1.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The original first proof step's
one-object-site construction is longer than needed for flat localization. The existing
interfaces already suffice for every later step. The node attachment for the abstract
perfect-complex notion names `IsPerfectRingComplex`, whereas this older module uses
`IsPerfect`; both definitions unpack to the same bounded finite-projective data at
this theorem's universes, so no new bridge or signature change is required.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
