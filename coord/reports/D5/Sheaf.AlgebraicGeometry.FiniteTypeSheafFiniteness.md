## What changed

Proved `AlgebraicGeometry.Etale.finiteType_directImages_finiteConstructible` in
`Sheaf.AlgebraicGeometry.FiniteTypeSheafFiniteness`, preserving its complete signature.
Two proved private helpers show that a constructible sheaf in degree zero is bounded
constructible, and that this property transfers along an isomorphism. The main proof applies
the stated ordinary finiteness theorem, extends by zero in the prescribed Nagata
compactification, applies the stated proper finiteness theorem, and applies the stated
original-geometric-fibre amplitude theorem. The exact functor/single-functor isomorphism
identifies the compact-support candidate. Added the proof-only constructibility-comparison
import. Updated the node proof and dependencies to match the implementation.

The proof follows the source proof in the current main-20261015 blueprint, which agrees
with the older node source, and preserves the unit route. The unit has no realized proof
steps to bypass. No definitions or existing signatures changed; no change record is needed.
Static checks confirm that the main theorem signature is byte-for-byte unchanged, all Lean
lines are at most 100 characters, and the node proof dependencies equal the union of its
step dependencies. The delivery dry run supplies compilation and declaration checks.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.finiteType_directImages_finiteConstructible`
(node `sbc-thm-finiteness-finite-type`). Added zero holes and zero split-offs.
No `sorry` remains in the delivered Lean file. Both private helpers are fully proved.
The imported `isZero_homology_rightDerivedLowerShriek_of_geometricFiberDimensionLE`
remains an existing dependency with its own node `lem-dg-compact-support-amplitude`;
this delivery does not claim to prove that dependency or eliminate all transitive axioms.

## No longer needed

Removed proof-only imports:

- `Mathlib.AlgebraicGeometry.Noetherian`.
- `WeilConjectures.Compactification.NagataCompactification`.
- `WeilConjectures.Compactification.Defs`.
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`.
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`.

The last is the unused compactifiability theorem (`def-asd-compactifiable`): the signature
already supplies `compactSupportAmplitudeCompactification`. Nagata and compactification
definitions remain needed through that existing helper; removing their redundant direct
imports does not withdraw those nodes. The existing public imports remain as the statement
interface. The new proof-only import is
`Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`.

Removed `lem-amb-etale-compact-comparisons` from the direct proof dependencies: the theorem
already states the chosen compactification candidate, so no comparison-independent functor
occurs in its conclusion. No proof step depends on
`etaleCompactSupport_refinementComparison_eq`.
Removed the direct Noetherian/quasi-separated tool uses
`lem-weil-pbc-finite-type-over-noetherian` and
`lem-weil-pbc-locally-noetherian-quasi-separated`: their checks are internal to the already
supplied compactification helper. This does not claim those foundational nodes are globally
unreachable. No module is withdrawn or deleted.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement is unchanged and matches the blueprint. The old plan did more
work than its Lean signature requires: compactification comparisons are unnecessary for an
explicit chosen-candidate conclusion. The class `HasInvertibleExponent` only asks for a
positive annihilating integer that is invertible; it does not demand the minimal exponent.
Thus the original coefficient N suffices, including for the zero ring, without an
additive-order argument. Quasi-compactness of the open immersion follows directly from
`Compactification.quasiCompact_openImmersion`.

Searches used the prescribed LeanFinder, Loogle, and grep service and source searches.
LeanFinder gave no finiteness theorem; Loogle found the canonical degree-zero homology
isomorphism; source search located the exact-functor/single-functor isomorphism and the
existing declared finiteness inputs. No counterexample or statement repair was required.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
