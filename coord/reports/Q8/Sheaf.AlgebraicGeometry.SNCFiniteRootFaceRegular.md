## What changed

Proved `AlgebraicGeometry.isRegularRing_snc_finiteRoot_face` with its existing signature.
The proof imports `Sheaf.AlgebraicGeometry.SNCRootLocalPresentation` and
`Sheaf.RingTheory.TransverseLocalRootFamilyRegular`, as the current DAG requests.
Fully proved private helpers construct the branch enumeration, identify the face quotient
with the transverse partial-root presentation, commute that presentation with coefficient
localization, and transfer regularity to each prime localization. The original iterated
quotient is recovered by the third isomorphism theorem. The final source also passes the project interface comparison with no interface changes.
All data are explicit quotient,
evaluation, localization, and ring-equivalence constructions; no witnesses are selected
from unproved mere existence results. The node proof now records this assembly. Server single-file compilation passed cleanly
with exit code 0 in 16.5 seconds. The theorem signature is byte-for-byte unchanged; all
Lean lines are at most 100 characters.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.isRegularRing_snc_finiteRoot_face`
(node `lem-sfb-snc-finite-root-face-regular`). Original holes: 1; remaining holes: 0;
added holes: 0; split off: 0. All private helpers are proved.
The proof uses the already declared `AlgebraicGeometry.snc_root_local_presentation`
and `RingTheory.isRegularRing_transverseLocalRootFamily`; their existing holes remain
in their own modules and are not newly introduced by this delivery.

## No longer needed

Removed the following old proof imports from the assigned module:

- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.RingTheory.FiniteType`
- `Mathlib.RingTheory.AdjoinRoot`
- `Mathlib.RingTheory.RegularLocalRing.Polynomial`
- `WeilConjectures.RingTheory.RegularLocalLocalization`
- `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`
- `WeilConjectures.RingTheory.RootAlgebraRegularAtRoot`
- `WeilConjectures.RingTheory.LocalizationOfRegularRing`
- `WeilConjectures.RingTheory.HypersurfaceDerivationRegular`

These were remnants of the original seven-step induction, which now belongs to the
existing transverse-family dependency. The parent's five obsolete direct `tool_uses`
entries are removed: `lem-weil-pbc-regular-local-localization`,
`lem-sc-regular-local-domain`, `lem-sbc-root-algebra-regular-at-root`,
`lem-weil-pbc-localization-of-regular-ring`, and
`lem-weil-pbc-hypersurface-derivation-regular`. Their transitive uses in the dependency
are retained. No DAG dependency node or library module is withdrawn, and neither local
input is pruned. No adopted source-library declaration changes.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The existing theorem docstring describes the old
seven-step proof, while the current DAG already delegates that induction to two stated
inputs. Their Lean interfaces differ at the branch data: the local-presentation theorem
asks for an equivalence with irreducible components and prime principal ideals. The new
proved private branch-enumeration helper derives exactly those from reducedness,
distinctness, and the given equality of component supports.

The local-presentation theorem compares only the full root algebra with its localization;
its face comparison is not assumed. This delivery proves the face and quotient-localization
comparisons directly. Empty J, full J, no branches, zero A, empty/disconnected strata, and
n=1 require no extra hypotheses or case exclusions.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
