## What changed

Proved `AlgebraicGeometry.smooth_geometric_stalk_algebra` from the four existing
smooth strict-local and polynomial model declarations. The existing public statements,
definitions, instances and public imports are unchanged. Added proved private helpers
for the Gamma-Spec identification of the canonical map, flatness of a specified strict
henselization presentation, pointed-map composition, quotient flatness and locality,
and affine-coordinate flatness and dimension.

The polynomial comparison explicitly reconciles the two chosen separable residue
closures: the quotient induces a residue-field isomorphism, separability transfers
along it, and an equivalence of pointed-etale over categories reindexes the first
colimit presentation to the second closure. No definition obtains data from an unproved existence theorem. The additional
presentation witness used in the proof is constructed by
reindexing the supplied universal cocone.

Updated only the item's theorem node proof, proof dependencies, proof origin. No shared interface repair or consumer adaptation is needed.

Validation: remote single-file compilation through lcompile.py passed, exit code
zero, in 15.8 seconds, with no warnings (result abd1499207269f82305ec6be). The original target statement and all four
existing definition bodies are retained verbatim. Searches used LeanFinder, Loogle,
Mathlib grep and local project rg; the declared model route supplies the geometric
inputs, and quotient-tensor base change supplies the algebraic glue.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.smooth_geometric_stalk_algebra`
(node `lem-trf-smooth-geometric-stalk-algebra`).

Remaining holes in the item: zero. Added holes: zero. Split-off statements: zero.
The proof uses already stated model theorems; their pre-existing proof obligations
remain assigned to their own modules.

## No longer needed

Removed these old direct proof imports:

- `Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison`
- `WeilConjectures.RingTheory.StrictHenselizationNoetherian`
- `Sheaf.Paper.StrictHenselizationFunctoriality`
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale`
- `Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance`
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Sheaf.AlgebraicGeometry.StrictHenselizationClosedImmersionCartesian`
- `Sheaf.RingTheory.SmoothOverFieldRegularLocal`
- `WeilConjectures.RingTheory.StrictHenselizationRegular`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `WeilConjectures.RingTheory.PolynomialOriginRegularLocal`
- `WeilConjectures.RingTheory.StrictHenselizationDimension`
- `Mathlib.RingTheory.Localization.Submodule`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.RingTheory.Flat.Stability`
- `Mathlib.AlgebraicGeometry.Pullbacks`
- `Mathlib.RingTheory.LocalRing.Quotient`
- `Mathlib.RingTheory.RegularLocalRing.Polynomial`
- `Mathlib.RingTheory.Smooth.Flat`
- `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`

No original model dependency is pruned: all four are used. The removed direct
imports describe geometric inputs now encapsulated by those models, or redundant
Mathlib imports. Many remain transitively required by the model modules; this packet
does not claim that any of those source modules can be withdrawn.

The following historical tool approvals are no longer direct proof inputs (their
uses are now inside the stated model lemmas); their approval records are retained: `lem-exc-affine-strict-local-ring-comparison`,
`lem-sc-strict-henselization-noetherian`,
`lem-weil-pbc-strict-henselization-affine-chart-ind-etale`,
`lem-weil-pbc-smooth-over-field-regular-local`,
`lem-sc-strict-henselization-regular`,
`lem-weil-pbc-polynomial-ring-origin-regular-local`, and
`lem-sc-strict-henselization-dimension`.

No module or declaration is withdrawn. The unit's statement and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The DAG's common-closure dimension
step requires an explicit comparison because the affine-coordinate model supplies
two separately constructed separable closures. The private `presentation_repoint`
proof supplies this comparison instead of assuming those types are definitionally
equal. The regular-local conclusions also require the existing regular-local
localization theorem to obtain the requested `IsRegularRing` conclusions.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
