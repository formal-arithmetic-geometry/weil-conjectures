## What changed

Withdraw the duplicate `Sheaf.AlgebraicGeometry.FppfAffineRefinement` and attach
`lem-pc-fppf-affine-refinement` to the fully proved declaration with the identical
name, signature and universes in
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc`. The mathematical node,
parent uses and unit route remain intact.

Replace only the private import in five current direct consumers:
`AlgebraicSpaceFppfFiniteAffineRefinement`, `FppfAffineRefinementPullbackModel`,
`FppfAffineSiteToposEquivalence`, `FppfSheafRepresentabilityDescentData`, and
`FppfSheafificationAffineContinuity` (all under `Sheaf.AlgebraicGeometry`).
Every declaration, signature, public import and proof body stays verbatim.

Repair the return at `ff32e2d5042` by taking the current
`AlgebraicSpaceOpenGluing` source, preserving the complete R5 proof landed at
`b3210a1419a` and all its private helpers. It already omits the withdrawn import.
Also preserve the now-complete `FppfFamilyCoproductDescentEncoding` proof and all
previously refreshed proofs. These preserved copies equal current source verbatim and are archived under
`scratchpad/preserved`; unchanged files are omitted from the delivery set.

Validation: `lcompile.py --all` passed all twelve sandbox modules. The source
and duplicate signatures are textually identical; every actual Lean edit is one
private import replacement, with all lines at most 100 characters.

Change record: `coord/changes/C7-fppf-affine-refinement-upstream.md`.

## Proved and sorry left

Closed 1 of 1 item holes by reuse of the existing complete source proof:
`AlgebraicGeometry.Scheme.exists_finite_fppf_affine_open_refinement`
(node `lem-pc-fppf-affine-refinement`). Zero item holes remain; zero holes added
or split off. This is duplicate retirement, not a new proof or decomposition.
A fresh server `#print axioms` check reports only `propext`, `Classical.choice`
and `Quot.sound`.

Four adapted consumers retain their existing holes unchanged:

- `AlgebraicGeometry.AlgebraicSpace.exists_finite_affine_fppf_refinement`.
- `AlgebraicGeometry.fppf_affine_site_topos_equivalence`.
- `AlgebraicGeometry.fppfSheafRepresentabilityDescentData`.
- `AlgebraicGeometry.Scheme.fppfSheafification_affineContinuity`.

The adapted `FppfAffineRefinementPullbackModel` and the seven unchanged consumer
proofs have zero holes. The latter are preserved from current source and are not
part of the delivery diff.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.FppfAffineRefinement`. All five current
direct consumers replace its private import by the source module. Former
consumers whose current proofs already omit it receive no delivered edit.
The withdrawn module's two public imports disappear with it; consumer public
imports stay verbatim. No source-library declaration or module is removed.

No mathematical dependency is pruned: affine neighborhoods, openness of flat
locally finitely presented maps, and compactness remain used by the source proof.
Every parent DAG reference still points to the same node, reattached to that
proved source theorem. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The assigned theorem duplicated one already proved in the adopted source library.
The returned packet predates the complete R5 gluing proof. It now preserves that
proof verbatim rather than replacing it with its old hole. The coproduct descent
proof has also landed since the previous packet and is likewise preserved.
Two new direct importers are included in the withdrawal adaptations.

The empty-base case permits the empty finite family; an empty original covering
can cover only the empty base. The source signature preserves both independent
universe parameters and the complete fppf covering hypothesis.

## Forced adaptations

Five private import replacements are required by withdrawal step 8b:

| Module | Holder | Changed line |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfFiniteAffineRefinement` | unclaimed | 12 |
| `Sheaf.AlgebraicGeometry.FppfAffineRefinementPullbackModel` | unclaimed | 11 |
| `Sheaf.AlgebraicGeometry.FppfAffineSiteToposEquivalence` | unclaimed | 10 |
| `Sheaf.AlgebraicGeometry.FppfSheafRepresentabilityDescentData` | F7 | 10 |
| `Sheaf.AlgebraicGeometry.FppfSheafificationAffineContinuity` | unclaimed | 14 |

Each line changes from `import Sheaf.AlgebraicGeometry.FppfAffineRefinement` to
`import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc`. This supplies the
identical proved theorem and removes the withdrawn dependency. Every other line
is verbatim, including every declaration signature and visibility.

No original-file compiler error is asserted: the withdrawal import-prune check
requires every direct importer to be adapted, including proof-only imports in
currently unfinished consumers. The delivery tool explicitly recognizes imports
of modules in `deleted.txt` as necessary migrations, since compiled copies of
the retired module are not valid counterfactual dependencies. Adapted modules
compile; the independent reader verifies the migration.

The first preflight attempt refused this section because it named the F7 module
only by its basename. This revision gives the exact full module names. All Lean
compiles and axiom probes had passed before that report-only refusal.

## Forced adaptations

### Sheaf.AlgebraicGeometry.FppfSheafRepresentabilityDescentData
Original imports module(s) explicitly withdrawn in deleted.txt: Sheaf.AlgebraicGeometry.FppfAffineRefinement. Those imports must be migrated in this delivery; the baseline's compiled copies are not valid counterfactual dependencies. Adapted module compiled in the delivered set. CODEX verifies the migration and every accompanying API adaptation is needed.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
