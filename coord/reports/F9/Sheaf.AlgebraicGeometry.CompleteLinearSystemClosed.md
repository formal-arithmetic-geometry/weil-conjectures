## What changed

Proved `AlgebraicGeometry.completeLinearSystem_isClosedImmersion` in
`Sheaf.AlgebraicGeometry.CompleteLinearSystemClosed`, with its original signature unchanged.
The proof extends the given independent family to a finite basis, transfers generation by
inclusion of stalk spans, and obtains the section-preserving pullback isomorphisms by comparing
the native chart construction with `homOfGeneratingSections`.

The source theorem `ProjectiveSpace.mono_of_eq_sum_smul` applies with Kronecker coefficients
because every original section is a coordinate of the extended basis. Properness follows
from `IsProper.of_comp`. Mathlib's proper-monomorphism characterization then gives the closed
immersion. This avoids constructing the projection on an open domain.

Added only proved private helpers `nativeHom_eq_generatingSections` and
`generatingSections_pair`; no definitions, instances, existing statements, public imports,
or consumers changed. Updated the item's proof docstring and its DAG proof route.

Validation: the final module compiles through `lcompile.py`, exit code 0, in 7.3 seconds,
without warnings. The source theorem signature was compared mechanically with the original.
The exported-interface checker reports no changes after scoping all new opens to individual
proofs. All empty cases are covered by the same argument: finite-dimensional zero section spaces,
empty bases, vacuous stalk conditions and the native chart construction require no nonempty
coordinate or nonempty scheme hypotheses. The deliver3 preflight additionally checks axioms.

## Proved and sorry left

Closed 1 existing hole:
`AlgebraicGeometry.completeLinearSystem_isClosedImmersion`
(node `lem-pc-complete-linear-system-closed`).

Added 0 holes; split off 0 unfinished results. There are 0 `sorry` tokens in the delivered
Lean module, including its two private helpers. The two new nodes attach existing proved
results and add no Lean module or proof obligation. Imported declarations retain their
existing upstream dependencies; this report does not claim the full targets are axiom-free.

## No longer needed

Removed these private imports from the item:

- `Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts`
- `Sheaf.Paper.EulerCharacteristicWellDefined`
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`
- `WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper`

The invertibility declarations remain available through the unchanged public imports.
Coherent cohomology is used directly from `Cohomology.DirectImage.AffineMorphism`.

The proof no longer needs these original direct DAG dependencies:

- `lem-weil-pbc-finite-type-over-noetherian`: finite presentation follows directly from
  invertibility, without proving the scheme locally Noetherian.
- `pqf-lem-coherent-ft-locnoeth`: unnecessary for the same reason.
- `lem-weil-pbc-projective-space-functor-of-points`: its separate theorem is not used;
  the already proved generating-sections construction provides the needed integral pair.
- `lem-weil-pbc-projective-space-standard-charts`: the native construction supplies the
  chart-generator API needed by the private comparison helpers.
- `lem-weil-pbc-projective-space-proj-separated`: use the relative projective-space properness
  instance instead.
- `lem-weil-pbc-separated-cancellation`: no open-domain projection is constructed.
- `lem-weil-pbc-closed-immersion-cancellation`: use the source monomorphism criterion instead.
- `lem-weil-pbc-proper-immersion-closed`: use the proper-monomorphism criterion instead.

Removed the obsolete entries of the item's `tool_uses` list for these dependencies.
No module or declaration is withdrawn; these are imports and dependencies pruned from this
proof, and do not assert that no other target path needs the same modules.

## Where the brief, the DAG or earlier work was wrong

The original plan is valid but longer than the source-library route now available.
`ProjectiveSpace.LinearCombination` already proves the monomorphism argument that avoids
constructing and comparing an explicit projective projection. The old local-Noetherian
coherence detour is also unnecessary: invertibility gives finite presentation directly.

No statement repair is needed. In particular, the theorem still allows the empty scheme
and empty index types. No source-library declarations, signatures, attributes or public
imports were changed, and no unit statement or realized step was bypassed.

## New nodes

`lem-pc-projective-pair-linear-mono` attaches the already proved source declaration
`AlgebraicGeometry.ProjectiveSpace.mono_of_eq_sum_smul` in
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination`. It is a generic
projective-coordinate lemma, specialized here to finite target coordinates. The source
allows arbitrary target coordinate types. Its source is the standard-chart argument of
Stacks 01NE. The semantic search for this lemma was unavailable; the Loogle and source
searches are recorded accurately. This node adds no hole.

`lem-pc-proper-monomorphism-closed` records the exact Mathlib leaf
`AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono`, read in
`Mathlib.AlgebraicGeometry.ZariskisMainTheorem` at line 393, Stacks 04XV.
The search records contain the actual LeanSearch, Loogle and grep results. This node adds
no hole. Both nodes are in the item's chapter and unit, with the same blueprint ancestor.

No change record is required: no existing definition, statement or exported environment
changed, and no consumer adaptation was made.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
