## What changed

Completed `AlgebraicGeometry.Etale.NoetherianSectionSpecialization.existsUnique_normalized`
and `AlgebraicGeometry.Etale.NoetherianSectionSpecialization.baseChange_compatibility` in
`lean/Sheaf/Paper/NoetherianEtaleSectionSpecialization.lean` without changing their statements,
existing public statements, definitions or public imports.

The first proof adapts the proved centred affine charts to the existing local dualizing
comparison interface, constructs its raw comparison, corrects its restriction at one by
its inverse, and applies normalized descent of shifted rank-one sheaves. The over-site
trivializations in `lines_and_fibres` are transported through the canonical over-sheaf
equivalence. Compactifiability of the local interface's symmetric normal projection follows
from its stated zero-fibre square and Nagata.

The second proof builds the geometric `ExceptionalSectionFamily` and base-change diagram
from the actual Rees deformation and its canonical fibres. The one-fibre compatibility is
proved by the Cartesian universal property and the forgetful map to V; normal-fibre
compatibility is the defining lift equation. Smooth affine coordinates supply regular
sequences over the changed base. The existing exceptional-fibre coherence theorem, uniqueness
on both bases, and the existing shared compositor endpoint theorem give both requested equations.
All added geometric definitions and private lemmas are fully proved.
To control compilation cost, `lines_and_fibres` now reuses the same existing local
comparison theorem for its shifted-line clauses; its signature and canonical fibre
maps are unchanged. The old duplicate private `section_line` proof is no longer needed.

Added proof imports: `Sheaf.Paper.SectionLocalDualizingComparisons`,
`Sheaf.AlgebraicGeometry.SmoothSectionAffineCoordinates`,
`Sheaf.AlgebraicGeometry.EtaleShiftedLineNormalizedDescent`, and
`Sheaf.Paper.SectionExceptionalFibreCoherence`.
Updated the item's DAG proof, proof dependencies and proof origin to record these uses.
The blueprint's local construction, normalization, gluing and base-change route is retained.
The proof works without extra assumptions in relative dimension zero and over the empty base;
its covers and pointwise arguments require no nonemptiness, and base change need not be flat.

Returned-delivery repair: removed the duplicate private `compositor_endpoint` theorem.
Reuse the existing proved `AlgebraicGeometry.Etale.sectionPullback_endpoint` directly
in `line_compositor` via `import all Sheaf.Paper.SectionExceptionalFibreCoherence`.
This is a private proof import: it exposes the imported module's private helper only
inside this file. The dependency module, its visibility, statement and proof are unchanged.
The normal-name lookup was verified in a compiler probe; no mangled private names are used.

## Proved and sorry left

Closed both original holes (2 of 2):

- `AlgebraicGeometry.Etale.NoetherianSectionSpecialization.existsUnique_normalized`.
- `AlgebraicGeometry.Etale.NoetherianSectionSpecialization.baseChange_compatibility`.

Zero holes remain in the item module. Zero holes added; zero statements split off.
The complete repaired item compiled with `lcompile.py` in 49.4 seconds, under the
60-second file limit. Its only diagnostic was the temporary profiler-option warning;
the profiler option has been removed for delivery. All 20 original public declaration
headers and all public import lines are unchanged. The item contains no `sorry`.
No dependency module is delivered or modified.
Existing imported declarations with unfinished proofs remain their own project items,
including normalized descent; the local dualizing comparison and fibre-coherence
modules currently have no direct `sorry`. This delivery proves the
item from those named declarations as required by stage 3; it does not claim their proofs
have also been completed.

## No longer needed

Removed the duplicate private `compositor_endpoint`; reuse the original shared theorem.

Removed the following direct proof imports:

- `WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality`.
- `WeilConjectures.ConstructibleSheaf.Pullback`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`.
- `Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction`.
- `Sheaf.AlgebraicGeometry.ConstantSheafSetSectionsConnectedNatural`.
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`.
- `Sheaf.AlgebraicGeometry.EtaleLocalNormalForm`.
- `Sheaf.AlgebraicGeometry.SmoothTensorDuality`.
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`.

Their mathematics is accessed through the named comparison, descent and coherence lemmas
where necessary. No node or module is withdrawn: the original lower arguments can still
be needed by these packaged lemmas or other consumers, and this delivery does not claim
global pruning of their dependencies. No top-level tool-use approvals were removed.

## Where the brief, the DAG or earlier work was wrong

The return correctly identified a duplicate of an existing private theorem.
That helper is now accessed through Lean’s private `import all` and reused.
Its original module and interface are unchanged; no duplicate proof remains.

No statement defect was found. The old plan did not mention that existing declared
interfaces already package the local comparisons, descent and exceptional-fibre coherence.
Those interfaces implement the same route. The local-comparison interface additionally
requires compactifiability of its symmetric normal projection; its existing Cartesian
zero-fibre theorem supplies the geometry needed to derive that requirement.

No new nodes, definition repairs, forced adaptations or source-library edits.
No change record is needed: there is no definition, statement or visibility change.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
