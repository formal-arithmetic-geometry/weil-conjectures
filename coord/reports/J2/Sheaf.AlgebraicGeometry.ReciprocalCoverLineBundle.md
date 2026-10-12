## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_line_bundle_sections_of_reciprocal_cover`
in `Sheaf.AlgebraicGeometry.ReciprocalCoverLineBundle`, preserving its full signature,
visibility, and existing docstring. Four private helpers construct the
Bool-indexed transition cocycle, glue compatible local sections by Mathlib, and turn a
top-open section into compatible sections by actual restriction. The helper definition
contains no data or proof hole and chooses no witness from a mere existence theorem.

Added proof-only imports of `Sheaf.AlgebraicGeometry.NonvanishingGeneratingLocus` and
`Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing`. Updated the existing node
`lem-sc-reciprocal-cover-line-bundle` so its three proof steps and dependencies follow
the compiled implementation. The curve-estimate unit route is unchanged.

Local compilation through lcompile.py succeeds without errors or warnings. The proof
checks all eight Bool-indexed cocycle cases. It does not require inhabited charts,
integrality, separatedness, or affine opens; empty charts and the empty scheme are
covered by the same proof.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_line_bundle_sections_of_reciprocal_cover`
(node `lem-sc-reciprocal-cover-line-bundle`). No sorry remains in the delivered module,
and no hole or new module was added. This is a complete proof from existing stated
results, not a decomposition into new holes.

The existing imported theorem `AlgebraicGeometry.exists_invertible_of_cech_transition`
(node `lem-sc-glue-component-transition-cocycle`) remains an upstream sorry dependency;
this delivery does not prove or change it. The nonvanishing/local-generation criterion
already has a complete proof in the library. All four new private helpers are proved;
`sectionOfTop` is an actual restriction construction.

## No longer needed

Removed the proof-only import `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
the unchanged public import of `Sheaf.AlgebraicGeometry.Ample` already provides it.
Its definitions remain needed by the statement and proof, so no mathematical node or
module is claimed as pruned from the target closure. The redundant public import
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` was removed during second reading:
`Ample` already publicly imports it through `Modules.Invertible`, the source's
`Mathlib.AlgebraicGeometry.Modules.Sheaf`, and its sheaf-generators module, so the
same declarations remain publicly available. No planned mathematical step was bypassed.
The old proof-dependency nodes `def-sc-invertible-module` and
`def-weil-pbc-ample-invertible-module` are no longer direct proof steps: the proof
uses the existing generation criterion instead. Both remain statement dependencies
and are supplied by `Ample`; neither module is pruned from the target closure. The direct stalk calculation is replaced by the existing proved
`lem-sc-nonvanishing-iff-generates-at` and local coefficient criterion in
`def-sc-section-generating-locus`.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The original DAG called for the stalk calculation directly;
the library already proves the required nonvanishing criterion, so this proof reuses
it. The supplied plan is otherwise implemented. The source is Stacks Varieties 09NB,
read in the locally available Stacks source at `lemma-find-globally-generated`.


## Second reading by J2

1. Compared the delivered Lean module against the repository with `diff`, then
   checked the original theorem signature and complete docstring byte for byte.
   Verdict: unchanged; no definition or existing declaration interface was edited.
   The only added declarations are four private, fully implemented helpers.

2. Compiled the delivered file and a scratch copy with `#print axioms` for all five
   declarations through `lcompile.py`. Verdict: clean compilation. The pair-gluing
   theorem, actual restriction construction `sectionOfTop`, and its top-evaluation
   theorem use only `propext`, `Classical.choice`, `Quot.sound`. The frame-gluing
   helper and main theorem additionally use `sorryAx` through the existing open
   Cech gluing theorem. There is no new sorry, forbidden declaration, hollow
   definition, or arbitrary witness chosen into a definition. The frame witness is
   used within a theorem proof; global section gluing is proved by Mathlib.

3. No statement is split off and no new public statement or node is introduced.
   Verdict: no disguised restatement. Checked the eight transition cases and four
   pair-compatibility cases; empty charts, the empty scheme, and coinciding charts
   need no extra hypotheses. The inverse transition has the correct orientation.

4. Read the proof from the target downward, the imported gluing and generation
   results, and the curve-estimate unit's `realized` record. Searched local Lean
   and Mathlib for alternative section/gluing constructions and used a fresh
   LeanFinder query about inverse transition units and prescribed sections.
   Verdict: the results confirm the Mathlib gluing theorem already used; no
   shorter proved replacement for the line-bundle gluing step was found. The unit
   route remains intact. Removed one redundant public import, whose whole public
   import closure is already provided by `Ample`. Completed the pruning report
   with both removed old direct proof-dependency nodes, distinguishing them from
   their continuing role as statement dependencies.

5. Compared the old and delivered JSON nodes. Verdict: only `proof`, `proof_deps`,
   and `proof_origin` differ. The proof-dependency set is exactly the union of the
   steps' `uses`; the descriptions match the Bool cocycle, Mathlib gluing, actual
   restriction family, and generation-locus argument. No new nodes need review.

Second-reading changes: removed the redundant public Mathlib generators import;
corrected the report's import-preservation claim and completed `No longer needed`.
No mathematical proof repair was necessary. One original hole is closed, zero
holes added; the main theorem still depends on the explicitly reported upstream
open Cech theorem and is not yet axiom-clean in the whole import closure.

Change record: `coord/changes/reciprocal_cover_generators_import.md` records the
redundant public import removal and unchanged downstream public closure.
