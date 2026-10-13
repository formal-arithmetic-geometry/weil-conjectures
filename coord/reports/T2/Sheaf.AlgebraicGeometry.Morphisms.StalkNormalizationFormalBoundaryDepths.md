## What changed

Completed the unchanged theorem
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_formal_boundary_depths`.
Its first bound uses boundary dimension, normality and normal Serre S2, then
transfers depth along the flat pullback projection. Its second bound is proved
from the existing coefficient-flatness theorem: minimality and the base equation
identify the boundary with points over the closed base point, and two applications
of flat depth monotonicity handle the formal spectrum and its coproduct.
A proved private helper `depth_le_of_flat_stalk` packages this monotonicity.
No heartbeat override is needed. Both files compile cleanly through lcompile.py.

Added one strictly smaller intermediate theorem in
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwo`:
only the dimension bound on the original normalization, before formal base change.
It has no formal test, variables, group, coproduct or depth conclusion.
Its source, complete affine going-down proof and DAG node are supplied.
This is a decomposition, not an axiom-free proof of the entire import closure.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_formal_boundary_depths`
(node `lem-sbc-stalk-normalization-formal-boundary-depths`).
No sorry remains in the assigned module. The private flat-stalk helper is proved.

Added one hole:
`AlgebraicGeometry.Scheme.stalk_normalization_boundary_dimension_two`
(node `lem-sbc-stalk-normalization-boundary-dimension-two`), in its own new module.
Net holes closed minus holes added: zero; one upper theorem decomposed, with
both formal depth transports and the entire coproduct argument now complete.
The new theorem's edge cases were checked: empty cover or empty C gives a vacuous
source assertion; disconnected smooth C is handled componentwise; U need not
contain every generic point, since only components supporting the cover occur.
Neither d=0 nor an empty G is excluded in the original theorem.

## No longer needed

Removed the assigned module's direct import of
`Mathlib.RingTheory.IntegralClosure.GoingDown`: the dimension lemma owns that step.
Replaced its import of
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationNormalDense` with the proved
normality-only module `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationNormalPart`.
The assigned theorem does not use density, so its direct proof dependency
`lem-sbc-stalk-normalization-normal-dense` is replaced by
`lem-sbc-stalk-normalization-normal-part`.

The other removed direct proof dependency is
`lem-weil-pbc-going-down-normal-integral`; it moves to the dimension lemma.

Neither going down nor density is globally pruned: both remain dependencies of
`lem-sbc-stalk-normalization-boundary-dimension-two`. No module is claimed to be
removed from the targets' closure. All other original imports are retained because
they support the unchanged signature or the written proof.

## Where the brief, the DAG or earlier work was wrong

The planned boundary-dimension/going-down step has no separately usable scheme
statement. The ring-level going-down and depth results do not directly give it:
one must pass to finite normal affine components dominating the smooth target and
lift strict prime chains. That step is now explicitly isolated with its proof.
No existing statement, definition or target signature was changed, and no forced
adaptations were needed. The unit route through depth-two extension is retained.

LeanSearch was unavailable (Internal Server Error). LeanFinder, Loogle and grep
were used: the ring height formula and normalization integrality declarations
were found, but no assembled boundary-dimension theorem. The existing proved
`MvPowerSeries.constants_flat` supplies the coefficient-flatness step.
Stacks Tags 0EYJ, 0337 and 00H8 were read online because the local literature clone
is absent on this machine; the sources corroborate the flat-depth and going-down
arguments recorded in the new node.

## New nodes

`lem-sbc-stalk-normalization-boundary-dimension-two` states only the dimension bound
on boundary stalks of the finite localized relative normalization. It is realized
by `AlgebraicGeometry.Scheme.stalk_normalization_boundary_dimension_two` in
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwo`.
Its proof separates closed-fibre identification and target depth/dimension from
affine normal-component domination and going-down chain lifting. The original
node is updated to the actual Lean assembly. No change record is needed.

## Second reading by T2

1. Compared both delivered modules with the repository: the dimension module is
   new; the original theorem signature and docstring are byte-for-byte unchanged.
   No existing definition, visibility or public import changed. Verdict: pass.
2. Compiled both modules in import order using lcompile.py, with no warnings or
   errors. Scanned for forbidden declarations and hollow definitions: none.
   In a scratch copy, #print axioms reports only propext, Classical.choice and
   Quot.sound for depth_le_of_flat_stalk; the main theorem and new dimension
   theorem additionally use sorryAx. The only delivered sorry is the named new
   dimension theorem. Verdict: valid decomposition, not a closed import closure.
3. Checked the new dimension statement and its affine proof against Stacks
   Tags [0EYJ](https://stacks.math.columbia.edu/tag/0EYJ),
   [0337](https://stacks.math.columbia.edu/tag/0337) and
   [00H8](https://stacks.math.columbia.edu/tag/00H8). Normal Noetherian affine
   components are domains; on the dense cover open, finite etaleness makes each
   source generic point map to a target generic point. Thus the finite component
   ring map is injective and integral, and going down lifts two strict inclusions
   below any boundary prime. Empty covers and empty C are vacuous; disconnected
   C is handled componentwise, without requiring surjectivity of PA. The formal
   assembly includes d=0 and empty G. Repeated LeanFinder, Loogle and grep searches
   with finite dominant morphisms, stalk dimension, coheight and going down:
   found normalization instances and ring-level height tools, no exact existing
   dimension theorem. The new lemma has no formal test or coproduct and asserts
   only the needed pre-base-change dimension bound. Verdict: true, strictly
   smaller, with a complete sourced proof and matching node; no quick closure.
4. Read the proof from its conclusion downward. Its normal S2 and flat-depth
   route is direct; the coproduct fold argument avoids unnecessary identification
   of individual summand stalks. Checked imports against the signature and proof;
   the new open lemma retains imports of its planned dependencies. Compared all
   old proof_deps with the new set and completed No longer needed with the
   explicit going-down node name. Read sk-prop-input-spreading.json: its depth-two
   extension and formal computation route is retained, without bypassing a unit.
   Its pre-existing realized statement and step arrays are empty; this delivery
   does not alter them or claim to populate those mappings. Verdict: pass, with
   that existing unit bookkeeping limitation recorded.
5. Checked both nodes: proof_deps equals the union of uses, every dependency
   exists, and each lean.statement matches its theorem signature. The new node
   has source, proof_origin, searches, creation, blueprint, chapter, unit and
   Lean fields. Existing node changes describe the actual dimension/S2 and two
   flat transports. Verdict: pass.

Second reading changed only this report: completed the list of removed direct
proof dependencies and recorded independent compilation, axiom, edge-case,
search and unit-route checks. No Lean or node repair was needed. One original
hole closed and one strictly smaller hole added: net zero, a decomposition.
