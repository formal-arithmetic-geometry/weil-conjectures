## What changed

Replaced the sorry in `AlgebraicGeometry.derivedTensor_cohomology_over_affine` with a
complete Lean proof from the affine module representatives, the core affine derived
QCoh equivalence, the K-flat tensor counit comparison, and exact homology comparisons.
The statement, binders, universes, visibility, and existing docstring are unchanged.
The proof constructs a specified functorial K-flat resolution of the first module
complex; it does not introduce any definition choosing an arbitrary witness from
an unproved existence theorem.

Added two separate modules for the missing comparisons:
`Sheaf.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses` and
`Sheaf.AlgebraicGeometry.AffineDerivedTensorChartComparison`.
They have no quasi-coherence hypotheses or conclusions. The first handles restriction
of arbitrary derived tensors to an open with an independent localization universe;
the second computes tensor on specified affine module representatives and a specified
K-flat module resolution. The main theorem combines these with the independent
cohomology calculation and transfer through exact restriction.

Updated the original DAG proof and its proof dependencies to follow the Lean argument.
Added the two matching nodes. All new proof imports in the original module are private
imports; its existing public imports remain unchanged. No other existing module is adapted.

On resuming the earlier attempt, checked the signatures, sources, unit route, and DAG
proof-dependency unions. The original signature is unchanged. Cached the affine-site
sheafification and abelian instances, and the exact open-restriction instances, locally
in the proof to avoid repeated instance synthesis. Profiling located the expensive
quasi-coherence site-instance synthesis; no existing definition or interface was changed.
Removed the earlier attempt's added namespace commands; exactness and additivity are
now supplied explicitly within the proof. The interface checker reports no changes to
the original module. The final main module compiled without errors or warnings in
40.3 seconds.
Both new modules also compiled independently. The final validation is the required
`deliver3.py --no-push`, including the project's axiom probe and preflight.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.derivedTensor_cohomology_over_affine`
(node `lem-pc-derived-tensor-qcoh-component`). No sorry remains in the item's module.

Added two holes, each the entire proof of one public named theorem in its own module:

- `AlgebraicGeometry.derivedTensor_openRestriction_iso_universes`
  (node `lem-pc-derived-tensor-open-restriction-universes`).
- `AlgebraicGeometry.affine_derivedTensor_chart_comparison`
  (node `lem-pc-affine-derived-tensor-chart-comparison`).

This is a decomposition of one upper hole into two strictly separate comparison steps,
not an axiom-free proof of the target closure: net holes closed minus added is -1 for
this delivery. Existing imported open results are not newly added holes. Both new
statements are true on empty opens/zero rings and zero complexes, and impose no
boundedness condition. The affine comparison quantifies over the given resolution;
it does not assert arbitrary resolutions are equal. The restriction comparison is
valid for all derived objects, regardless of quasi-coherence.

## No longer needed

Removed direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`
  (node `lem-pc-affine-derived-pullback-tensor-tilde`): the original mixed pullback/tensor
  wrapper is unnecessary for this module. The two new comparison nodes use the smaller
  underived tensor, K-flat and tilde totalization ingredients of that calculation.
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`
  (node `lem-pc-affine-qcoh-derived-equivalence`): the full equivalence with its shift
  clause is unnecessary here. The core equivalence's tilde comparison suffices;
  `new-affine-qcoh-derived-equivalence-core` remains used.

The second reading also removed the unused direct import of
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` from the new affine chart
module. It changed its import of
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` to private and
added the narrower public `Mathlib.AlgebraicGeometry.Modules.Tilde` import, whose
declarations occur in its signature.

These are pruned from this proof's direct dependency list. Other targets or other modules
may still reach them; this report does not claim they are globally unreachable.
The source module's derived-pullback and derived-tensor naturality declarations, its
arbitrary-resolution affine object formulas, and the affine equivalence's shift/unit
clause are not used by the delivered proof. No further direct imports can be removed:
module representatives, exact open QCoh transfer, K-flat resolution construction,
the generic K-flat tensor comparison, the core affine equivalence, and both new
comparison modules each provide an explicitly used declaration or required instance.

## Where the brief, the DAG or earlier work was wrong

The original node's single paragraph conceals two interfaces that the existing signatures
do not supply directly. Its existing tensor open-restriction statement requires the same
localization universe on X and its open subscheme. The original theorem supplies only
an arbitrary localization on X, whereas standard localizations on the open have their
own universe. The new restriction comparison explicitly allows independent universes.
The affine tensor formula is written on an actual spectrum, whereas an arbitrary affine
open is its open-subscheme object. The new chart computation handles the canonical
spectrum presentation on specified module complexes. These are missing glue steps,
not disputed mathematics, and neither changes the unit's route.

The attempt to transport the generic spectrum tensor formula through an exact derived
restriction functor exceeded the 60-second limit while comparing its tensor object
expressions. The delivered chart statement instead records the source's concrete
termwise K-flat model calculation. No expensive existing definition was changed, no
file was split to evade the compiler limit, and no existing module was adapted.

LeanSearch returned Internal Server Error; LeanFinder/Loogle and textual searches found
underived tensor/locality tools and the existing same-universe comparison, but no exact
independent-universe or specified affine-chart comparison. The source argument was
checked against Stacks Tags 08DX and 08DV online because the listed Stacks TeX files are
not present in this checkout. No mathematical error or statement dispute was found.

## New nodes

`lem-pc-derived-tensor-open-restriction-universes`, in
`dag/nodes/sec-picard-framework/lem-pc-derived-tensor-open-restriction-universes.json`,
records the restriction comparison for arbitrary derived objects. Its module is
`lean/Sheaf/AlgebraicGeometry/DerivedTensorOpenRestrictionUniverses.lean`.

`lem-pc-affine-derived-tensor-chart-comparison`, in
`dag/nodes/sec-picard-framework/lem-pc-affine-derived-tensor-chart-comparison.json`,
records the affine K-flat module computation through the canonical spectrum chart.
Its module is `lean/Sheaf/AlgebraicGeometry/AffineDerivedTensorChartComparison.lean`.

Both inherit the original node's chapter and unit and carry source-based proof steps,
search records, and exact Lean signatures. No interface change record is needed for
an existing declaration: none of their signatures or definitions was changed.

## Second reading by T2

1. **Unchanged interfaces: pass.** Compared each sandbox module with the repository;
   only the main module previously exists. Its complete theorem signature is byte
   for byte unchanged, checked separately by extraction. Its public imports and
   local monoidal definition are unchanged. No change record is needed.

2. **Proof and axioms: pass with reported holes.** Compiled all three modules with
   lcompile in import order, without errors or warnings. Compiled scratch copies
   with #print axioms for all three theorem declarations: each shows only propext,
   Classical.choice, Quot.sound and sorryAx. The last is expected from the named
   open comparisons and imported open results. The main module has no sorry;
   the two new modules each have precisely one public named theorem with sorry.
   No prohibited declarations or hollow definitions were added. Module-complex
   witnesses are eliminated inside a proposition proof, not used to define data.
   The resolution is the existing functorial resolution construction.

3. **Split statements: pass.** Read both comparisons and their docstring arguments
   against Stacks Tags 08DX and 08DV. For empty opens and zero rings the relevant
   module categories are trivial; zero complexes compute zero tensors. For a
   nonzero affine ring the given quasi-isomorphism from the K-flat complex computes
   the first factor, with no boundedness assumption. Exact open restriction
   preserves the total tensor calculation for arbitrary derived objects. Neither
   statement assumes or concludes quasi-coherence, so neither restates the item.
   Repeated searches with different wording using LeanFinder (strong monoidal exact
   restriction), Loogle (Functor.mapDerivedCategory), msearch grep, and rg in both
   library roots. Found underived tensor tools and the existing same-universe
   comparison, but no exact independent-universe or affine-chart comparison.
   Loogle did not recognize the qualified query identifier. No short existing
   proof closes either new hole; the missing totalization/derived transport work
   remains precisely the documented comparison steps.

4. **Top-down route and pruning: pass after import cleanup.** Traced the main proof
   from the target through exact open restriction, the two affine representatives,
   the given K-flat resolution, chart tensor comparison, and core affine equivalence.
   All direct proof imports supply used declarations or instances. Both old DAG
   proof dependencies are accounted for under No longer needed. Read the unit's
   realized fields (empty statement and step lists); no realized node is bypassed
   and no unit record or chapter route changes. The proof keeps the source's
   affine-local route. This closes one upper hole and adds two smaller holes,
   a decomposition with net -1, not a proof of the target import closure.

5. **DAG agrees with Lean: pass.** Compared the original node's changes: only proof,
   proof_deps and proof_origin change. Verified all three proof_deps sets equal
   the unions of their proof-step uses. New nodes contain source, searches,
   creation provenance, blueprint origin, inherited chapter and unit, and Lean
   signatures matching the actual declarations.

Changes during second reading: removed the unused ExactFunctor import from the new
AffineDerivedTensorChartComparison module; made its broad QuasicoherentKernel
import private and supplied the narrow public Tilde import needed by the signature.
The repaired module compiles. Added a direct private QuasicoherentKernel import to the main module, which uses
its exact restriction instances and previously received them through the chart
module. The dry run caught this visibility dependency after rebuilding the imports.
No theorem statement or proof body changed. Added
this review and recorded the import cleanup above. The required delivery dry run
and full axiom probe are the final checks.
