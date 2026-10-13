## What changed

Repaired both duplicate-proof findings without changing any existing public signature.
Removed the private `unit_stalk_iso` and `pushforward_restrict_iso` helpers from
`Sheaf.AlgebraicGeometry.BirationalLinePushforwardGenericStalk`.
Added proof-only `import all Sheaf.AlgebraicGeometry.IdealModuleProductStalk`
and reused `AlgebraicGeometry.Scheme.unit_stalk_iso`.
Added proof-only `import all WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`
and specialized its existing `pushforward_restrict_square` to the canonical
open-restriction pullback square. Its component replaces the duplicate comparison.
Updated the node's first proof step, dependencies and proof origin accordingly.
No other library module was changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.birational_line_pushforward_generic_stalk`
(node `lem-pc-q2-birational-line-pushforward-generic-stalk`).
No sorries remain or are added; zero statements split off.
The three remaining private helpers are fully proved:
`stalk_bijective_of_restrict_iso`, `stalk_free_of_restrict_iso`, and
`line_pushforward_stalk_on_iso_open`.
Local compilation passed without warnings. A fresh `#print axioms` probe of the
public theorem returned exactly `propext`, `Classical.choice`, and `Quot.sound`.
The reused comparisons introduce no transitive `sorryAx`.
The repaired delivery dry run printed OK (commit `90caa6ab95`); nothing was pushed.
The fresh independent second reading is recorded below.

## No longer needed

The two duplicate local comparisons are removed; their existing library proofs
are reused. No original imports or original DAG dependencies were removed.
`Sheaf.AlgebraicGeometry.PushforwardRankOnOpen` is not imported: it already
reaches this item and would create an import cycle. The general underived
comparison in `DirectImage.Sections` supplies the needed specialization.
No new modules or nodes are needed. As before, the component-product
`Sheaf.AlgebraicGeometry.FunctionField` and explicit
`Sheaf.AlgebraicGeometry.TensorPullback` modules are not imported: Mathlib's
generic local field instance and existing restriction/pullback interfaces suffice.
This does not claim that these modules leave the targets' closure globally.

## Where the brief, the DAG or earlier work was wrong

The returned delivery reproved two comparisons already present privately in the
library. Both findings are repaired by importing and using existing declarations.
For the pushforward comparison, the exact duplicate's module cannot be imported
without a cycle; the more general existing cartesian-square comparison is used.
`isPullback_morphismRestrict` needs `.flip` to match that comparison's orientation.
Proof-only `import all` exposes the private existing comparisons locally without
changing what this module's importers see.

No mathematical error or statement change was needed. The original three-step
route and the unit's realized steps remain. The local line-stalk argument needs
neither density nor integrality; these enter at the generic-point specialization.
An empty open has no point satisfying membership, and the closed stalk map is
used only surjectively, never injectively. The source remains Stacks coherent.tex,
Tag 02O5, proposition-proper-pushforward-coherent, property (a).
The old second reading predates this repair and was removed so that the designated
second reader can record a fresh independent review.

## Second reading by Q2

1. PASS: Compared the sole delivered module and node with the repository using
   diff. The existing public theorem signature is byte for byte identical,
   verified separately by extracting its text before `:= by`. No definition,
   visibility, original public import, target, or other module changes. No change
   record is required.
2. PASS: Compiled the repaired module locally through lcompile.py without errors
   or warnings. Regenerated scratchpad/AxiomReview.lean from the current source
   and printed axioms for all three private helpers and the public theorem:
   each uses exactly propext, Classical.choice, and Quot.sound. No sorry or
   forbidden declaration occurs, and no data comes from an unproved existence.
3. PASS: Zero statements split off, zero holes added, one original hole closed.
   Read the helpers and the reused comparisons. The local assertion is vacuous
   on an empty open, and density on an integral scheme puts its generic point
   in U. The closed immersion stalk map is used surjectively; the injectivity
   needed for residue equivalences comes from field homomorphisms. No assumption
   on properness or Noetherianity is introduced. Searched the library with rg
   for restriction-stalk, unit-stalk, invertible-stalk, and pushforward comparisons,
   and repeated Mathlib searches via msearch.py with alternate queries.
4. PASS after repair: Found upstream bijective_stalk_of_isIso_restrict and replaced
   the local stalk-conjugation proof with its application on j.opensRange, using
   restriction composition along j.isoOpensRange.inv. The generalized helper now
   only transports to the existing lemma. Added its proof-only import. The other
   comparisons already reuse existing declarations. The remaining helpers retain
   the necessary ambient-ring linearity. No original proof dependency or import
   is pruned; No longer needed is complete. Read sk-thm-picard-coherence.json:
   its realized fields are unchanged; this node-level local-stalk argument does
   not replace any step of the unit's coherence proof.
5. PASS after repair: The node retains its statement and Lean record. Its three
   proof steps follow the restriction/trivialization, closed-stalk and generic
   field, and residue-naturality argument actually compiled. Updated step one,
   proof_deps, and proof_origin to record the additional existing restriction-stalk
   lemma. The dependency list is exactly the union of the steps' uses. No new
   node is required.

Second reading changed only the proof of stalk_bijective_of_restrict_iso, added
proof-only import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf, updated
its existing node's proof route, and recorded this review. No signatures changed.
The imported source-library lemma is a proved tool, used below the unit level.
