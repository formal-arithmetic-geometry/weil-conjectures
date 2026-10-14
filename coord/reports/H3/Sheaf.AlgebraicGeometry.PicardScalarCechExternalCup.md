## What changed

Repaired and proved `AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup_core`
in `lean/Sheaf/AlgebraicGeometry/PicardScalarCechExternalCup.lean`, using the complete direct
ordinary-pairing proof supplied in the ROUTE sandbox. The core now has the missing
`hUc : iSup U = ⊤` and `hVc : iSup V = ⊤` hypotheses. Its sole caller,
`picardScalarCech_externalCup`, passes its existing hypotheses; that enclosing theorem's
signature, universe, visibility, hypotheses and conclusion are unchanged. No definition or
Challenge target changes.

The proof substitutes the natural-degree equality, forms the bidegree component of `c`,
and obtains its image cycle through `HomologicalComplex.cyclesMap`. Mathlib's
`cyclesMap_i` and `homologyπ_naturality` compute its inclusion and class. The scalar
comparison witnesses yield ordinary comparison maps. The uniquely characterized ordinary
module cup and `picardModuleCech_externalPairing` identify the image class with the ordinary
cup of the projection pullbacks. Substituting the three witness equations and applying
`scalarExternalCup_moduleComparison` yields precisely the scalar external cup in the goal.
This is the covering refinement and cup comparison route of
[Stacks 01FD](https://stacks.math.columbia.edu/tag/01FD) and
[Stacks 0FKV](https://stacks.math.columbia.edu/tag/0FKV).

Added four proof-only imports: `PicardExternalCechCupBidegree`,
`PicardModuleCechExternalPairing`, `ScalarExternalCupModuleComparison` and
`Sheaf.Paper.ModuleCohomologyCupProduct`. Both original public imports remain public.
Kept the tested local irreducibility attributes and transparency settings, plus a proved
private `moduleCup_congr`, so equality glue does not unfold large derived constructions.
No other module is adapted.

Updated the two existing DAG nodes' proof routes and dependencies. The core's node also
records the corrected statement, verbatim Lean signature and `statement_change`.
The outer node now depends directly on the corrected core. The blueprint unit
`sk-prop-av-cube` and its realized route are unchanged; these below-unit comparison helpers
use the same refinement, ordinary cup and scalar identification operations.

Change record: `coord/changes/picard-scalar-cech-external-cup-cover-repair-H3.md`.
It lists every transitive importer and the current server claim holders; only this item's
local caller mentions the changed core.

Searches before proof: LeanFinder returned group-cohomology cycle identities rather than
this project-specific assertion; Loogle found Mathlib's `homologyπ_naturality`; Mathlib grep
for Čech cup compatibility returned no match. Project searches found the ordinary pairing
and scalar/module bridge used here. No new intermediate theory was stated.

## Proved and sorry left

Closed the item's one local hole:
`AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup_core`
(node `lem-sc-picard-scalar-cech-external-cup-core`). This is a proof from existing named
library declarations after repairing its false below-unit signature, not a new split.
The existing public `AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup`
(node `lem-sc-picard-scalar-cech-external-cup`) now applies the repaired proof with its
cover hypotheses.

Local holes before: 1. Local holes after: 0. Holes added: 0. Split off: 0.
No `sorry` is left in any delivered Lean declaration. No new module or node is added.
The imported ordinary/scalar compatibility theory still has existing unfinished proofs;
therefore the transitive axiom set can still contain `sorryAx`. This delivery does not claim
the Challenge targets or the whole import closure are axiom-free.

Validation: the repaired item compiled cleanly through `lcompile.py` in 11.6 seconds.
The enclosing theorem's textual signature was checked identical to the original, and the
core's only signature change was checked to be the two cover binders. The direct importer
`PicardRightCechCupCycleComparison` compiled unchanged against the sandbox replacement
in 22.4 seconds (the replacement compiled in 12.0 seconds in that set).
`deliver3.py H3 Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup --no-push` printed
`OK (dry run)`: compile and preflight passed except for the reserved second-reading
section, which the independent second reader writes. Nothing was pushed.

## No longer needed

Removed proof import `Sheaf.Paper.CechCupPullbackCompat` and its direct route node
`lem-sc-picard-cech-cup-pullback-compat`. The ordinary pairing and the scalar/module bridge
replace that combined comparison in this item. The other old upper proof dependencies
remain available transitively where the direct pairing route actually uses them; moving
those dependencies to the core is not a claim that they disappear globally.

The complete difference of the old and new item import closures in the project's source
import graph is:

| Module leaving this item's source import closure | Attached DAG nodes |
|---|---|
| `Mathlib.CategoryTheory.Adjunction.CompositionIso` | No attached node |
| `Sheaf.AlgebraicGeometry.BasicPropertiesDegreeZero` | `lem-weil-pbc-module-cohomology-fmap-basic-degree-zero` |
| `Sheaf.AlgebraicGeometry.BasicPropertiesIdentity` | `lem-weil-pbc-module-cohomology-fmap-basic-identity` |
| `Sheaf.AlgebraicGeometry.BasicPropertiesLinearity` | `lem-weil-pbc-module-cohomology-fmap-basic-linearity` |
| `Sheaf.AlgebraicGeometry.BasicPropertiesRestriction` | `lem-weil-pbc-module-cohomology-fmap-basic-restriction` |
| `Sheaf.AlgebraicGeometry.EtaleTensorSections` | `lem-sc-etale-qcoherent-presheaf-functorial` |
| `Sheaf.AlgebraicGeometry.IdentityResolutionHomology` | `lem-weil-pbc-module-cohomology-fmap-identity-resolution-homology` |
| `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties` | `lem-weil-pbc-module-cohomology-fmap-basic-properties` |
| `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapCompData` | `lem-weil-pbc-module-cohomology-fmap-comp-data` |
| `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapComparison` | `lem-weil-pbc-module-cohomology-fmap-comparison` |
| `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapDataLinearity` | `lem-weil-pbc-module-cohomology-fmap-data-linearity` |
| `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial` | `lem-weil-pbc-module-cohomology-fmap-functorial` |
| `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapSemilinear` | `lem-weil-pbc-module-cohomology-fmap-semilinear-lift` |
| `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapZeroAugmentation` | `lem-weil-pbc-module-cohomology-fmap-zero-augmentation` |
| `Sheaf.AlgebraicGeometry.RestrictionNaturality` | `lem-weil-pbc-module-cohomology-fmap-target-iso-naturality` |
| `Sheaf.Paper.CechCupPullbackCompat` | `lem-sc-picard-cech-cup-pullback-compat` |
| `Sheaf.Paper.CechCupResolutionRepresentatives` | `lem-sc-cech-cup-resolution-representatives` |

These are removals from this item's source import path. No module file is deleted and no
claim is made that another target branch cannot still import them. The Mathlib row is a
removed source-graph leaf; this analysis does not traverse Mathlib's own imports.
`PicardScalarExternalCocycleComparison` has no live source importer in this checkout and
is not used or introduced. The alternate scalar cocycle comparison split is unnecessary.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the baseline `picardScalarCech_externalCup_core` omitted both cover
hypotheses while quantifying over arbitrary comparison witnesses. The old node explicitly
claimed compatibility without the cover equalities. Those equations only fix restriction
to the union of the opens and do not fix extensions outside it.

Use the route note's corrected mathematical counterexample: `X = Y = P¹_k`, rational
points `x₀,x₁`, and singleton families `U = V = P¹_k \ {x₁}`. For
`F = G = k(x₀) ⊕ k(x₁)`, the global structure ring is `k`. Factor comparisons may extend
`s` as `(s,0)`; the product comparison may extend `s` as `(s,s,s,s)`. Restriction to
`U` or `U × U` satisfies the comparison equations in both cases. The external cup of
factor extensions of `1` is `(1,0,0,0)` and the product extension is `(1,1,1,1)`.
This scheme counterexample is documented mathematically, not fully formalized in Lean.
The previous disjoint `Spec(k × k)` example is invalid because ring-linear comparison
maps must respect the global idempotents.

The repaired signature restores hypotheses assumed by the enclosing theorem and by the
source's open-cover comparisons. It does not weaken any public target or change a
unit's statement. The outer theorem's previously unused cover assumptions now do real
work in the ordinary pairing application. The baseline DAG had no proof/statement citer
of the core (only historical blueprint provenance mentioned it); the outer node now
records that actual proof dependency.

## Second reading by H3

1. **Visible declarations and statements.** I compared the delivered module with the
repository version. The public theorem `picardScalarCech_externalCup` has the same
binders, hypotheses, universe, visibility, and conclusion; its proof now supplies the
two already-present cover hypotheses to the core. The core is the sole intentional
signature change, adding `hUc : iSup U = ⊤` and `hVc : iSup V = ⊤`, and the change record
and node `statement_change` identify this correction. Verdict: no accidental target or
consumer statement change.

2. **Compilation and proof hygiene.** I compiled the item alone and with all sandbox
modules using `lcompile.py`; both passed without warnings or errors. The delivered file
contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or
`debug.skipKernelTC`. The private bilinear-congruence helper is proved directly, and
the proof uses only existing declarations for the Cech bidegree, ordinary module
pairing, and scalar/module comparison. Verdict: proof and hygiene checks pass.

3. **Truth and strength of the repaired statement.** The core's added cover equalities
are required by `picardModuleCech_externalPairing` and by the open-cover comparison
theory. Without them, comparison witnesses can agree on the listed opens while
choosing different extensions outside their union, so the former helper was false. The
P¹ counterexample in the report tests this edge case; empty and zero cases remain
covered by the unchanged quantified conclusion. Verdict: the corrected helper is true
and has exactly the assumptions used by the route; no new split statement was added.

4. **DAG, imports, and pruning.** The core and outer node proof steps and
`proof_deps` match the Lean proof: the route goes through `cyclesMap` naturality, the
ordinary module external pairing, and `scalarExternalCup_moduleComparison`. The removed
pullback-compatibility import and node are listed under `## No longer needed`; the four
new proof-only imports are plain `import`, while the two statement imports remain
public. The unit record and its realized route are unchanged. Verdict: DAG metadata and
pruning agree with the implementation.

5. **Axiom and downstream checks.** The direct importer
`PicardRightCechCupCycleComparison` compiled unchanged against the replacement. The
change record lists all 174 downstream importers and identifies the item's sole textual
user of the changed core; no forced adaptation is needed. Existing imported unfinished
theorems may contribute `sorryAx`, as reported, but this delivery introduces none.
Verdict: downstream and axiom-scope checks pass.

I changed only this report section after the first worker's delivery; no Lean code,
node, or change record required repair.
