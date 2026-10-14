## What changed

Replaced the admission in
`AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup_core` with the
direct ordinary-pairing proof supplied in the audited route note
(`/home/ubuntu/weil-sandbox/ROUTE/picard-root-scalar-20261014/`). It forms the
bidegree component of c, computes the image cycle using cyclesMap_i, identifies
its class by homologyπ_naturality, extracts the three ordinary comparison
witnesses, applies picardModuleCech_externalPairing, and identifies the resulting
module cup with the scalar external cup by scalarExternalCup_moduleComparison.
The private moduleCup_congr helper only rewrites equal inputs. Local
irreducibility keeps the derived cohomology and tensor-pullback implementations
folded during equality glue.

Restored `hUc : iSup U = ⊤` and `hVc : iSup V = ⊤` in the below-unit core
helper. Its only call now passes those hypotheses. The enclosing
picardScalarCech_externalCup signature is byte-for-byte unchanged. The core's
only signature difference is that one added line. No definition, Challenge
target, or universe changes. Both existing nodes now describe the actual proof;
the core records its corrected statement, verbatim Lean signature, and
statement_change. The change record is
`coord/changes/picardScalarCech_externalCup_core-covers.md`.

Removed the direct proof imports Sheaf.Paper.CechCupPullbackCompat and
Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations. Added proof-only
imports PicardExternalCechCupBidegree, PicardModuleCechExternalPairing, and
ScalarExternalCupModuleComparison. Both public imports stay. The second reader
removed the redundant added direct import Sheaf.Paper.ModuleCohomologyCupProduct:
the public import chain PicardExternalCechCupComponent → CechCupProduct already
supplies it. Its cup characterization is still used and stays a proof dependency.

The first worker also supplied a support-module instance-name repair. During
second reading, the repository refreshed to Q4's independently landed equivalent
repair, recorded in coord/changes/Q4-module-cup-compatibility-instance-names.md
(landing 20261014T115943-L-2408458). The second reader removed the duplicate
ModuleCupNaiveDerivedCompatibility edit and its change record. This delivery
changes only the assigned Lean module, its two existing nodes, the core change
record, and this report. No held or unclaimed support module is adapted.

Short-route checks: the worker's leanfinder search found unrelated group
cohomology coordinate lemmas; loogle found homologyπ_naturality, which is used.
The second reader searched with the different query “cohomology map class of
image cycle naturality tensor bilinear pairing comparison”; again no replacement
for this project-specific compatibility theorem appeared. Loogle confirmed
HomologicalComplex.cyclesMap_i. Mathlib grep found no external-pairing bridge;
whole-library rg found the existing ordinary pairing, scalar/module bridge,
core and wrapper. No new intermediate obligation was necessary.

## Proved and sorry left

Original local hole removed after its declared statement repair:
AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup_core
(node lem-sc-picard-scalar-cech-external-cup-core). The corrected core has a
complete Lean proof from existing declarations. The original uncovered statement
is not claimed proved. The enclosing picardScalarCech_externalCup remains proved
and applies that corrected core with its existing cover hypotheses.

Holes added: none. Sorries left in delivered Lean: none. Split-offs: none.
The equality-congruence helper is proved. The cup witness is used inside a
proof and has an exists-unique characterization; no data definition chooses an
arbitrary witness from an unproved existence result. This is a statement repair
with a completed local proof, not a decomposition or a fully closed transitive
target proof. Both scalar declarations print only propext, Classical.choice,
Quot.sound and inherited sorryAx from unfinished imported theory.

Second-reader validation uses only lcompile.py and its unchanged 60-second
per-file limit. The final item, after redundant-import removal, compiles without
warnings in 11.9 seconds. Its unchanged direct consumer
PicardRightCechCupCycleComparison compiles against the final artifact in 20.8
seconds; that test copy and its artifacts were removed from the delivery set.
The ordinary-import scratch probe prints both axiom lists successfully in 2.2
seconds. While the published artifacts still had the old collision, Q4's
unchanged landed support source was compiled in the sandbox overlay in 36.5
seconds solely for validation; that source is not part of this delivery. All
delivered Lean lines satisfy the 100-character limit.

## No longer needed

Removed old direct proof imports: Sheaf.Paper.CechCupPullbackCompat and
Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations. Removed redundant
new direct import: Sheaf.Paper.ModuleCohomologyCupProduct, still reached through
public statement imports and still used mathematically.

The core's old proof edges no longer needed are
lem-sc-picard-cech-cup-pullback-compat and
def-sc-field-linear-module-cohomology-operations. Scalar vocabulary still comes
through the statement imports. The wrapper now has only the core as its direct
proof dependency. All seven old wrapper proof edges are replaced by that edge:
def-sc-cech-cup-product, def-sc-cech-refinement-cochain-map,
def-sc-field-linear-module-cohomology-operations,
def-sc-module-cohomology-cup-product, lem-sc-picard-cech-cup-pullback-compat,
lem-sc-picard-external-cech-cup-component, and
lem-sc-picard-scalar-cech-comparison. The core retains the component and scalar
comparison, and uses the ordinary pairing and cup characterization. The ordinary
pairing retains its own refinement and cup theory.

These are removed redundant direct edges, not assertions that their modules are
globally unreachable. No existing module is withdrawn. The competing
PicardScalarExternalCocycleComparison split is not imported or recreated. The
unit sk-prop-av-cube and its realized record stay unchanged; this below-unit
route does not bypass a realized unit statement or step. No new nodes exist.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (old core, repaired here): omitting both cover equalities left
comparison extensions outside the union unconstrained. IsModuleCechComparison
specifies the composite with the resolution-to-Cech-total map, not a unique
extension when the opens fail to cover. The ordinary pairing theorem explicitly
requires both covers. The supplied corrected G3 example uses X=Y=P¹_k with two
rational points x₀,x₁, U=V=P¹_k minus x₁, and F=G=k(x₀)⊕k(x₁). Global structure
rings are k; the factor extensions s↦(s,0) and product extension s↦(s,s,s,s) are
linear and have the required visible restrictions. At degree zero the factor
cup of 1 is (1,0,0,0), whereas the product extension is (1,1,1,1). This is a
source-level geometric counterexample, not a formal Lean scheme counterexample.
The earlier disjoint Spec(k×k) example was invalid because idempotents constrain
linearity. The complete Lean proof checks the repaired statement.

The original planned direct Cech/Ext glue is replaced by the existing ordinary
pairing and scalar/module bridge. No lower hole is introduced. The first
worker's support repair was necessary for the older shared artifacts, but Q4
landed the same repair during review. Retaining V2's differently named copy would
needlessly replace Q4's helper names, so the second reader removed it and its
obsolete change record. The sandbox validation uses Q4's identical current
source while awaiting artifact refresh.

## Second reading by V2

1. Compared every delivered module to the refreshed repository and checked raw
   theorem signatures. The wrapper is byte-for-byte unchanged. Removing only the
   recorded cover-hypothesis line from the core gives its old signature exactly.
   The core is below the unit level and has only the wrapper as a source caller;
   that call supplies the already assumed covers. The change record covers it.
   No target or definition changes. The support edit was name-only, but became
   redundant after Q4 landed, so it is excluded. Verdict: pass.
2. Read the proof line by line and compiled the final item and unchanged direct
   consumer. cyclesMap_i gives exactly the image-cycle inclusion, and
   homologyπ_naturality gives exactly its class. The three comparison witness
   equations and the two existing compatibility results compose in the stated
   orientations, with n substituted by p+q to remove the cast. No admission or
   forbidden declaration remains in delivered Lean; ordinary-import axiom
   queries show only the allowed axioms and inherited sorryAx. No data or hollow
   definition was added. Verdict: pass as a local proof, with inherited holes.
3. No statement is split off and no new mathematical node is created. The sole
   new private lemma is equality congruence, proved by rewriting. Checked the
   degree-zero tensor formula, zero coefficients, and empty covers of empty
   schemes: the reduction uses universal ordinary-pairing statements and never
   assumes positive degrees, nonempty index sets, or comparison invertibility.
   The omitted-cover version fails for the reported P¹ example. Searches with
   different wording confirmed the existing direct route rather than a missing
   shorter generic result. Verdict: pass.
4. The proof opens the original core hole and directly combines existing ordinary
   and scalar/module theorems; it does not restate the whole item as a lower hole.
   Each retained proof import supplies an explicitly used declaration. Removed
   the redundant direct ModuleCohomologyCupProduct import and recorded every
   removed old proof edge, including FieldLinearModuleCohomologyOperations.
   Opened dag/units/sk-prop-av-cube.json: neither this helper nor the wrapper is a
   realized unit entry, and no unit record or chapter route is changed. No module
   is claimed globally pruned. Verdict: pass.
5. Opened both node files and compared their proof steps to the Lean reduction.
   Both proof_deps arrays are exactly the unions of steps' uses. The wrapper's
   core edge and the core's six ordinary/scalar/component edges match the code.
   Both verbatim lean.statement records match their source signatures; the core
   statement_change records the old statement and baseline DAG citers (none).
   Changed fields are only the stage-3 proof/lean fields plus the core's declared
   statement and statement_change. No new-node checks are needed. Verdict: pass.

Second-reading changes: removed the redundant direct ModuleCohomologyCupProduct
import; removed the duplicate support-module source and its change record after
Q4's landing; corrected the report's import list, current delivery scope and
validation evidence; added this independent reading. The mathematical proof and
both node files required no further repair.
