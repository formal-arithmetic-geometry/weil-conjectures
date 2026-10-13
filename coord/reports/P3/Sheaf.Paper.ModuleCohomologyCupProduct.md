## What changed

Second reading removed the redundant truncation split and replaced its import
and proof-plan reference by the upstream proved homology bijection. It added
plain proof imports of LongExactSequence and PlusHomology to pairing-exists
for its cited Leray criterion, and removed three redundant imports from the
new compatibility module. No pre-existing signature or definition was changed.


Repaired every numbered point of return X-3869a. The item still reduces
`AlgebraicGeometry.Scheme.Modules.exists_unique_moduleCupProduct` by proved
class-map surjectivity, Leibniz cycle construction, bilinear quotient descent,
resolution invariance and extensional uniqueness. Its original statement and
all pre-existing definition bodies remain unchanged. The four original data
declarations remain verbatim in `ModuleCupResolutionData`, publicly re-exported.

Replaced the generic-category tautology in `ModuleCupNaiveDerivedCompatibility`
with a sourced whole-proof theorem asserting the actual six-object global cup
diagram for arbitrary integer complexes of module sheaves. Its derived cup is
an existential natural family; the naive cochain map is specified on every
summand by `tmulSection`. Comparison arrows are the canonical right-derived
unit transported by `quotientCompQhIso`, and the lax tensor comparisons of Q.
There is no equality hypothesis. Global sections implement the specialization
(X,O_X) → (pt,Γ(X,O_X)); no Spec Z occurs in the repaired node. The theorem uses
the shared sheaf-module category and its recorded tensor structure.

Added `ModuleCupCanonicalHZeroIdentification`, with the real single-tensor
isomorphism and a sourced canonical H-zero theorem. It asserts invertibility
of H-zero of the canonical Q tensor comparison followed by that isomorphism.
It also gives its precise transport through any nonpositive termwise-flat
K-flat resolution: inverse localized resolution tensor identity, recorded
flat-model isomorphism, localized tensor augmentation, then single-tensor
identification. No data is chosen from an unproved existence statement.
The previous H-zero model theorem keeps its signature; its node and docstring
now assert exactly its model calculation rather than canonical transport.

Corrected the Godement existence and flasque-acyclicity node statements to
match their Lean conclusions. Pairing-exists now takes the existential flasque
complexes, and uses the separately cited Leray criterion for computing
comparisons. Recorded the actual Lean proofs of flasque acyclicity and derived
tensor connectivity, with their actual result dependencies. Added all requested
plain proof imports to pairing-exists and resolution-invariance, including the
canonical identification, and cited the latter in invariance step 2.

Repair worker validation before this independent reading: all eleven proposed
modules compiled in dependency order through
lcompile.py without warnings. deliver3.py --no-push then printed
`OK (dry run): commit 0ec26ddc8f compiles and passes the preflight; nothing pushed.`
Review class is CODEX. Its declaration axiom probes passed. The first dry run
found only a missing LeanSearch metadata record and two node IDs missing from
the New nodes section; those are corrected. LeanSearch was unavailable with an
Internal Server Error, recorded as unavailable without a mathematical verdict.
The six original declarations retain their statements and visibility, all
original non-hole bodies are unchanged, node theorem statements are verbatim,
proof_deps match step uses, and all cited nodes exist. No delivery was pushed.

## Proved and sorry left

Closed the one original item hole:
`AlgebraicGeometry.Scheme.Modules.exists_unique_moduleCupProduct`
(`def-sc-module-cohomology-cup-product`). The item and data module have no sorry.

The final delivery adds exactly six whole-proof public theorem holes:

- `AlgebraicGeometry.Scheme.Modules.exists_moduleCupResolutionPairing`
  (`lem-sc-module-cup-pairing-exists`, `ModuleCupPairingExists`).
- `AlgebraicGeometry.Scheme.Modules.moduleCup_resolution_invariance`
  (`lem-sc-module-cup-resolution-invariance`, `ModuleCupResolutionInvariance`).
- `AlgebraicGeometry.Scheme.Modules.moduleCup_godement_pairing`
  (`lem-sc-module-cup-godement-aw`, `ModuleCupGodementPairing`).
- `DerivedCategory.moduleCup_hzero_identification`
  (`lem-sc-module-cup-hzero-identification`, `ModuleCupHZeroIdentification`).
- `AlgebraicGeometry.Scheme.Modules.moduleCup_naive_derived_compatibility`
  (`lem-sc-module-cup-naive-derived-compatibility`,
  `ModuleCupNaiveDerivedCompatibility`).
- `DerivedCategory.moduleCup_canonical_hzero_identification`
  (`lem-sc-module-cup-canonical-hzero-identification`,
  `ModuleCupCanonicalHZeroIdentification`).

The second reader removed the proposed `DerivedCategory.moduleCup_truncation_adjunction`
hole and its module/node because the upstream proved
`DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE` already gives it.
The invariance proof plan now cites that result directly.

The two proved new results are `AlgebraicGeometry.moduleCup_flasque_acyclicity`
and `DerivedCategory.moduleCup_derived_tensor_connectivity`. The latter is the
explicit specialization of upstream `isLE_tensor`. All private helpers in the
item are proved. `moduleCup_globalComparison` and `moduleCup_singleTensorIso`
are real constructions with no holes.

This is a decomposition, not a sorry-free proof. One original hole is closed
and six holes are added: arithmetic net -5. All six are reachable through the
item's proof imports. This local inventory is not a computation against the
ledger's pinned closure baselines; other pre-existing imported holes remain.
No positive closure progress is claimed.

Edge cases checked mathematically: empty scheme, zero coefficients and zero
representatives; p=q=0; identical and distinct computing pairings; nonflat
coefficients; arbitrary unbounded integer complexes in compatibility. The
H-zero model needs no flatness of F or G. Canonical transport uses an actual
K-flat resolution isomorphism. The only chosen data in the new definitions are
uniquely prescribed cycles and proposition-valued tensor-structure instances;
no arbitrary object is chosen from an unproved existence theorem.

## No longer needed

Second reading removes the proposed new module `Sheaf.Paper.ModuleCupTruncationAdjunction`
and node `lem-sc-module-cup-truncation-adjunction`; invariance directly imports the
upstream TStructure module. This removes one proposed hole, not a baseline module.
The old item node had empty `proof_deps`, so no old proof-dependency node is omitted
from this inventory.

Removed three redundant direct imports from the new compatibility module:
`WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`,
`WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory`, and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`.
The retained signature imports already publicly supply them. FlatResolution
must remain: removing it fails to synthesize the ModuleCat derived-category
instance used in the public comparison and compatibility signatures.


The item's redundant direct import
`WeilConjectures.AlgebraicGeometry.Modules.TensorSection` remains removed;
the data module publicly re-exports it and needs it for `augmentation_pair`.
This is import deduplication, not pruning from the target closure.

Both original Cech comparison exports remain. No blueprint unit statement or
step is bypassed: `sk-prop-av-cube` has no realized statement/step nodes for this
construction. No module or node is claimed pruned. The old Godement/Leray proof
route in the flasque node and flat-resolution construction route in the
connectivity node were inaccurate descriptions, and are replaced by the actual
Lean proofs; this does not claim their mathematical theories are globally unused.

## Where the brief, the DAG or earlier work was wrong

The original item node had no numbered proof plan; its proof was only in the
docstring. The earlier decomposition records the actual upper proof route.

Return point 1 was correct: the former compatibility declaration assumed its
entire conclusion, despite its docstring and node claiming a canonical diagram.
The repair replaces that declaration with a genuine, non-tautological theorem
statement, whose full proof remains an explicit hole. Spec Z was also the wrong
base: the correct base is the point with ring Γ(X,O_X).

Return points 2 and 3 were correct: the flasque and Godement nodes overstated
their Lean declarations; the model H-zero assertion did not establish the
canonical identification. The canonical comparison now has its own module,
node and explicit transport. Actual proved flasque/connectivity arguments are
now recorded rather than unrelated construction plans.

Return point 4 was correct: cited modules were missing from proof imports.
The repaired imports expose the planned lower tasks in the target closure.

Return point 5 was correct: the old hole inventory and blanket second-reading
claim were false. This report replaces them with declaration-level checks and
accurate local counts. No existing target or pre-existing definition changed.

## New nodes

`def-sc-module-cup-resolution-data` records the original moved data; no hole.
`lem-sc-module-cup-pairing-exists` supplies computing paired resolutions only.
`lem-sc-module-cup-resolution-invariance` compares transported output classes
for equal input classes; it neither constructs a product nor asserts uniqueness.

`lem-sc-module-cup-godement-aw` records only existence of flasque augmented
complexes and their tensor cochain map. `lem-sc-module-cup-flasque-acyclicity`
records only positive-degree vanishing, proved by the abelian comparison.
`lem-sc-module-cup-derived-tensor-connectivity` records the one-line upstream
`isLE_tensor` specialization. `lem-sc-module-cup-hzero-identification` records
the nonpositive termwise-flat model calculation.
`lem-sc-module-cup-naive-derived-compatibility` records the actual six-object
global diagram.

`lem-sc-module-cup-canonical-hzero-identification` is new in this repair. It
records the canonical Q tensor comparison into the ordinary tensor single
complex, invertibility on H-zero, and equality with the explicitly transported
flat-model augmentation. Its proof uses the model H-zero node.

Change record: `coord/changes/module-cup-resolution-data.md`. No existing
consumer is adapted; no forced-adaptation exception is used.

## Earlier second reading (a previous round; superseded)

Correction of the earlier reading for return X-3869a. These are the repair
worker's declaration-by-declaration checks; the dispatcher’s independent
second reader must recheck them before delivery. The previous blanket PASS
and assertion that no repair was needed are withdrawn.

1. `moduleCup_godement_pairing`: the node now matches existential K,L,M,
   nonnegative support, flasqueness, quasi-isomorphic augmentations, tensor
   cochain map and degree-zero formula. It promises no specified Godement
   objects or naturality. Pairing-exists consumes these existential data.
2. `moduleCup_flasque_acyclicity`: the node now matches only IsZero of positive
   module cohomology under underlying-sheaf flasqueness. Its actual proof uses
   module_cohomology_iso_underlying_abelian, subsingleton_H'_top and transport
   to ModuleCat.isZero_iff_subsingleton. Computing comparisons are left in
   pairing-exists with the separate Leray criterion.
3. `moduleCup_derived_tensor_connectivity`: its generic category hypotheses
   and degree-zero singleFunctor tensor IsLE 0 conclusion match the node.
   The proof is isLE_tensor specialized to 0,0 followed by simpa; no new flat
   resolution construction is claimed. Invariance needs exactly this bound.
4. `moduleCup_hzero_identification`: the node matches P.IsStrictlyLE 0,
   QuasiIso p, termwise flatness and IsIso of the termwise tensor homology map.
   It supplies the model calculation only. The new canonical theorem specifies
   the single-tensor identification and equality of its comparison with the
   flat-model transport through Qp, QObjTensorQObjIsoOfKFlatLeft and Q(p tensor id).
   Invariance explicitly cites both nodes, using the canonical theorem to fix
   which H-zero isomorphism makes augmentation_pair the identity.
5. `moduleCup_truncation_adjunction`: the node matches bijectivity of the
   H-zero map on morphisms K→singleFunctor(M), under K.IsLE 0. Invariance uses
   its injectivity to identify the derived morphisms after fixing H-zero.
6. `moduleCup_naive_derived_compatibility`: the six vertices are Q(TK) tensor^L
   Q(TL), R(QK) tensor^L R(QL), Q(TK tensor TL), R(QK tensor^L QL),
   Q(T(K tensor L)) and R(Q(K tensor L)). The top and bottom arrows are the
   canonical right-derived units; the tensor comparisons are μ_Q; the naive
   map has the explicit tmulSection summand formula. The theorem asserts both
   paths agree without assuming equality. The natural derived cup family and
   naive map are existential theorem data, never chosen in definitions.
   Invariance uses the diagram to compare computing resolution classes.

All six repaired declarations, and the additional canonical theorem, are
checked separately against their nodes. Existing item signatures and data
bodies must remain unchanged. The remaining existence and invariance proofs
are complete-proof holes, so the documented downstream use is a plan rather
than a claim those holes have been proved from the imports.

## Second reading by P3

Independent second reader, 2026-10-13. Read every delivered Lean module, its
node, the original item, the unit record, the change record and the repair report.

1. PASS: diff against the read-only repository shows only the original item and
   its node existed there. Compared the four moved declaration bodies byte for
   byte after stripping docstrings, the two remaining public signatures byte
   for byte, and the entire IsModuleCupProduct definition byte for byte. All
   match. Moving the data is declared in module-cup-resolution-data.md; its
   public re-export retains the original names. No target statement changes.
2. PASS with explicit open dependencies: all eleven initial modules compiled
   without warnings. A scratch copy with #print axioms checked every new
   construction, each private proof/helper and the public results individually.
   Only propext, Classical.choice and Quot.sound occur, with sorryAx additionally
   on the six named splits and the results depending on invariance/existence.
   There is no prohibited declaration, hole in a definition or private hole.
   cupPairCycle chooses the unique subtype element with a prescribed value from
   a proved existence theorem. The bilinear descent choices occur inside a
   proved theorem, and its output is verified there.
3. PASS after repair: six remaining splits have sourced full proof docstrings
   and matching nodes. Existence supplies resolution data only; invariance
   supplies equality of product classes only. Neither restates unique product
   existence. The Godement split is smaller than computing-pairing existence;
   the two H-zero tasks and compatibility are distinct parts of invariance.
   Checked degree zero, zero coefficients/representatives, empty space, nonflat
   coefficients, identical/different pairings and unbounded compatibility.
   The actual global six-object diagram matches Stacks 20.31.3 and its global
   specialization (https://stacks.math.columbia.edu/tag/0FKU). Independently
   searched with new LeanFinder, Loogle and rg queries. Local source search
   found the exact upstream truncation homology bijection: removed the duplicate
   split module/node and now use that upstream result directly. No equally
   short proof of the other six splits was found. The flasque bridge and
   connectivity specialization are fully proved, with standard axioms only.
4. PASS after repair: read the upper proof downward: surjective class maps,
   Leibniz product cocycle, bilinear descent through equal input classes,
   cross-resolution invariance, then extensional uniqueness. It is a real
   reduction, not a single application of a renamed target. Removed three
   redundant imports from the new compatibility module; retained its necessary
   FlatResolution import after an explicit removal trial failed. Added explicit
   plain Leray proof imports to pairing-exists. Existing Cech public exports
   remain to preserve the original interface. The original node had empty
   proof_deps; No longer needed accounts for that and for every removal.
   sk-prop-av-cube has realized.statement=[] and realized.steps=[[]]; no
   realized unit statement or step is bypassed or changed.
5. PASS after repair: all proof_deps are exactly the union of the step uses;
   every cited node exists. Lean statements in the new nodes match their
   declarations. Godement states existential flasque augmented complexes and
   a cochain pairing, flasque states positive module cohomology vanishing,
   connectivity records the actual isLE_tensor specialization, model H-zero
   states only its termwise calculation, canonical H-zero adds the specified
   canonical comparison and flat-model transport, and compatibility records
   the six concrete vertices and arrows. Updated the invariance plan to cite
   the upstream truncation result instead of the deleted duplicate node.
   Normalized new nodes' created.by to worker as required by the brief.

Changes by this reader: removed ModuleCupTruncationAdjunction and its node/hole;
replaced its invariance import and proof-plan reference with upstream TStructure;
added two plain Leray imports; removed three redundant compatibility imports;
corrected the final hole inventory to six and local net to -5; recorded the
independent checks here. No existing mathematical signature or definition was
altered. This remains a decomposition, not a completed cup-product proof.

Final validation by second reader: deliver3.py --no-push printed OK for
commit 267d11a330, after compiling all ten final modules and running the
declaration axiom probes and preflight. Review class CODEX.
