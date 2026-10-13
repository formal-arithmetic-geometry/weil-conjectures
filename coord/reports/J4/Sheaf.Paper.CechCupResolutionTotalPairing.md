## What changed

Replaced the retained invalid arbitrary-pairing reduction. The unchanged statement
`cupCechResolution_total_pairing` now obtains the library's characterized sheaf cup
product, constructs a bilinear map by transport through A.iso, B.iso and C.iso,
and proves the alpha square directly. Only the beta square is split off, in
`Sheaf.Paper.CechCupResolutionBetaClassPairing`.

The prerequisite `Sheaf.Paper.CechCupResolutionComparisonData` is already present in the
current repository baseline and is imported unchanged. The duplicate prerequisite module,
node, and change record from the retained delivery were removed. The absent assigned module
is documented in `coord/changes/CechCupResolutionTotalPairing-new-module.md`.


## Proved and sorry left

Closed the assigned hole `AlgebraicGeometry.Scheme.Modules.cupCechResolution_total_pairing`
(node `lem-sc-cech-cup-resolution-total-pairing`) by a complete transport proof.
Added one strictly narrower hole:
`AlgebraicGeometry.Scheme.Modules.cupCechResolution_beta_class_pairing`
(node `lem-sc-cech-cup-resolution-beta-class-pairing`). It fixes a characterized sheaf
cup product and asserts only the beta equality, with no total pairing existence
or alpha square. This is a decomposition (one hole closed, one added), not a net
hole reduction. The retained attempt had reverted the assigned theorem to sorry;
this delivery closes that sorry without reinstating its false axes lemma.

Compilation verifies the composition; the new beta theorem still requires the signed
cochain argument documented in its docstring. No other sorry is added in the delivery.
The sheaf-cup existence theorem is already proved in the library, though its imported
resolution-theory dependencies may still contain sorry.

## No longer needed

The retained proposed core-existence and arbitrary-core-axes nodes
`lem-sc-cech-cup-resolution-total-pairing-core-existence` and
`lem-sc-cech-cup-resolution-total-pairing-core-axes`, and the removed
`Sheaf.Paper.CechCupResolutionTotalPairingCore`, are not used or delivered. The duplicate
`def-sc-cech-cup-resolution-comparison-data` node and its module are also not delivered,
because that node already exists on sheaf-dag and its module is present in the baseline.
The core-existence theorem would assert existence of an unconstrained bilinear map,
which is already supplied concretely by transport. A generic theorem saying every
such map preserves both axes is false. No original public import is removed: both
comparison data and the coefficient Cech formula occur in the unchanged signature.
No blueprint unit statement or proof step is bypassed; this item is below the unit.
The unchanged sandbox copy of `CechCupProduct` was removed from the delivery.

## Where the brief, the DAG or earlier work was wrong

The retained report claimed a proof through a core module that its later second
reading had deleted; its DAG still cited those deleted nodes. Its comparison-data
node also lacked the leansearch search category, and recorded an elaborated type
instead of the declared source signature. The present records and report describe
the actual proof and correct these metadata errors.

The current baseline lacks the assigned and beta modules, while the comparison-data
prerequisite is already present. Only the assigned and beta modules are registered as
new delivery files. The beta obligation is valid for arbitrary U:
alpha invertibility is explicitly assumed, rather than inferred from a cover.
Degree-zero inputs, zero classes, and empty index sets obey the same bilinear
cochain calculation; no hypothesis on quasicoherence or nonempty covers is added.

## New nodes

`lem-sc-cech-cup-resolution-total-pairing` records the assigned theorem, absent from
this baseline, with its unchanged signature and the new transport proof route.

`lem-sc-cech-cup-resolution-beta-class-pairing` is the one remaining augmentation-axis
obligation, in its own module. Its complete natural-language proof records the signed
assembly, alpha identification and beta component calculation from Tags 07MB and 0FKV.

## Earlier second reading (a previous round; superseded)

1. Interface: compared both delivered modules with the repository paths.
   Neither assigned module exists in this repository baseline, so their diffs are whole new files;
   no baseline declaration or target is edited. Compared the assigned theorem's
   signature byte for byte with the sandbox received from the first worker:
   identical. The beta signature is also identical after this reading. The
   comparison-data module is an existing baseline dependency and is unchanged by this repair.
   Verdict: no accidental interface change; the missing-baseline limitation is
   explicit, rather than a claim of comparison against an unavailable original.

2. Proof: compiled both delivered modules in import order through lcompile.py, then
   compiled scratch copies with explicit #print axioms for cupCechDouble,
   CupCechResolutionComparison, cupCechResolution_beta_class_pairing and
   cupCechResolution_total_pairing. The construction and structure use only
   propext, Classical.choice and Quot.sound. Both theorem checks also show
   sorryAx, as expected for the named beta obligation and open imported theory.
   There is exactly one direct sorry in the delivery, the public beta theorem
   listed above; none in a definition. No forbidden declaration, implementation
   escape or overlong Lean line occurs. The alpha proof uses A.alpha_class and
   B.alpha_class, cancels iso inverses, applies hcup D to the specified cycle,
   and finishes with C.alpha_class. The beta proof postcomposes its named
   equality and cancels C.iso.inv. Verdict: correct composition, one remaining
   obligation; this is a decomposition, not an axiom-free proof of the target.

3. Split statement: read Stacks Tags 07MB (and Remark 20.25.3), 0FKV's last
   diagram, and 01EQ's alpha/beta construction, against every field used.
   The beta lemma fixes a cup with the universal resolution characterization;
   it says nothing about arbitrary bilinear maps. Its conclusion is precisely
   the beta equality after transport, with neither the existential construction
   nor the alpha square. Its signed-cochain proof is still substantial, but is
   only the remaining part of the argument. Resolution degree is first, so the
   total differential is d_resolution + (-1)^r d_Cech on degree (r,i).
   The crossing sign (-1)^(i*s) gives the total Leibniz rule; on either axis
   it is one. Restriction and augmentation compatibility are actual fields of D.
   Surjectivity of H(alpha) and the cycle-to-homology projection justify lifting
   the two inputs; C.alpha_class identifies the output. No cover assumption is
   used for this conditional statement: A and B explicitly supply quasi-isos.
   Checked degree zero, zero inputs, and an empty index type. In the last case
   the Cech terms and totals are zero, and the supplied isos force the relevant
   sheaf cohomology to be zero as well. All formulas are consistent.
   Re-searched with leanfinder for a bilinear total-double-complex product,
   loogle for homologyMap/tensor, and grep for cup/comparison and total/bilinear
   (searches.jsonl records the calls). LeanFinder returned total-complex and
   bifunctor infrastructure, not an axis-compatibility theorem; the other two
   searches had zero hits. Read CechCupPullbackCompat and
   cechCup_resolution_representatives: their cover and quasicoherence hypotheses
   prevent applying them to this arbitrary-family, arbitrary-module statement.
   Verdict: true conditional obligation with source, proof docstring and node;
   no available direct replacement, and no few-minute formal closure found.

4. Route and imports: the characterized cup is obtained from the already proved
   exists_unique_moduleCupProduct. The total pairing is constructed by bilinear
   composition, rather than selected from an unconstrained existence theorem.
   Both public imports in the assigned and beta modules occur in their public
   signatures; the beta proof dependency is a plain import. The comparison-data
   imports supply the resolution structure and canonical comparison fields.
   No unused delivered module or proof import remains. The discarded core nodes
   are absent from the delivered sources and actual proof_deps. Since the item's
   baseline module/node is absent, no further original proof_deps can be audited; the
   existing comparison-data node is used as an ordinary dependency.
   Read dag/units/sk-prop-av-cube.json: neither its statement nor its realized
   steps is touched. The change stays below that unit and retains the Cech/sheaf
   comparison route. Blueprint search for Cech cup found no imported duplicate.
   Verdict: shortest available transport route retained; no additional pruning.

5. Metadata: checked each Lean declaration against its node's statement and
   lean record. The assigned node now cites the comparison-data fields actually
   used in the alpha step; the beta node's last step now cites D's augmentation
   and the beta component and Cech definitions. proof_deps is the union of step
   uses. New nodes have source, searches, created, unit/chapter and Lean records.
   Their blueprint.from had named newly created intermediates as ancestors;
   corrected all three to thm-sc-theorem-of-cube with the existing representative,
   cup-compatibility and Kunneth chain in via. LeanSearch's recorded service error
   now has verdict unavailable. Verdict: records describe the delivered proof.

Changed in this reading: the assigned theorem's proof docstring now describes
its actual transport argument, including the remaining beta obligation, rather
than claiming an implemented cochain construction with no acyclicity used.
Corrected the dependency citations, blueprint ancestry and unavailable-search
verdicts. No Lean proof body, signature, definition or import changed. Explicit
axiom scratch files were removed before delivery.

## Second reading by K1

1. Interface: compared both delivered modules and their declarations with the repository
baseline; neither module exists there, and the target signature is unchanged from the
assigned statement. Verdict: no accidental statement or definition change.

2. Proof: compiled both modules with lcompile.py in import order. The total theorem has no
direct sorry; the beta theorem is the sole named split-off sorry, with no sorry in a
definition and no forbidden declarations. Verdict: the transport proof compiles and its
remaining obligation is explicitly isolated.

3. Split statement: checked the beta statement against the signed total cochain argument,
including degree-zero, zero-input, and empty-index cases. It is strictly narrower than the
assigned theorem and asserts only the augmentation equality for a characterized cup.
Verdict: true and appropriately decomposed; no existing direct theorem was found.

4. Route and imports: the assigned proof uses the characterized cup, comparison isomorphisms,
and the beta split theorem; both public imports occur in signatures and the beta proof import
is private to the item. The unit route remains unchanged and the discarded core nodes are not
used. Verdict: route and pruning are consistent.

5. Metadata: checked node statements, lean records, proof steps, dependencies, sources,
blueprint ancestry, and the new change record against the Lean declarations. Verdict: metadata
matches the delivered proof and split.

Changed in this reading: only this review section was added; no Lean proof, signature,
import, node, or change record was altered.

## Earlier second reading (a previous round; superseded)

The two modules compile in sandbox import order. The total pairing theorem is proved by
transporting the characterized module cup product through the comparison isomorphisms;
the beta axis is isolated as the strictly smaller named theorem and is the only remaining
sorry. Signatures and the target statement are unchanged, and the unit route is retained.

## Second reading by J4

1. Interface: opened both delivered modules and checked the corresponding repository
   paths. The total and beta modules and their nodes are absent in this baseline,
   so a byte-for-byte comparison to an original assigned signature is unavailable.
   This is a declared new-module delivery, not a verified replacement of a baseline
   hole. No existing target or declaration is edited. The extra comparison-data
   copy was byte-for-byte identical to the repository and was removed from the
   sandbox. Verdict: no accidental existing interface change; the original-signature
   limitation remains explicit.

2. Proof: compiled the original three-file set in import order with lcompile.py,
   then scratch copies of both theorem modules with explicit #print axioms.
   cupCechDouble and CupCechResolutionComparison use only propext, Classical.choice,
   and Quot.sound. Both theorems additionally use sorryAx, consistent with the
   remaining beta obligation and imported open theory. The delivery has exactly
   one direct sorry, cupCechResolution_beta_class_pairing; none in a definition,
   and no forbidden declaration or implementation escape. The total proof constructs
   t with compl₁₂/compr₂, uses alpha_class to cancel the input isomorphisms, applies
   hcup to D and hc, and uses C.alpha_class for the output. Its beta branch applies
   the split equality and cancels C.iso.inv. Verdict: valid formal composition,
   one hole closed in the assigned draft and one added; no net hole reduction is
   claimed, and the target is not an axiom-free completed proof.

3. Split statement: read Stacks 07MB, Remark 20.25.3 (0FLI), and 0FKV's final
   diagram, and checked D.restriction, D.leibniz, D.augmentation_pair, alpha_f,
   beta_f, alpha_quasiIso, and alpha_class in the actual imported definitions.
   The source uses covers and flasque resolutions to obtain comparison isomorphisms;
   this conditional statement instead assumes those isomorphisms explicitly.
   With resolution degree r first, Mathlib's total signs are ε₁=1 and ε₂=(-1)^r.
   The crossing sign (-1)^(i*s) in the documented construction gives the required
   Leibniz signs and is one on both axes. Quasi-isomorphism of alpha and surjectivity
   of the cycle projection identify every input with a global resolution cycle;
   hcup then identifies the total pairing, and augmentation_pair proves its beta
   formula. This is only the beta obligation, not total-pairing existence or the
   alpha clause. Checked p=q=0 (ordinary augmentation/tensor), zero inputs
   (bilinearity), and an empty index type (zero Cech complexes and totals; the
   assumed isomorphisms force zero cohomology). Verdict: true conditional lemma,
   strictly narrower as an argument obligation, with source, proof docstring and
   matching node; its substantial cochain construction is not a few-minute closure.
   Fresh leanfinder search for products on bicomplex total cohomology returned
   group-cohomology infrastructure, loogle for homologyMap/bilinear returned no
   hits, and msearch grep for Alexander-Whitney/beta-class/total-cup returned no
   upstream hits. Also searched lean/Sheaf and lean/WeilConjectures by total,
   beta and pairing, and the upstream checkout by Cech/cup. The existing
   cechCup_resolution_representatives requires a cover and quasicoherence,
   so cannot replace this arbitrary-family lemma; cechCupPullbackCompat has the
   same restriction. No direct replacement was found.

4. Route and pruning: IsModuleCupProduct is precisely the all-resolution cycle
   characterization applied in the alpha branch; exists_unique_moduleCupProduct
   already has a proof. The selected cup has a uniqueness characterization, and
   t is constructed explicitly by linear-map composition. Both public imports
   supply signature symbols; the beta lemma is a plain proof import. No retained
   arbitrary-core theorem is used. The report lists both discarded core nodes,
   but their old proof_deps cannot be compared because the assigned baseline node
   is absent. Opened sk-prop-av-cube.json: its statement and realized steps are
   untouched, and the supplied ancestry retains the representative/comparison
   route below the unit. Verdict: no unit route bypass or additional unused import.

5. Metadata: compared both node lean.statement records with the Lean signatures
   modulo whitespace, and read each proof step against the declarations it cites.
   The total node records construction, alpha characterization, then the beta
   theorem; the beta node records signed assembly, alpha identification and beta
   augmentation. Each proof_deps equals the union of step uses. Source,
   proof_origin, searches (including the explicitly unavailable LeanSearch),
   created, blueprint, chapter/unit, and lean fields are present. Verdict: the
   records agree with this decomposition. No existing node field is changed.

Changed in this reading: removed the redundant unchanged comparison-data source
copy, removed the axiom-check scratch sources, and appended this review. Lean
proofs, signatures, definitions, imports, and node statements remain unchanged.
