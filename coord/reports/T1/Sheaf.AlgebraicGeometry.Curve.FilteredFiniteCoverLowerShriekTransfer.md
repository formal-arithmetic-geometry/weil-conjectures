## What changed
The target theorem now combines two explicit intermediate transfer theorems. The core theorem isolates compactification, filtration devissage, and finite pushforward without requiring the retraction; the retract theorem isolates descent along the supplied unit retraction. Both intermediate proofs remain named `sorry`s for parallel proof.

## Proved and sorry left
`AlgebraicGeometry.IsCurve.filteredFiniteCoverLowerShriekTransfer` is proved by applying the two intermediate theorems. Sorry remains in `filteredFiniteCoverLowerShriekTransfer_core` (node `k1-filtered-finite-cover-lower-shriek-transfer-core`) and `filteredFiniteCoverLowerShriekTransfer_retract` (node `k1-filtered-finite-cover-lower-shriek-transfer-retract`).

## No longer needed
The item's direct proof dependencies are now the core and retract nodes; its former compactification/devissage dependencies are recorded on the core node and its former retract dependencies on the retract node. The target retains its two public signature imports and adds two plain proof-only imports; no import was removed.

Former direct dependencies moved to the helper plans (none pruned): `thm-pqf-zmt-factorization`, `etale-proposition-etale-reduced`, `def-nagata-scheme-theoretic-closure`, `def-weil-pbc-scheme-reduction`, `lem-weil-pbc-closed-immersion-finite`, `lem-weil-pbc-finite-composition`, `lem-weil-pbc-finite-over-separated-finite-type`, `lem-weil-pbc-integral-incomparability`, `lem-weil-pbc-finite-permanence-over-separated`, `lem-weil-pbc-finite-closed-map-finite-fibres`, `lem-weil-pbc-finite-type-over-noetherian`, `lem-weil-pbc-qc-open-immersion-finite-type`, `def-weil-pbc-extension-by-zero`, `lemma-weil-pbc-eight-curve-devissage`, `lemma-weil-pbc-finite-pushforward-extension-zero`, `def-weil-pbc-finite-open-comparison`, `lem-weil-pbc-curve-assertions-finite-pushforward`, `def-weil-pbc-primary-torsion`, `def-weil-pbc-constructible-torsion`, `lem-weil-pbc-finite-pushforward-constructible-noetherian`, `lem-weil-pbc-curve-assertions-retract`.

## Where the brief, the DAG or earlier work was wrong
Repair of return X-6afac (head 6afac6afe): the independent reviewer passed the
delivery, but landing stopped because another merge held coord/.merge.lock
for 120 seconds. The return requests regeneration on current sheaf-dag and
server compilation. The approved three-module reduction and node records are
retained. deliver3.py --no-push fetches current sheaf-dag, regenerates a single
delivery commit on that base, compiles locally and on the server, and runs
preflight. This repair does not retry the landing or push the branch.

The original node's three-page proof cannot be completed directly within this item; it has been split at the two mathematically independent transfer steps so each can be proved in parallel.

## New nodes
`k1-filtered-finite-cover-lower-shriek-transfer-core` and `k1-filtered-finite-cover-lower-shriek-transfer-retract` are new intermediate statements corresponding to the compactification/devissage and retract steps.

## Earlier second reading (a previous round; superseded)
1. **Statements and accidental changes.** I compared the delivered target module with the repository version. The target declaration is byte-for-byte unchanged; only its proof and two proof-only imports differ. The two split-off declarations are strict intermediate statements: the core concludes for the pulled-back sheaf, while the retract theorem assumes that conclusion and adds the retraction data before concluding for `G`.
2. **Proof and axioms.** All three modules compile with `lcompile.py --all`. The target has no `sorry`; the only remaining `sorry`s are the two named intermediate theorems listed above, each with a matching node. No forbidden declarations or hollow definitions were introduced. The intermediate theorem docstrings now record the complete compactification/devissage and retract arguments in words.
3. **Split-off statements.** I checked the edge cases `n = 0` and a trivial retraction conceptually: the core uses `hzero` and `hend`, and the retract step reduces to the identity when `ρ` is an inverse to the unit. Neither statement is a restatement of the target, and neither duplicates an existing library theorem.
4. **Pruning and imports.** I checked the parent node against its Lean proof: its direct dependencies are `k1-filtered-finite-cover-lower-shriek-transfer-core` and `k1-filtered-finite-cover-lower-shriek-transfer-retract`. Both imports are used and remain proof-only. I checked that the core proof is baseline steps 1 and 2, with their original uses lists and proof dependencies equal to their union: `thm-pqf-zmt-factorization`, `etale-proposition-etale-reduced`, `def-nagata-scheme-theoretic-closure`, `def-weil-pbc-scheme-reduction`, `lem-weil-pbc-closed-immersion-finite`, `lem-weil-pbc-finite-composition`, `lem-weil-pbc-finite-over-separated-finite-type`, `lem-weil-pbc-integral-incomparability`, `lem-weil-pbc-finite-permanence-over-separated`, `lem-weil-pbc-finite-closed-map-finite-fibres`, `lem-weil-pbc-finite-type-over-noetherian`, `lem-weil-pbc-qc-open-immersion-finite-type`, `def-weil-pbc-extension-by-zero`, `lemma-weil-pbc-eight-curve-devissage`, `lemma-weil-pbc-finite-pushforward-extension-zero`, `def-weil-pbc-finite-open-comparison`, `lem-weil-pbc-curve-assertions-finite-pushforward`. The retract proof is baseline step 3, with proof dependencies `def-weil-pbc-primary-torsion`, `def-weil-pbc-constructible-torsion`, `lem-weil-pbc-finite-pushforward-constructible-noetherian`, `lem-weil-pbc-curve-assertions-retract`. The former dependencies remain on these intermediate nodes rather than on the parent.
5. **DAG, unit route, and conditional hypotheses.** I verified all three node records against the unchanged Lean signatures. Both new statements are self-contained TeX and cite every definition in `stmt_deps`. Both blueprint ancestors are `prop-weil-pbc-algebraically-closed-extension`, via `k1-filtered-finite-cover-lower-shriek-transfer` and `e1-prime-coefficient-curve-assertions`. Searching the imported blueprint node statements and the `sk-thm-p1` unit's steps found no equivalent statement; `lem-weil-pbc-curve-assertions-retract` is a general retract theorem requiring coefficient conditions, not this specialized theorem that verifies them. Thus both `same_as` lists are empty. The unit's curve-calculation route is retained. I checked the corrected retract docstring in the nonzero p-primary case (p = r), the nonzero invertible-order case (r invertible in k), and the zero case (G = 0 and K = 0). These checks pass the conditional hypotheses from F = j_!G to K = j_!(v_*v^*G), the direction required to use hH. Naturality supplies retractions of the comparison maps, and cohomology supplies retractions for vanishing and finiteness.

The repair changes the two new node statements, their proof dependencies and blueprint records, adds the existing item's composition node, corrects the retract docstring, and replaces second-reading points 4 and 5 with the checks above. No Lean statement or definition was changed.


## Earlier second reading (a previous round; superseded)

1. Statements and accidental changes: PASS. The diff against the repository changes only
   the target's proof and two plain imports. I compared the existing target signature
   byte for byte before `:=`: it is unchanged. No definition, existing docstring, or
   target in Challenge.lean was changed. The new core theorem now omits the unused
   retraction data; this corrects a new declaration, not an existing library statement.
2. Proof and axioms: PASS as a partial delivery. All three delivered modules compile
   locally. Scratch copies outside the delivered lean/ tree print the axioms of each
   declaration: propext, Classical.choice, Quot.sound, and expected sorryAx only.
   The target contains an actual composition of core transfer with retract descent.
   Exactly two named public theorems remain sorry, as listed above, with complete
   source-based proof docstrings and matching nodes. There are no definitions or
   forbidden declarations in the delivery. These checks do not certify the two
   unfinished proofs; the composition remains conditional on them.
3. Split-off statements: PASS. I read Stacks 03SD, 0A5C and 0A5D on their official
   tag pages because the local literature text is absent. The core corresponds to
   compactification, finite-open exchange, filtration induction and finite pushforward;
   the retract lemma corresponds to descent, assuming the larger sheaf's assertions.
   Their conclusions are different and neither restates the whole target. For n=0,
   hzero and hend make v^*G zero, and the retraction in the target makes G zero;
   the core by itself only needs the former. Empty schemes and identity covers cause
   no exception. For primary torsion with a nonzero stalk, an element of order r killed
   by p^a forces p=r. For invertible-order torsion, an annihilator of that element is
   divisible by r, so r is invertible in k. If j_!G=0, restriction gives G=0, hence
   v_*v^*G=0. These are exactly the conditional hypotheses needed in retract descent.
   Actual msearch queries using different words were run with leanfinder, loogle and
   grep and recorded for both new nodes. Local rg also inspected upstream Curve/
   Reductions.lean, Assertions.lean, RetractAssertions.lean, FinitePushforwardAssertions.lean
   and ConstructibleSheaf modules. No matching complete transfer theorem was found.
   assertions_of_isIso_comp is over ULift Z and requires the coefficient implications;
   it does not duplicate this specialized lemma. Neither helper can be closed in a
   few minutes: geometric compactification and coefficient/retract bridges remain.
4. Top-down route, imports and pruning: PASS. The target first applies the core and
   then the retract theorem. Both added imports are used only by the proof and are
   plain imports; the two public imports supply names in the signatures. No import
   is unnecessary. Every former direct dependency is retained transitively in the
   core or retract node, rather than discarded. Thus no module or node is pruned.
   The sk-thm-p1 realized statement and all realized steps remain untouched: this
   reduction stays inside its curve-calculation step, including filtration and trace
   splitting, and changes no unit or chapter route.
5. Node agreement: PASS. I compared the three Lean signatures against the node records
   and checked that proof_deps is exactly the union of proof-step uses. The parent
   records the two applications actually in its proof. The core records the geometric
   and devissage steps; the retract node records the coefficient checks and descent.
   New nodes have the required source, creation, blueprint ancestry, chapter, unit,
   search and Lean fields. Their natural-language statements agree with the Lean.
   The old dependencies below are all still represented in their corresponding helper
   nodes; none disappeared from the argument.

Second-reading repairs: removed unused rho and hrho arguments from the new core
signature and its natural-language node statement, updated the target application
and core docstring, and replaced the two new nodes' search records with actual
independent searches. No existing Lean signature was changed and no change record
is required for this correction to an as-yet-undelivered new theorem.

Sources read: [03SD](https://stacks.math.columbia.edu/tag/03SD),
[0A5C](https://stacks.math.columbia.edu/tag/0A5C),
[0A5D](https://stacks.math.columbia.edu/tag/0A5D).

Former direct dependencies retained, not pruned: `thm-pqf-zmt-factorization`, `etale-proposition-etale-reduced`, `def-nagata-scheme-theoretic-closure`, `def-weil-pbc-scheme-reduction`, `lem-weil-pbc-closed-immersion-finite`, `lem-weil-pbc-finite-composition`, `lem-weil-pbc-finite-over-separated-finite-type`, `lem-weil-pbc-integral-incomparability`, `lem-weil-pbc-finite-permanence-over-separated`, `lem-weil-pbc-finite-closed-map-finite-fibres`, `lem-weil-pbc-finite-type-over-noetherian`, `lem-weil-pbc-qc-open-immersion-finite-type`, `def-weil-pbc-extension-by-zero`, `lemma-weil-pbc-eight-curve-devissage`, `lemma-weil-pbc-finite-pushforward-extension-zero`, `def-weil-pbc-finite-open-comparison`, `lem-weil-pbc-curve-assertions-finite-pushforward`, `def-weil-pbc-primary-torsion`, `def-weil-pbc-constructible-torsion`, `lem-weil-pbc-finite-pushforward-constructible-noetherian`, `lem-weil-pbc-curve-assertions-retract`.

Dry-run repair: the node validator requires LeanSearch as well as LeanFinder and grep;
LeanSearch was actually attempted and returned Internal Server Error. This is recorded
as unavailable, with no mathematical verdict. Loogle remains an additional independent
search. Compilation and the other static checks passed before this metadata repair.


## Second reading by T1

1. Existing interfaces: PASS. Read every delivered module and diffed the item against
   the repository. Programmatic byte comparison confirms the entire existing theorem
   signature before `:=` is unchanged. The existing docstring is also unchanged; only
   two plain imports and the composition proof differ. No definition or Challenge
   target changes, and there are no change records or adapted existing modules.
2. Proof and trust: PASS for a partial reduction. All three modules compiled with
   lcompile.py --all. Independent scratch copies with #print axioms compiled in import
   order: each declaration uses only propext, Classical.choice, Quot.sound and
   expected sorryAx. Exactly the core and retract public named theorems remain sorry,
   each as its whole proof, with source, proof docstring and node. No forbidden
   declaration or hollow definition occurs. The original item has one of one direct
   sorries closed, but is still conditional on the two helper proofs.
3. Split statements: PASS. Independently read Stacks 03SD, 0A5C and 0A5D and the
   upstream Reductions, Assertions, RetractAssertions and FinitePushforwardAssertions
   modules. The core needs no retraction and concludes for j_!(v_*v^*G); the retract
   helper needs that conclusion, not the filtration or constant-case hypothesis.
   Neither restates the target. Checked n=0, zero sheaves, empty schemes and identity
   covers. For nonzero F=j_!G, an r-torsion stalk element has order r; primary torsion
   forces p=r and invertible-order torsion forces r invertible in k. If F=0,
   restriction gives G=0, hence K=j_!(v_*v^*G)=0. These supply conditional hypotheses
   in the direction required by hH. The finite dense open compactification step
   and filtration devissage agree with the cited sources. New independent msearch
   queries were run: leanfinder "cohomology sheaf retract direct summand comparison
   map bijective", loogle '"Assertions"', and grep
   "filteredFinite|assertions.*retract|assertions.*finite". Hits concern general
   cohomology or Lean parser assertions; none supplies either helper. Local rg also
   confirms that the existing retract and finite-pushforward theorems are over
   ULift Z and need coefficient transport and coefficient conditions. Neither helper
   can be closed by one of those declarations in a few minutes.
4. Route, imports and pruning: PASS. The actual proof combines core transfer with
   retract descent. Each new import is plain and used by that proof; each public
   import supplies signature names. No shorter complete theorem was found. Every
   former direct dependency is now listed explicitly under No longer needed and
   retained in the helper plans; no node or module is pruned. Read sk-thm-p1.json:
   its realized fields and curve-calculation route, including filtration and trace
   splitting, remain untouched.
5. Node agreement: PASS. Compared every Lean signature byte for byte with lean.statement
   in its node; proof_deps equals the union of proof-step uses for all three nodes.
   Only proof, proof_deps and proof_origin differ in the existing parent node. The
   union of helper dependencies equals the former parent dependency set. The two
   new nodes carry source, self-contained statements, statement dependencies, creation,
   searches, blueprint ancestry, chapter, unit, status and Lean records. Their plans
   and natural-language statements agree with their respective signatures and docs.

Second-reading changes this round: corrected the import description, made the former
direct-dependency list explicit in No longer needed, and appended this fresh review.
No Lean proof or statement needed repair. Earlier second-reading sections describe
previous rounds and are superseded by this section. The earlier no-push repair note
is historical; this round performs the requested dry run followed by delivery.

Sources checked: [03SD](https://stacks.math.columbia.edu/tag/03SD),
[0A5C](https://stacks.math.columbia.edu/tag/0A5C),
[0A5D](https://stacks.math.columbia.edu/tag/0A5D).
