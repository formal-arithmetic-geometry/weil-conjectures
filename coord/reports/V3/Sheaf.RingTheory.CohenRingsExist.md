## What changed

Replaced the first worker's `exists_cohenRing_core` restatement with a genuine reduction
of the unchanged `exists_cohenRing` statement. The item now obtains a flat local
extension from the existing Tag 03C3 theorem, constructs the ring explicitly as
`AdicCompletion (IsLocalRing.maximalIdeal S) S`, and proves its maximal-ideal,
completeness, and residue-isomorphism clauses using Mathlib. The new module
`Sheaf.RingTheory.CohenCompletionDVR` isolates only the domain/DVR property of this
fixed completion, conditional on a given flat extension with maximal ideal `(p)`.
No definition or existing signature changes; no change record or forced adaptation.
The item's docstring and DAG proof now describe the actual reduction.

The only public import of the item remains `Sheaf.RingTheory.CohenRing`.
`Mathlib.NumberTheory.Padics.RingHoms`,
`Mathlib.RingTheory.AdicCompletion.LocalRing`, the new completion lemma, and the
existing flat-local-extension theorem are proof-only imports. The helper's public
imports are needed by its signature: p-adic integers, the adic-completion ring,
and the flat ring-map predicate.

## Proved and sorry left

Hole closed in the item: `exists_cohenRing`
(node `lem-weil-pbc-cohen-rings-exist`). Its body is now a checked reduction.
Hole added: `adicCompletion_dvr_of_flat_padicInt`
(node `lem-weil-pbc-cohen-completion-dvr`) in
`Sheaf.RingTheory.CohenCompletionDVR`; its entire proof is `by sorry`.
There are no other delivered holes. The uncommitted first-worker theorem
`exists_cohenRing_core` and its node/module were removed, not delivered.

This is a decomposition, not an unconditional proof: one original hole is replaced
by one strictly smaller hole, so the local hole delta is zero. The pre-existing
`IsLocalRing.exists_flat_local_extension_given_residue_field` is still open and
is used directly rather than restated. No whole-library or import-closure ledger
reduction is claimed without the maintainer's ledger measurement.

All delivered modules compile cleanly with `lcompile.py`. Scratch copies with
`#print axioms exists_cohenRing` and
`#print axioms adicCompletion_dvr_of_flat_padicInt` were also compiled. The item
and the helper both have only `propext`, `Classical.choice`, `Quot.sound`,
and `sorryAx`. The remaining `sorryAx` is explicitly accounted for by the
new conditional lemma and the already open flat-local-extension theorem.

## No longer needed

Removed proof-only imports:
- `Sheaf.RingTheory.AdicCompletionNoetherianOfQuotient`.
- `Sheaf.RingTheory.Flat.FlatModulePowers`.

Every old `proof_deps` entry removed from the item's new route:
- `def-weil-pbc-noetherian-ring`.
- `lem-weil-pbc-completion-noetherian-quotient-noetherian`.
- `lem-weil-pbc-flat-module-base-change`.
- `lem-weil-pbc-flat-module-powers`.

The new conditional argument cancels `p` directly on successive completion
components. It does not require Noetherianity of the completion or a complete
flatness criterion. The retained flat-local-extension import is actually applied.
The uncommitted `Sheaf.RingTheory.CohenRingCore` import/module and
`lem-weil-pbc-cohen-rings-exist-core` node were removed. Whether any removed
module becomes unreachable elsewhere is for the queue/ledger, not asserted here.

## Where the brief, the DAG or earlier work was wrong

The first worker's core theorem was definitionally the whole original existence
claim with `IsCohenRing` unfolded; it isolated no strictly smaller construction
step. Its report called the wrapper proved, did not update the item's DAG, and
incorrectly said that removed proof imports remained in the original interface.
Compilation also found a `letI` style warning. These faults are repaired.

The original ten-step plan had a longer Noetherian and complete-flatness detour.
At this below-unit level, direct componentwise cancellation gives the needed
nonzerodivisor property, and the same unit-times-power argument gives a domain
and DVR. No unit statement or realized step is changed or bypassed.

## New nodes

`lem-weil-pbc-cohen-completion-dvr` is the domain/DVR property of a specified
completion of a specified flat local p-adic algebra with maximal ideal `(p)`.
It asserts neither existence of that algebra nor a prescribed residue field,
nor completeness/maximal-ideal/residue-isomorphism clauses of the target.
Its module is `lean/Sheaf/RingTheory/CohenCompletionDVR.lean`; its node is
`dag/nodes/sec-proper-base-change/lem-weil-pbc-cohen-completion-dvr.json`.
The six-step proof in the docstring explains flatness giving injectivity of `p`,
locality and completeness, cancellation on components, maximal exponent,
the domain property, and principal ideals. Searches were actually run through
`msearch.py` and are recorded in `searches.jsonl`: LeanSearch was unavailable;
Loogle had no adic-completion domain theorem; LeanFinder returned locality,
DVR criteria requiring a domain, and completions of already-Dedekind rings;
grep returned completion locality and unrelated valuation completions.
`Sheaf.RingTheory.CompletionOfDVR` was read and is inapplicable: it assumes the
input already is a domain and DVR. Blueprint searches for completion/valuation
and completion/nonzerodivisor found no equivalent statement. There are no
change records.

## Second reading by V3

1. Compared every delivered module with the repository. The item has one
   existing declaration; the full signature of `exists_cohenRing`, its visibility,
   universe, prime hypothesis, arbitrary field/characteristic hypotheses, and
   quotient-ring equivalence conclusion are byte-for-byte unchanged. The new
   helper is the only added declaration. No existing definition, target,
   public import, or claimed module's interface was altered.
2. Compiled both files and the axiom scratch copies through `lcompile.py`.
   No compiler error or warning remains. Exactly one named theorem has `sorry`,
   with its source, complete proof in words, and matching node; none occurs in
   a definition or a partial proof. No prohibited axiom/unsafe/opaque/extern/
   implemented_by/kernel-check escape occurs. Axiom output is as listed above.
3. Read [Stacks 0328](https://stacks.math.columbia.edu/tag/0328) and
   [00PD](https://stacks.math.columbia.edu/tag/00PD), the completion and flatness
   Mathlib source, and the existing dependency declarations. The old core was
   rejected as a restatement. The replacement helper only proves domain/DVR
   for the fixed completion; the item genuinely constructs this completion and
   proves all other clauses. Checked `p=2` and the identity extension `S=Z_p`:
   the conclusion agrees with the known complete DVR. `p=0,1` are excluded by
   primality. `S=F_p` cannot be a flat extension (multiplication by `p` fails
   injectivity), so the zero-uniformizer counterexample is excluded. The flat
   algebra `Z_p[epsilon]/(epsilon^2)` fails the maximal-ideal hypothesis, excluding
   surviving nilpotents. No perfectness, Noetherianity or separatedness of `S`
   is assumed; completion supplies separatedness. Cancelling `p*y=p^(n+1)*z`
   gives `y=p^n*z` and kills each component, so the argument uses exactly the
   supplied flatness. Searches and the inapplicable completion-of-DVR theorem
   were checked independently. No arbitrary witness is made into a public data
   definition: the existential extension is eliminated inside a proposition's
   proof, and its completion is an explicit construction. The helper chooses
   only proofs of properties of that fixed object.
4. Followed the item from the top: Mathlib residue and completion results prove
   the available clauses, Tag 03C3 is used directly, and only the genuinely
   smaller domain/DVR subargument remains open. All proof imports are needed;
   public imports in the helper occur in its signature. Every removed old DAG
   dependency is listed under No longer needed. Read `dag/units/sk-thm-p1.json`:
   neither this item nor any removed dependency is a node realizing that unit's
   statement or a step. Its `realized` fields and chapter route are untouched.
5. The updated item node's six proof steps and dependency union match the Lean
   body, including the existing flat-local-extension theorem and new conditional
   lemma. The new node has the exact Lean signature, self-contained statement,
   definition citations, six-step proof, dependency union, worker proof origin,
   actual search records, inherited chapter/unit, blueprint ancestry, creation
   metadata, and Lean module/file/declaration metadata. The removed invalid
   core node is not delivered. No statement change record is needed.

Changes made by this second reading: removed the whole-statement core theorem;
wrote the explicit flat-extension/completion reduction; isolated the smaller
conditional DVR lemma with a full proof description; removed the unnecessary
Noetherian/complete-flatness imports; repaired the DAG, docstrings and report;
and eliminated the style warning. Verdict: valid decomposition for delivery,
not a completed proof of Cohen-ring existence.
