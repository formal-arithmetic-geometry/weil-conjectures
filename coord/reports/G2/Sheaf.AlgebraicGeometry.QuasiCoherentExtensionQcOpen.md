## What changed

Completed the earlier sandbox proof of
`AlgebraicGeometry.Scheme.Modules.exists_quasiCoherent_extension_of_quasiCompact_open`
in `Sheaf.AlgebraicGeometry.QuasiCoherentExtensionQcOpen`, preserving its entire signature
and visibility. The construction is the pullback of the restriction unit and the
pushed-forward given map. A proved private helper identifies this pullback with the
kernel of the difference map on a biproduct, following Stacks 01PE (3).
A second proved private helper transports quasi-coherence from the localized site
to the open subscheme. The restricted second projection supplies the required
isomorphism, and adjunction identities prove its compatibility with the given map.

Repaired the earlier attempt's typeclass-search timeout by supplying the
`PreservesLimitsOfShape WalkingCospan` and `PreservesLimit (cospan a b)` witnesses
explicitly from the existing limit-preservation result. Removed an unused simp argument.
Kept the original file-level commands and qualified names within the proofs.
Added the proof-only Mathlib pullback-isomorphism import and removed the proof-only
TensorPullback import. Updated the item's DAG proof, proof_deps and proof_origin to
record the actual categorical implementation. No statement, definition, public import,
or other module was changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_quasiCoherent_extension_of_quasiCompact_open`
(node `lem-weil-pbc-quasi-coherent-extension-qc-open`).
Both private helpers `overEquiv_quasiCoherent` and `quasiCoherent_pullback` are proved.
There are no remaining sorries in this module and no added holes or new modules.
This is a proof from existing dependency declarations, not a decomposition into
new assumed intermediate statements. Existing dependencies may still rest on sorries;
this delivery makes no claim to have closed their transitive proof obligations.

## No longer needed

Removed import `Sheaf.AlgebraicGeometry.TensorPullback` and the proof dependency
`def-pc-module-pullback`: only the existing restriction/pushforward adjunction for
an open immersion is needed, not the general tensor pullback construction.
All other original imports are used: Coherent supplies the statement's moduleRings
carrier, QuasicoherentBinarySum supplies biproduct quasi-coherence,
QuasicoherentPushforwardQcqs supplies pushforward quasi-coherence, and
WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel supplies kernel
quasi-coherence and preservation of limits by restriction.
No unit statement or unit proof step is bypassed. The item is below the unit's
realized statements and steps. Whether TensorPullback leaves the targets' entire
closure depends on its other importers; this report claims only its removal here.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt already contained the main argument but had no report
or DAG update and did not compile: instance search timed out when constructing
`PreservesPullback.iso`. Explicit witnesses fix that failure without raising
heartbeat limits or changing any dependency definition.
The DAG's general tensor-pullback dependency was unnecessary for an open immersion.
The source's kernel construction and this pullback construction are canonically
isomorphic by the proved Mathlib abelian-category lemma, so the mathematical route
is unchanged. The local literature source is absent on this machine; Stacks 01PE
was read at https://stacks.math.columbia.edu/tag/01PE, including its proof.
The earlier recorded LeanFinder, Loogle and grep searches were inspected; they found
restriction/adjunction infrastructure but no ready-made extension theorem.
The statements and signatures of every original proof dependency were read.
No new statements or edge-case exclusions were introduced: U may be empty or all of X,
φ need not be injective or surjective, and X need not be quasi-compact or separated.

## Second reading by G2

1. Compared the only delivered module with the repository using diff and compared
   the existing theorem signature byte for byte. Verdict: identical hypotheses,
   conclusion, universes and visibility; no definition or public import changed,
   no change record needed. The two new helpers are private and fully proved.
2. Compiled the module locally with lcompile.py: clean, no warnings or errors.
   Compiled a scratch copy with #print axioms for the main theorem and both private
   helpers: each uses only propext, Classical.choice and Quot.sound, with no sorryAx.
   No sorry, forbidden declaration, or hollow definition is present. The chosen
   pullback is specified by its universal property; no arbitrary existence witness
   supplies the extension data.
3. No statements were split off and no holes added. Read both helper proofs: site
   equivalence transports quasi-coherence by the existing left-adjoint pushforward
   lemma, and the categorical pullback is the kernel of the biproduct difference.
   Checked empty and full opens, zero modules and arbitrary noninjective maps:
   no extra assumption is used. Independent Loogle and grep searches, including
   IsQuasicoherent with pullback and overEquiv, found the infrastructure already
   used but no ready-made extension or helper theorem replacing this argument.
4. Read downward from the extension theorem through the restriction adjunction,
   qcqs pushforward, binary sum and kernel declarations. Verdict: the proof takes
   the source's kernel construction through its canonical pullback isomorphism,
   and the final naturality and cancellation argument proves precisely the given
   map compatibility. Every retained import supplies statement or proof material;
   the added Mathlib import is proof-only. No longer needed lists the sole removed
   original dependency, def-pc-module-pullback / TensorPullback. Read
   dag/units/sk-thm-p1.json: none of its realized statement or step nodes is bypassed;
   this item and the pruned dependency lie below those nodes. No unit record changed.
5. Compared the node files: only proof, proof_deps and proof_origin changed.
   Checked all dependency Lean records and verified that proof_deps equals the
   union of proof-step uses. Verdict: the four steps match the actual construction,
   quasi-coherence proof, restricted isomorphism and compatibility proof. There
   are no new node records to validate.

Second-reading change: restored the original theorem docstring's correct node
citation lem-weil-pbc-quasi-coherent-module-kernel, which the first worker had
accidentally changed to the nonexistent lem-weil-pbc-quasi-coherent-module-Limits.kernel.
No proof changed. Independently read Stacks https://stacks.math.columbia.edu/tag/01PE
part (3) and its proof; it agrees with the kernel-of-difference route here.
