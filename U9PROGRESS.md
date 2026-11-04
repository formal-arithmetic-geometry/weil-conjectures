# K5 progress

2026-11-05: Read the assigned leaf, blueprint fix-prop-projection-formula proof,
Houyi PRs #2086/#2087, Sheaf route comparison records, and performance guide.
Merged pr/2086 (82afa10e6), as it restructures the assigned leaf without changing
its statement. Its sole new projection dependency sorry is
NativeCondensedRealizationCoherence.comparisonCompatible_derivedCondensedRealization.
Plan: prove the comparison via its sheaf/total/K-flat localization normalizations,
using new small helper files. No Lean/lake process run locally; no build yet.
PR #2087 provides an alternate ordinary adic transfer but uses a transported
monoidal structure; it does not itself close the native comparison coherence.

The corresponding Sheaf theorem is also unproved: origin/iface-start:
lean/Sheaf/Paper/NativeProperKFlatPullTensorSquare.lean,
AlgebraicGeometry.ProEtaleWeilSheaf.native_proper_kflat_pull_tensor_square.
Its condensed-only analogue is proved, but it does not supply the native square.
Added a small generic tensor-square representative extensionality helper, ported
from the surrounding Sheaf proof, for the eventual K-flat normalization proof.

2026-11-05 02:30 CST: Added proof candidates for the tensor-generator unit
formulas, the adic/condensed sheaf pullback tensor square, and its native/total
versions. The proof transposes through the pullback adjunction, then uses the
monoidality of lowerStarForgetAbIso. Ported the generic ordinary tensor
normalization lemmas from pr/2087 under distinct names to keep its future merge
clean. Remote uchecks are queued behind K6; no compilation feedback yet.

2026-11-05 02:38 CST: Full proof candidate now replaces the relocated coherence
sorry, with seven small helper modules. The original assigned theorem's statement
is byte-identical to 19ba966718. Reviewed LEAD route B: the Sheaf compact projection
user reaches the same K-flat tensor-square sorry through proper_projection, so it
does not bypass the gap. Added a declaration-level dependency audit for the final
validation. All three ucheck requests remain queued; the single shared tree is
currently building K1 after successful K6/K3 builds. No heartbeat raises or local
Lean/Lake runs.

2026-11-05 02:37 CST: A second shared tree opened; the full leaf check has
started on fe888fc3e9 in slopci-w5. Log:
/home/ubuntu/u9/logs/K5-20261105T023641.log. Pending compiler feedback.

2026-11-05 02:46 CST: First compiler feedback from K5-20261105T023641.log:
OrdinaryTensorNormalization is GREEN (7.7s). TensorSquare needed explicit
whiskered components before rw; SheafTensorUnit needed homEquiv_id instead of
simplifying homEquiv_unit. Both fixed and pushed in aa4dc89dc. The existing
pr/2086 NativePullTensor is still compiling (about 8 minutes, ~1 CPU). Stopped
the duplicate later full check on w3 to free shared capacity: rc=143, log
/home/ubuntu/u9/logs/K5-20261105T024008.log, same two already-fixed errors.
The original full check continues on w5; the minimal AdicSheafTensorSquare check
remains queued and will fetch the corrected branch.

2026-11-05 02:48 CST: NativePullTensor PASSED after 495s. First full leaf
check completed rc=1 with precisely the two already-fixed helper errors, log
K5-20261105T023641.log. Canceled the older pending minimal request and consolidated
validation into a fresh ucheck of Projection.AxiomAudit, which depends on the leaf
and all eight new helper/audit modules.

2026-11-05 02:50 CST: Second check log K5-20261105T024835.log, rc=1.
TensorSquare, OrdinaryTensorNormalization and SheafTensorUnit all GREEN.
AdicSheafTensorSquare had two deterministic 200000-heartbeat elaboration timeouts
at redundant placeholder-heavy change steps, and a rewrite mismatch between
adicUpperStar.obj.X and the ambient pullback. Removed those change steps and
normalized both spellings before the rewrite; no heartbeat increase.

2026-11-05 02:53 CST: K5-20261105T025124.log rc=1, adic square now elaborates
in 16s with no timeouts. Remaining issues are identity/composition normalization:
used explicit mate components, ordinary-transparency identity cancellation, and
rfl for the final strict forgetting/pushforward square. Rechecking the audit.

2026-11-05 03:00 CST: K5-20261105T025344.log rc=1. AdicSheafTensorSquare
GREEN in 19s. NativeSheafTensorSquare hit two explicit kernel deterministic
timeouts (256s total), at the concrete horizontal-iso component lemma and the
sheaf square. Factored horizontal identity elimination and square rotation into
an abstract helper; no heartbeat increase. Also corrected dependency audit to
report hidden imported bodies and added the coproduct-preservation instance
needed by totalization. Rechecking.

2026-11-05 03:08 CST: Generic SheafSquareTransport GREEN (<1s), but native
wrapper still has the same two kernel timeouts (K5-20261105T030309.log,
243s). The proof tactics now elaborate without errors. Running a synchronous
profiler/diagnostics check through ucheck to locate the kernel conversion; no
kernel skipping, no heartbeat increase.

2026-11-05 03:22 CST: Synchronous profile K5-20261105T031710.log (237s,
rc=1) confirms kernel costs: alpha component 1.15s elaboration/~104s kernel;
sheaf square ~5s elaboration/122s kernel. Trace identifies concrete conversion
adicUpperStarCompCondensedModIso.inv versus .symm.hom as expanding the conjugate
isomorphism, including limits/sheafification/geometric fibres. Added inverse-
spelled generic component identity and a natural-component version of square
rotation to avoid converting concrete Iso.app/mapIso projections. Rechecking
with profiler retained temporarily; no heartbeat changes.

2026-11-05 03:28 CST: K5-20261105T032307.log rc=1 (242s), same kernel
failures. Matching inverse spellings exposed the remaining difference: the two
adic pullback maps have distinct generated proofs of comp_over, so equality of
their .inv components unfolds the whole conjugate construction. Applying the
repository's exact_mod_proofs tactic at explicit, structurally aligned boundaries
to cast those proof arguments before kernel conversion. This tactic generates
ordinary equality/proof-irrelevance terms; no trusted checks bypassed.

2026-11-05 03:44 CST: New-server log K5-20261105T033542.log rebuilt the
PR2086 closure (NativePullTensor 375s; all prior helpers green). The isolated
transparent proposition SheafPullTensorSquare itself hit kernel timeout after
127s: this proves the remaining bottleneck is in the concrete statement's object
conversions, not in proof tactics. Replaced its body with an instantiation of a
generic PullTensorSquare predicate, and likewise abstracted the inverse square.
No opaque definitions, skipped checks, or heartbeat increases. The ucheck wrapper
reported a shell EOF error after the actual failed Lean build; checking wrapper
syntax before the next run. Also simplified derived symmetry using the existing
mapDerivedCategorySquareIso_symm theorem instead of concrete unfolding.
