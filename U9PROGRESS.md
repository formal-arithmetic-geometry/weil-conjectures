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
