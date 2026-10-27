## What changed

Filled the proof of `AlgebraicGeometry.ProEtale.internal_first_residue_smallMap_pushout`
in `Sheaf.SixFunctors.ProEtale.InternalFirstResidueSmallMapPushout`, without changing
its statement or any definition. Updated its DAG proof to record the shorter argument.

The identity lower edge forces the upper map to be epi in the preadditive category
of abelian sheaves. Section-ring reconstruction forgets to the original additive
map, so the faithful additive forgetful functor reflects this epimorphism.
The adjunction induced by the continuous `AsSmall.down` and `AsSmall.up`
functors shows that the small-site pushforward preserves it. The transported square
commutes, and Mathlib's `IsPushout.of_horiz_isIso_epi` supplies its universal property.

Validation is blocked before the file is checked: `lcompile.py` returned a missing
mirrored dependency artifact, and both delivery attempts returned the missing
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf.olean` error. That artifact
now exists, but the failed result is cached. The local-to-server fallback only
recognizes the wording `failed to open file`, whereas Lean reports
`object file ... does not exist`. No delivery was pushed. The last proof edit
supplied explicit universes for the existing small-site continuity instance;
that edit still needs a successful compile and delivery validation.

Resumption check on 2026-10-26: the required initial `deliver3.py J1
Sheaf.SixFunctors.ProEtale.InternalFirstResidueSmallMapPushout` again failed
at the module header with the missing `Modules/Sheaf.olean` diagnostic above.
The supported standalone `lcompile.py` command also failed at the header,
reporting missing `WeilConjectures/Mathlib/CategoryTheory/Limits/HasLimits.olean`.
Both named artifacts currently exist in the shared mirror. Read-only inspection
of the launcher confirms that missing-object failures are cacheable, and its
fallback still recognizes only `failed to open file`, not Lean's actual
`object file ... does not exist` diagnostic. The dependency cache key includes
the publication stamp but not the restoration of individual mirrored artifacts.
No launcher files or cache entries were changed, and no delivery was pushed.
The retained proof has therefore still not been validated by Lean.

Resumption check (third dispatcher attempt, 2026-10-26): the required initial
delivery again returned `COMPILE FAILED (local), nothing pushed`, at line 5,
for missing `WeilConjectures/Mathlib/AlgebraicGeometry/Modules/Sheaf.olean`.
The supported standalone compile also returned exit code 1 at line 5 for
missing `WeilConjectures/Mathlib/CategoryTheory/Limits/HasLimits.olean`;
its result is `compile-results/6cc7d695ae98044760f00984.txt`.
Both artifacts were checked with `ls -l` and exist in the shared mirror
(768288 and 7672 bytes respectively). The launcher still caches these failures:
`cacheable` excludes timeouts and certain service errors, but not missing
object files. Its local-mirror fallback at `lcompile.py:427` still matches
`failed to open file` rather than the returned `object file ... does not exist`.
The proof, DAG, launcher, and compile caches were left unchanged. This is a
compile-service failure before elaboration, not a Lean proof diagnostic.
No delivery was pushed.

Resumption check (fourth dispatcher attempt, 2026-10-26): the required initial
`deliver3.py` again returned the cached missing `Modules/Sheaf.olean` error,
and standalone `lcompile.py` returned the cached missing
`CategoryTheory/Limits/HasLimits.olean` error in result
`compile-results/6cc7d695ae98044760f00984.txt`. Both artifacts still exist
in the shared mirror, with sizes 768288 and 7672 bytes respectively.
Read-only inspection confirms that the cache and fallback behavior described
above persists. Neither command is pending: both exited with code 1 before
proof elaboration. No launcher files, cache entries, or library files were
changed; the retained proof and node are preserved. No delivery was pushed.

Resumption check (fifth dispatcher attempt, 2026-10-26): the required initial
delivery again exited with code 1, `COMPILE FAILED (local), nothing pushed`,
for missing `Modules/Sheaf.olean`. The supported standalone compile exited
with code 1 for missing `CategoryTheory/Limits/HasLimits.olean`, returning
the same result file `compile-results/6cc7d695ae98044760f00984.txt`.
Both artifacts exist in the shared mirror (768288 and 7672 bytes respectively).
Read-only inspection still finds that `lcompile.py:427` matches
`failed to open file`, but not `object file ... does not exist`, and that
`cacheable` does not exclude these missing-object errors. Both requests have
finished; neither is pending or timed out. No proof elaboration was reached.
The proof and node were retained unchanged; only this report was updated.
No launcher files, caches, or shared repository files were changed.

## Proved and sorry left

Replaced the one original hole with an explicit proof (final validation blocked):
`AlgebraicGeometry.ProEtale.internal_first_residue_smallMap_pushout`
(node `lem-sfb-internal-first-residue-small-map-pushout`).

The retained source replaces 1 hole and adds 0; it contains 0 `sorry`s.
Validated holes closed: not established, because compilation fails at the
module header before elaborating the proof. There is no delivered commit.
No split-off statements or definitions were added.

## No longer needed

No imports, modules, or DAG dependencies were removed. The only declared
proof dependency, `def-sfb-integral-models-stacks-data`, remains needed for
`sectionMap`, `smallRing`, and `smallMap`.

A general construction of an equivalence between internal commutative ring
objects and section-ring sheaves, and a general preservation theorem for
pushouts under that construction, are unnecessary for this identity-edge
square. No existing declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old proof plan omitted the bridge from a pushout in abelian sheaves to
a pushout of reconstructed ring sheaves: an equivalence on ring objects
cannot directly be applied to the supplied additive pushout. The identity
lower edge gives a direct epimorphism argument that proves the exact statement.
No target, unit route, existing signature, or source-library declaration changed.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
