## What changed

Restored Sheaf.SixFunctors.ProjectiveLineExceptionalBaseChange from its rework quarantine
and repaired the deterministic timeout. Reused the existing derived-module proof
instances locally, preserved let bindings during cleanup, respected transparency, and
locally protected instCategoryDerivedCategory. The proved private helper now applies
the componentwise isomorphism criterion directly and disables implicit definitional
proof synthesis in its explicit cancellation simplification. All public and private
signatures, imports, definition bodies, docstrings, and the main theorem proof body
remain identical to the archive. The archive itself is untouched.

The unchanged projective-line proof uses the finite splitting and diagonal integrals,
the two presented adjunctions, the concrete counit base-change equation, and the mate
criterion. The node and unit route are preserved. The declaration is still valid over
arbitrary bases, including empty bases and zero coefficients; no assumption was added.

The restored original with profiling stopped at 120 seconds. After the repair the
item compiles cleanly through lcompile.py in 7.1 seconds. A subsequent joint check
compiled the item in 34.4 seconds and its unchanged direct consumer,
WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange, in 35.0 seconds.
Both meet the 60-second limit. The temporary consumer source was removed from the
sandbox. Profiling was removed.

Change record: coord/changes/C2-projective-line-exceptional-proof-context.md.

## Proved and sorry left

This is a zero-hole compile repair. Original holes: 0. Holes closed: 0. Holes added: 0.
Remaining holes in the delivery: none. The complete existing proof of
AlgebraicGeometry.Etale.projectiveLineExceptionalBaseChange is retained, with its
private mate criterion repaired. No new statement is split off. The existing imported
adjunction theorem remains a proof dependency; this delivery does not claim to close
holes in imported modules.

## No longer needed

None. No imports, declarations, modules, or DAG dependencies are pruned or withdrawn.
All three proof imports supply declarations used by the retained proof.

## Where the brief, the DAG or earlier work was wrong

The module's absence from lean/ is quarantine after a build timeout, not withdrawal.
The rework row identifies the original source and its dependencies; those are preserved.
The archived proof needed a local elaboration-context repair after its trace-counit
dependency changed. No mathematical error or unit-route departure was found.

Loogle and LeanFinder searches confirmed the general adjunction/mate API already used;
local searches found the existing finite trace-model equation and the same mate
criterion. No shorter mathematical replacement is needed for this compile repair.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
