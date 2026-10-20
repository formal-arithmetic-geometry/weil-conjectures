## What changed

Completed all six proofs in `lean/Sheaf/Paper/ProjectionFormulaArrows.lean`.
All existing public declarations, signatures, docstrings, public imports and
non-theorem bodies are preserved. Added proved private helpers and proof imports only.

The finite-free mate is identified with the finite-product comparison using its unit
case and naturality. The retract identities then prove degreewise invertibility of
the total mate. A finite-support coproduct argument handles the unbounded first
complex, and cancellation gives the specified inverse on each summand.

K-injectivity uses bounded triangulated devissage in the right orthogonal of acyclic
complexes. This works under the original general monoidal hypotheses and avoids
introducing a closed or symmetric structure on the generic categories.

The mixed representative uses the existing public K-flat resolution theorem, including
its degreewise epimorphic augmentation. Resolve the pullback of this augmentation
along any other resolution to obtain a common resolving refinement. Naturality of
the given tensor representative gives every required square; cancellation at the
chosen augmentation proves uniqueness. Tensor-cone compatibility proves that the
fixed K-flat coefficient preserves quasi-isomorphisms. This adapts the existing
common-refinement argument of `ProjectionFormulaCompactified`, which cannot be
imported here because it depends on this module.

For the strict-perfect package, finite free objects are dualizable, retracts are
flat, and the existing bounded-above flat theorem gives K-flatness. All newly added
helpers are proved; no statement is split off.

Local transparency attributes keep elaboration from expanding total complexes during
unrelated unification. Local priorities select the existing generic limit/colimit
instances directly, and a local witness caches the family of total-tensor instances.
The full file plus the delivery's axiom probe compiled in 30.5 seconds
(`fast-canonical-probe.log`), with `SHEAF-PROBED 16` and no forbidden axiom reported.
Its only warning is the appended tool probe's own overlong line, which the delivery
tool excludes. The delivered source has no overlong lines or diagnostics.

The required local-elaboration change record is
`coord/changes/P2-projection-formula-proof-elaboration.md`. It documents the local
attributes and removed private import; no public interface changes.
The copied definition node records the proof route; its existing specialized
pro-etale Lean attachment and its statement are unchanged.

## Proved and sorry left

Closed six original holes:

- `CategoryTheory.tensorAdjunctionMate_free_isIso`
- `CategoryTheory.tensorAdjunctionTotal_isIso`
- `CategoryTheory.tensorAdjunctionTotalInverse_summand`
- `CategoryTheory.tensorAdjunctionTotal_target_isKInjective`
- `SheafOfModules.mixedTensorRepresentative_existsUnique`
- `SheafOfModules.StrictPerfectCoefficientPackage.isKFlat_flat`

These implement `def-weil-pbc-projection-formula-arrows`.
Actual remaining hole count in the delivered Lean file: **0**.
Holes added: **0**. Split-off statements: **0**.
No definitions contain holes. No other Lean modules are changed.

## No longer needed

Removed the proof import `Sheaf.Algebra.Homology.SplitPerfectTensorKInjective`.
The generic K-injectivity assertion follows directly from the already-proved
homotopy-category tensor functor and bounded devissage. Thus this item's proof
needs neither its sheaf-specific tensor-dual construction nor the node
`lem-weil-pbc-split-perfect-tensor-kinjective` as a proof dependency.
The definition node's existing statement citation is preserved, and this is not
a claim that other consumers of that module can be withdrawn.

No other original import is removed. No new unresolved dependency or new module is
introduced. The proper-base-change unit statements and steps are untouched.

## Where the brief, the DAG or earlier work was wrong

The generic module's docstrings cite `def-weil-pbc-projection-formula-arrows`, but
that node currently attaches to `Sheaf.Paper.ProEtaleProjectionFormulaArrows`, not
the generic module. Its original proof field was empty. The delivery supplies the
proof description without changing that specialized attachment.

The first dry run detected a stale replacement of the public K-injective-resolution
re-export by its upstream module. Restored the current shared `Sheaf` re-export,
preserving all public imports. The same dry run requested a change record for the
local transparency commands; that record is included. A later compile-time failure
was repaired by using the public resolution theorem and common refinements instead
of importing the internal functorial-resolution machinery.

The original generic K-injectivity docstring proposed dualizing coefficients,
although its hypotheses do not assume a symmetric or closed monoidal category.
The bounded orthogonal/devissage argument proves the exact original statement
under its stated hypotheses. The original docstring is preserved as required.

After provider interruptions the launcher reset the reference metadata: the
previous recorded start was 1792451261.1896923 and the resumed `.budget` start is
1792498816.2660604. The worker did not edit budget metadata, and no elapsed-time
exception or unfinished split was used.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
