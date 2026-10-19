## What changed

Proved `WeilConjectures.IntegralSystemRealization.Recursion.integralRealizationRecursion`
in `Sheaf.SixFunctors.IntegralRealizationRecursion`, preserving every existing signature,
definition and public import. Added proved private helpers for characteristic and prime
invertibility, the actual counit/unit, proper/open comparison cancellation, tensor counits,
and the structural recursion equations. Uniqueness is a second structural induction using
componentwise equality of natural isomorphisms.

Replaced the proof-only import `Sheaf.Paper.NormalizedDVREffectivity` with
`Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`, whose existing
`purNormalizedReconstruction` directly gives the actual counit isomorphism for normalized
systems. Added proof-only `Mathlib.Algebra.CharP.CharAndCard` for the finite field's
characteristic. Updated the node's proof route to match these arguments.

Validation: the delivered module compiled cleanly through `lcompile.py` in 16.4 seconds.
The proof handles all BasicTree constructors, including two independent tensor children;
compact-support constructors are excluded by the unchanged predicate. No finite evaluation
is used to infer equality. The single-variable construction uses `ULift Unit` so it works
in the prescribed universe. No target, consumer, or exported definition was changed.

## Proved and sorry left

Closed 1 hole: `WeilConjectures.IntegralSystemRealization.Recursion.integralRealizationRecursion`
(node `lem-pur-integral-realization-recursion`). Added 0 holes; split off 0 statements.
There are no remaining `sorry`s in the delivered module. All private helpers are proved.
This is a proof from the existing declarations; the imported reconstruction theorem's
existing hole is not claimed closed by this delivery.

## No longer needed

Removed the direct proof import `Sheaf.Paper.NormalizedDVREffectivity` and the direct
proof dependency `lem-coef-normalized-dvr-effectivity`: the existing normalized
reconstruction theorem packages the same actual-counit argument. Effectivity remains
needed transitively by reconstruction, so its module is not claimed globally pruned.

No public import is removed. The generator-reduction module supplies the unchanged
single-operation definitions, and the realization package supplies the specified maps
and their normalization equations. No other planned dependency is pruned. There are no
new modules or nodes. The unit route remains coefficient reconstruction followed by
operation comparisons and tree induction.

## Where the brief, the DAG or earlier work was wrong

The existing Lean `Realizations` record already exposes inputNormalization, the pull,
push, shriek and tensor equations, and openNormalization. Thus the transpose construction
need not be repeated: cancellation of the actual invertible counits proves the requested
formulas directly from those recorded equations. The existing
`lem-pur-normalized-reconstruction-adjunction-calculus` supplies the same normalized
counit statement the original first proof step wanted to derive from effectivity. It is
used only for that coefficient reconstruction step, not to bypass a geometric unit.
Mathlib adjunction/isomorphism cancellation handles the remaining glue. Prior search
results are in the dispatch sandbox's searches.jsonl; they found generic derived
adjunction infrastructure but no domain-specific recursion theorem.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
