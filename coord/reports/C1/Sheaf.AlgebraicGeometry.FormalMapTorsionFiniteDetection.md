## What changed

Repaired the returned delivery of
`Sheaf.AlgebraicGeometry.FormalMapTorsionFiniteDetection`.
Removed the two duplicate private declarations
`AlgebraicGeometry.exactness_independent_zero` and
`AlgebraicGeometry.preadditive_unique_of_abelian`.
Both matching declarations in `GrothendieckExistenceProjective` are private,
so importing that module cannot expose them. The proof now uses Mathlib's
`CategoryTheory.subsingleton_preadditive_of_hasBinaryBiproducts` directly.
It transports the exactness hypothesis with `congrArg₂` and
`Subsingleton.elim`, quantifying over the zero-preservation witness so that
the transport is well typed. No replacement generic helper is introduced.

The sole remaining private helper is
`AlgebraicGeometry.kernel_quotient_projection_isIso`, proved without holes.
The theorem transports the actual coherent kernel fork by exact completion,
factors the difference through it, cancels the separating quotient at level n,
and uses naturality to show vanishing at all levels. Formal kernels are never
identified with termwise kernels. Abelian witnesses supply categorical structure;
no arbitrary geometric object is chosen from an unproved existence theorem.

The public signature and visibility remain unchanged. The four proof-only
imports remain: `FormalCompletionExact`, `CoherentKernelCokernelSum`,
`CoherentFormalModuleKernelFactorization`, and Mathlib's
`ShortComplex.ExactFunctor`. The node's proof, proof dependencies and origin
follow this categorical argument; the repair adds structure-transport details.
No other module, definition or public interface changes.
The former second reading predates this repair and is removed for a fresh reading.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.formalMap_torsion_finite_detection`
(node `lem-weil-pbc-formal-map-torsion-finite-detection`).
One of one holes closed; zero holes added or split off. No delivered Lean
declaration contains `sorry`. This proof uses existing library statements;
it does not claim their entire transitive dependency closure is sorry-free.

The repaired module compiles without warnings through `lcompile.py`.
The delivery dry run uses `--no-push`; this worker does not deliver.

## No longer needed

No imports removed and no modules pruned. The two duplicate private helpers
are removed, using existing Mathlib uniqueness results instead.
The old DAG plan's direct dependencies
`lem-weil-pbc-coherent-formal-modules-affine` and
`lem-weil-pbc-completion-exact-finite-modules` are replaced by
`lem-weil-pbc-formal-completion-exact`. They remain transitive dependencies
of that theorem, so neither module is claimed pruned. All four proof-only
imports are used. The unit's realized statement and steps remain untouched;
this auxiliary node is below the unit level.

## Where the brief, the DAG or earlier work was wrong

Return point 1: the prior delivery duplicated two private helper statements
already present in `GrothendieckExistenceProjective`. Both are now removed.
The existing private declarations cannot be used by import; their underlying
Mathlib uniqueness results are used directly without changing another module.

The old affine proof plan needs more glue than categorical completion
exactness. The separating monomorphism factors through every kernel quotient
at m >= n, making its projection both mono and epi, hence invertible.
Thus hker is redundant for this statement; its binder remains unchanged.
The argument handles n=0, zero/unit ideals, zero kernel and empty scheme
without positivity or a nonempty affine cover. Exactness applies in the
formal category, with no claim that evaluation preserves kernels.

No new nodes, changed statements, forced adaptations or new holes.

## Second reading by C1

1. **Interfaces: PASS.** Diffed the sole delivered module and its node against
   the repository. The full existing theorem signature is byte-for-byte identical,
   including Noetherianity, positive-power kernel torsion, the separating mono,
   both formal maps, comparison equality and level-n equality. Its public visibility
   and the sole public import are unchanged. No definitions or other modules change;
   no change record is needed. The rewritten docstring describes the actual proof.
2. **Proof and axioms: PASS.** Compiled the module locally using `lcompile.py`:
   no errors or warnings. Inspected the entire proof and scanned for forbidden
   declarations and holes: none occur. Refreshed and compiled the scratch copy with
   `#print axioms` for both declarations. The private quotient-projection helper uses
   only `propext`, `Classical.choice`, `Quot.sound`; the public theorem additionally
   uses `sorryAx` from existing dependencies, as permitted for an open import closure.
   Exactness transports the actual coherent kernel fork, not a termwise kernel.
   The selected abelian witnesses provide structures whose relevant preadditive
   operations are unique; kernel objects are constructed as the ordinary kernel
   with a coherence proof. No arbitrary geometric witness is chosen.
3. **Split statements and small cases: PASS.** Zero new holes, zero split-off
   statements and zero new nodes. Checked the private helper mathematically:
   the quotient projection factors the assumed mono, is therefore mono, is epi
   as a cokernel projection, and is invertible in the abelian module category.
   This is strictly an elementary part of the argument, recorded in node step 1.
   At n=0 no lower levels exist; equal levels use identity transitions. Zero J,
   the unit ideal, zero kernel and the empty scheme require no extra hypotheses.
4. **Shortest route, imports and pruning: PASS.** Read the three imported Sheaf
   dependencies and Mathlib's exact-functor criterion and uniqueness instance.
   Independently searched the library for quotient/kernel and detection variants;
   Loogle returned `CategoryTheory.Functor.preservesFiniteLimits_tfae`, an alternative
   criterion in the same Mathlib module, with no reduction of the required structure
   transport or kernel argument. No duplicate generic helper remains. All four
   proof-only imports supply used declarations; the public import supplies the
   signature. The report lists both old proof dependencies no longer used directly;
   these remain transitive through exact completion, so no module is claimed pruned.
   Read `dag/units/sk-thm-p1.json`, including its realized statement and all steps:
   this auxiliary node is not a realized unit step, and the unit route is preserved.
5. **DAG: PASS.** Diffed the node and checked its proof against the Lean from
   kernel quotient invertibility through coherent kernel closure, exact completion,
   the kernel lift, level-n cancellation, higher transition cancellation, lower
   transition epimorphy, and extensionality. Its three proof dependencies match
   the declarations used; the kernel-factorization module is used specifically for
   `formalTransition_epi`. Only proof, proof_deps and proof_origin change.

Second reading changed only this report and the scratch axiom check, removing stale
checks for the two already deleted private helpers. No delivered Lean or DAG repair
was needed. Confirmed one original hole closed, zero holes added, zero split off;
this is a local proof from existing library results, not a claim of a closed
transitive axiom closure.
