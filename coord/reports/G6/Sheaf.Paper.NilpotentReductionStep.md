## What changed

Proved `SheafOfModules.locallyConstantFiniteTypeModules_reduction_succ` in
`lean/Sheaf/Paper/NilpotentReductionStep.lean`, with its statement and public imports unchanged.
The proof constructs the quotient-layer short exact sequence, tensors it with a bounded-above
flat K-flat representative, identifies all three terms by chain isomorphisms, and applies
finite locally constant tensor and triangle closure over the quotient coefficient rings.
All supporting glue is proved privately in the same module; no other module is adapted.
The node now records these actual steps and dependencies. No definition or statement repair
was needed. The preflight requested a record for the added private proof scopes; see
`coord/changes/G6-nilpotent-reduction-private-proof-scopes.md`. The additive helper is used
only as a local instance. No consumer adaptation is needed.

## Proved and sorry left

Closed the original single hole in
`SheafOfModules.locallyConstantFiniteTypeModules_reduction_succ`
(node `lem-weil-pbc-nilpotent-reduction-step`). Holes closed: 1; holes added: 0;
holes remaining in delivered Lean files: 0. Nothing is split off.
All private helper declarations are proved. The complete module compiled successfully
through `lcompile.py`; delivery preflight provides the independent signature and axiom checks.
The proof uses the existing declared dependencies as permitted by stage 3.

## No longer needed

Removed the unused proof import
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` from the working packet.
Compared with the current shared module, the following proof imports are unnecessary:

- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat`: its definition is already publicly
  available through the retained specialized flat-replacement and K-flat modules.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`.

The last four generalize universes independently; the assigned statement has equal site and
coefficient universes and uses the existing specialized declarations instead. Their underlying
mathematical nodes (K-flatness, resolution, and derived extension) are still used, not pruned.
The retired duplicate imports `Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat` and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed` are not retained. Additivity is obtained
directly from the source `MonoidalFree` tensor functors.

The planned mathematical dependencies are retained. In particular, the sheafification
exactness leaf is supplied directly by its Mathlib tools, together with the existing
constant-presheaf helpers. No unit statement or unit proof step is bypassed. No claim is
made that a whole library module becomes unreachable globally.

## Where the brief, the DAG or earlier work was wrong

The planned tensor step is implemented over D=B/J^(n+1) using the flat quotient extension
P_D. Its outer terms are identified by actual chain isomorphisms and exact restriction,
so the conclusion retains quotient-linear local models throughout.
During this session the shared repository retired duplicate Flat and TensorClosed modules;
the delivery uses the retained source APIs. The original target signature is unchanged.
The earlier unimported sandbox draft `NilpotentReductionTriangle.lean` was never delivered
and has been removed; no new intermediate obligation remains.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
