## What changed

Proved `WeilConjectures.RationalOperations.integralDualizing_exceptional_unit_bridge`
in `lean/Sheaf/SixFunctors/IntegralDualizingExceptionalUnitBridge.lean`, with its public
statement and existing public imports unchanged. Added private proof helpers and private
imports of `IntegralConstructibleReductionHom`, `CompactSupportTermHomFinite`, and
`Mathlib.CategoryTheory.CofilteredSystem`. Updated the item's DAG proof and dependencies.

At each exponent n+1, the recorded right coefficient comparison, finite-right realization,
and constant-unit reduction give an isomorphism to the prescribed finite dualizing term.
The finite-level isomorphism sets are finite and nonempty. Their successor descent maps
come directly from the normalized reduction adjunctions. Mathlib's finite inverse-limit
theorem chooses a compatible family, and the existing Roos/Milnor machinery reconstructs
its maps and inverses. Reconstruction uniqueness proves their inverse equations.

`successorReductionHom` is a private specialization of the already proved reconstruction
argument, repeating its proof with successor compatibility, which is the only compatibility
its Milnor-map proof uses. The proof imports the existing private transition, Hom-finiteness,
and Roos helpers with `import all`; no source-library or other project file is changed.

The complete candidate compiled through `lcompile.py` in 29.1 seconds before removing
its diagnostic output. The final delivery tool performs the clean compile and preflight.

## Proved and sorry left

Closed the one existing hole:
`WeilConjectures.RationalOperations.integralDualizing_exceptional_unit_bridge`.

Item holes: 1 before, 0 after. Holes added: 0. Split-off statements: 0.
Every added private helper is proved; every added definition is an explicit construction.
The proof uses existing library declarations, whose independent downstream obligations
remain with their modules.

## No longer needed

The proof does not need `prop-coef-integral-exceptional-adjoint`, attached to
`WeilConjectures.SixFunctors.Etale.Derived.IntegralExceptionalAdjoint`, as a direct proof
dependency. Removed it from this node's `proof_deps`; its pre-existing `stmt_deps` entry
is unchanged. This does not withdraw that source module or any of its declarations.

No existing Lean import was removed. `Sheaf.Paper.IntegralDualizingExceptionalUnit`
(the older `integral_dualizing_exceptional_unit` obligation) is not imported or used:
it reaches this item through RationalOperations and would create an import cycle.
No canonical-coherence split, new reconstruction obligation, or additional dualizing
existence theorem is needed. No module is withdrawn or claimed to be globally pruned.

## Where the brief, the DAG or earlier work was wrong

The old plan compressed normalized finite comparison and integral reconstruction into
one step. Also, `S.ring.finiteRight` supplies an isomorphism of functors without a
counit-normalization field; its arbitrary choices do not by themselves justify asserting
coherence of the particular finite isomorphisms built from it.

The actual conclusion is only `Nonempty` of an ambient object isomorphism. Finiteness of
constructible finite-coefficient Hom sets permits a shorter proof by compatible choice.
It uses `w.reduction` but does not need `w.coherent`; no hypothesis or conclusion changes.
The empty scheme, zero objects, and exponent-one reductions require no extra assumptions.
The current blueprint source is under sec-smooth-purity/sk-lem-sp-tower, rather than the
outdated sec-six-functors path in the node's unchanged source metadata.

The current server queue row was checked: stage 3, one hole, reason `proof`, route item.
There was no current rework row or build-error file for this module.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralDualizingExceptionalUnitBridge": "5bab0b8a6b84e3360f4968fcf971bee4d5291a9b"}, "results": {"Sheaf.SixFunctors.RationalDualizingIdentification": {"hash": "8bb3207e9be05e516b7361a4585430d9e198193c", "status": "OK"}}, "seconds": 52, "time": "2026-10-28T04:13:28+0800", "transitive": 0, "version": 1}
```

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
