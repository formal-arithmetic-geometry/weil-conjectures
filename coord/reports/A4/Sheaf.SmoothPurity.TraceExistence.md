## What changed

Copied and compiled `Sheaf.SmoothPurity.TraceExistence`. Added an inline explanation of the
existing `STATEMENT-DISPUTED` marker: for the identity smooth morphism in relative dimension
zero, postcomposition by any automorphism of the coefficient unit is bijective on every Hom set,
so the displayed predicate does not determine a unique trace.

## Proved and sorry left

No sorry was closed. `AlgebraicGeometry.ProEtale.CondensedRing.existsUnique_smoothTrace` remains
one sorry because its uniqueness conclusion is false as stated. No new sorries were added.

## No longer needed

Removed the two unavailable proof-only imports
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek` and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition`. The statement and
its current disputed `sorry` do not use either module; retaining them prevented the returned
delivery from finding their source files on current main.

## Where the brief, the DAG or earlier work was wrong

The DAG and source docstring ask for an `∃!` representing morphism while the predicate only says
that postcomposition is bijective. Such a representing morphism is generally unique only after a
normalization is fixed. For `f = 𝟙 X`, `d = 0`, and `M = U` the identity, every automorphism of the
unit gives another map satisfying the same bijectivity condition. The source module already marks
this as `STATEMENT-DISPUTED`; proving a weaker existence theorem here would silently change the
contract and would not prove the assigned statement.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SmoothPurity.TraceExistence": "5c590c5d281b893eb8d55912cb91460b99b0a178"}, "results": {}, "time": "2026-10-28T09:06:38+0800", "transitive": 0, "version": 1}
```

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
