## What changed

Proved `AlgebraicGeometry.Scheme.finitePerfectAdicOrdinaryScalar_compatibility` with its existing signature. The two sides are natural transformations whose common source is isomorphic to the ordinary target. A proved private helper establishes small-colimit preservation of that target, using the existing normalized scalar-extension adjunction. A second proved private helper extends equality on the regular module to arbitrary free modules by coproduct universality and then to every module by the canonical free surjection. All new imports are private proof imports. Updated the item node to this argument.

The proof imports `Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`, `Sheaf.Paper.FinitePerfectAdicConstantCohomology`, and `Mathlib.Algebra.Category.Grp.Ulift`. Redundant Mathlib imports were removed during development. The final file compiles through `lcompile.py` with no errors or warnings in 11.2 seconds, including the current unpublished ordinary-model-base dependency overlay. The theorem signature was compared verbatim with the original and is unchanged.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.Scheme.finitePerfectAdicOrdinaryScalar_compatibility` (`new-s3-finite-perfect-adic-ordinary-scalar-compatibility`). No holes added or split off; no `sorry` remains in the item. Both private helpers are fully proved. This is a proof, not a decomposition. The existing hypotheses and conclusion are unchanged.

## No longer needed

No existing imports or modules were removed. The former direct proof dependencies `def-weil-pbc-finite-perfect-adic-scalar-realization` and `lem-weil-pbc-completed-constant-algebra-flat-quotients` are not used by this proof and are removed from the item's `proof_deps`. Their unchanged declarations and their other consumers remain; in particular the ordinary model base still imports completed flatness for its separate exactness theorem, so this delivery claims no global module pruning. The proof needs neither finite presentations nor flatness of completed coefficients, only the explicit functors' colimit preservation and the given natural isomorphisms.

## Where the brief, the DAG or earlier work was wrong

The previous plan and existing theorem docstring claim a finite free presentation for every quotient-ring module. The statement does not assume that the module is finitely generated or finitely presented. Use the arbitrary free module on the underlying set instead; colimit preservation handles its possibly infinite coproduct, and epimorphism cancellation is enough, without presenting the relation module. This preserves all edge cases and the unit route.

The generic ordinary scalar-extension adjunction `lem-pur-sheaf-ring-coefficient-ordinary-adjunction` is used as a tool from another unit. It applies directly to the already specified object and morphism formulas of completed scalar extension, with no new chosen data. The maintainer may record this tool use if required.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FinitePerfectAdicOrdinaryScalarCompatibility": "3403b03ca8537f276473fe7c5b843b6a9d78aed5"}, "results": {"Sheaf.Paper.FinitePerfectAdicOrdinaryScalarModel": {"hash": "2a8c62c7f1a3f4be7dada4f7cc3c5baff3a2651b", "status": "OK"}}, "seconds": 85, "time": "2026-10-28T12:18:48+0800", "transitive": 0, "version": 1}
```

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
