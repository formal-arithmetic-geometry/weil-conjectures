## What changed

Proved `AlgebraicGeometry.ProEtaleWeilSheaf.native_ordinary_tensor_model_resolution_roof`
without changing its signature or any public import. Only the item module and its own
DAG node change. The proof imports the existing ordinary-total tensor comparison privately
and the source reduced flat-resolution API privately.

Use one reduced functorial flat resolution on the actual native module category
`ProEtale.AdicSheaf l Y`. Its resolution functor has categorically K-flat values and its
augmentation is a natural quasi-isomorphism. For an acyclic complex N, apply tensorRight
of a resolution value to the quasi-isomorphism from zero to N. Its source is acyclic by
additivity, hence its target is acyclic. The proved ordinary-total comparison transfers
this to exactly `NativeOrdinaryKFlat`. The same functor resolves both inputs and maps g;
augmentation naturality gives a strictly commuting square, and `Homotopy.ofEq` supplies
the requested homotopy. No common-refinement choices or extra existence lemmas are needed.

The proof uses the generic source construction underlying
`lem-sfb-unbounded-kflat-resolution-existence` and the module-object flat-cover instance
`lem-sfb-modobj-flat-resolutions` as tools. These already proved results apply directly
to this Grothendieck abelian module category and preserve functoriality on complexes.
`GenericOrdinaryTensor.ordinaryTotalIso` from
`Sheaf.Paper.NativeOrdinaryTensorRepresentatives` is reused through `import all` solely
in the theorem proof; no private helper enters a public signature or definition.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtaleWeilSheaf.native_ordinary_tensor_model_resolution_roof`
(node `lem-sf-native-weil-tensor-resolution-roof`).

Holes closed: 1. Holes added: 0. Holes left in the delivered module: 0.
No split-off theorems or modules.

Validation: the full proof compiled in 11.6 seconds. The theorem-scoped
`linter.unusedVariables` setting suppresses warnings about the original existential
proof binders without renaming them or changing the statement. The delivery tool
also compiles the final file with its axiom probe. The dependency graph below the
updated item is acyclic, and every Lean line is at most 100 characters.

## No longer needed

The proof does not use the planned dependency `lem-pc-kflat-resolution`, whose module is
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`; that dependency is removed
from this node's `proof_deps` and proof steps. It is a sheaf-of-modules existence theorem,
whereas the native category has an existing functorial module-object resolution directly.
The planned homotopy-category common-refinement argument and its second K-flat replacement
are unnecessary: naturality gives strict equality already. No previously present Lean
import is removed and no existing module or declaration is withdrawn. Other consumers of
the independent-coefficient resolution theorem remain unaffected.

## Where the brief, the DAG or earlier work was wrong

The statement is correct, including unbounded complexes, zero maps, zero complexes, and
an empty scheme. The planned fraction-calculus argument is longer than necessary.
The existing reduced flat-resolution functor produces the two required resolutions
simultaneously and lifts their map naturally. The DAG proof and proof origin are updated
to record this route; the owning unit's statement and realized steps are unchanged.
The specialized module-object theorem for abelian sheaves was inspected but is not used:
the native category here consists of module objects in sheaves of Weil coefficients.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeOrdinaryTensorModelResolutionRoof": "c743cfcc42f877a6649befe2af9e81923de28097"}, "results": {"Sheaf.Paper.NativeOrdinaryTensorModelResolutionData": {"hash": "1d8c0806bd1ed91d5fdc588b24dca8e5c96bbf83", "status": "OK"}}, "seconds": 84, "time": "2026-10-28T10:23:59+0800", "transitive": 0, "version": 1}
```

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
