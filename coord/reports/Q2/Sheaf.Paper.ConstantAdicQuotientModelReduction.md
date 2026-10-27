## What changed

Added `Sheaf.Paper.ConstantAdicQuotientModelExtensionIso`, which isolates the
geometric/algebraic comparison as a strictly smaller derived scalar-extension
isomorphism statement.  The target module now constructs the required arrow by
transposing that isomorphism through
`ConstantScalarRealization.moduleDerivedAdjunction`; its Hom-bijection proof is
complete and uses only categorical composition, the inverse of the isomorphism,
and adjunction naturality.  The target statement is unchanged.

## Proved and sorry left

Closed the sorry in
`AlgebraicGeometry.Scheme.constantAdicQuotient_model_reduction`.

Added one strictly smaller sorry theorem:
`AlgebraicGeometry.Scheme.constantAdicQuotient_model_extension_iso`.
It is the algebraic derived-extension isomorphism extracted from the geometric
comparison portion of the original proof plan.

## No longer needed

The target proof no longer directly imports or cites the geometric normalization,
stalk, completion, or tensor-pullback declarations.  Those declarations remain
needed by the split extension-isomorphism theorem, so no existing dependency
node or source module was pruned from the library.

## Where the brief, the DAG or earlier work was wrong

The original proof steps bundled the geometric comparison and the categorical
universal-property argument into one target.  The latter is independent once an
extension isomorphism is supplied.  Extracting that comparison as a separate
statement makes the target proof a genuine adjunction argument and leaves the
remaining geometric work as a strictly smaller node.

## New nodes

- `lem-weil-pbc-constant-adic-quotient-model-extension-iso`
  (`Sheaf.Paper.ConstantAdicQuotientModelExtensionIso`).

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ConstantAdicQuotientModelExtensionIso": "84c3efda939b7f1862a7986cf8df0a15b0d1a963", "Sheaf.Paper.ConstantAdicQuotientModelReduction": "35546e20b7fd16f6e5dbef86ff0526a99dc8894e"}, "results": {}, "time": "2026-10-28T00:20:33+0800", "transitive": 0, "version": 1}
```

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
