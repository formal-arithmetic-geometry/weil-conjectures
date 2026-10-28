## What changed

The parent theorem `WeilConjectures.LocallyFiniteAdicRealization.normalizedFunctor_descent`
now has a complete assembly proof. It applies two newly stated, strictly smaller
obligations and combines them with `And.intro`.

The new modules are `Sheaf.Paper.LocallyFiniteAdicFunctorDescentHom` and
`Sheaf.Paper.LocallyFiniteAdicFunctorDescentImage`. They retain the source's finite-stage
realization, coefficient comparison, condensed flat calculus, local-freeness, and
filtered two-colimit interfaces for the two split obligations. The three delivered files
compile in import order with the required server compiler. The change record is
`coord/changes/E6-locally-finite-adic-functor-descent.md`.

## Proved and sorry left

Closed:

- `WeilConjectures.LocallyFiniteAdicRealization.normalizedFunctor_descent` (the parent
  hole, by assembly of the two split statements).

Added split obligations, each deliberately strictly smaller than the parent conjunction:

- `WeilConjectures.LocallyFiniteAdicRealization.normalizedFunctor_descent_hom`, the
  bijectivity of each derived Hom map.
- `WeilConjectures.LocallyFiniteAdicRealization.normalizedFunctor_descent_image`, the
  bounded-constructible essential-image equivalence.

Both split obligations remain `sorry` with their source and proof plan in their
module docstrings and DAG nodes. No other holes were added.

## No longer needed

The parent module no longer directly imports the seven proof-only modules used by the
original unsplit proof (`ContinuousRationalDerivedRealization`,
`RationalCoefficientCategoryComparison`, `CondensedFlatCoefficientCalculus`,
`CondensedFieldLfpLocalTriviality`, `CondensedQbarLfpLocalTriviality`,
`CondensedQbarFunctionCoefficients`, and `TwoColimit`). Their mathematics remains needed
and is imported by the corresponding split modules. No DAG node or declaration is
withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original node bundled the independent full-faithfulness and essential-image clauses
into one unresolved theorem. The Lean statement itself is sound; the issue was proof
granularity. The delivery records the decomposition explicitly and leaves the parent
statement unchanged.

## New nodes

- `lem-sf-locally-finite-adic-functor-descent-hom`: derived Hom bijectivity for the given
  normalized functor.
- `lem-sf-locally-finite-adic-functor-descent-image`: bounded constructibility exactly
  characterizes the essential image of the given normalized functor.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.LocallyFiniteAdicFunctorDescent": "5faeced6a7cc469b2c116417093b5ee54ffe2443", "Sheaf.Paper.LocallyFiniteAdicFunctorDescentHom": "c76d0d96a5b3965c03f128063397b74da34a311a", "Sheaf.Paper.LocallyFiniteAdicFunctorDescentImage": "8a92e1b1712cf1f01c253b089e04cce277e2c84b"}, "results": {"Sheaf.Paper.LocallyFiniteAdicConstructibleRealization": {"hash": "916ef6335a84737c7a527093bbdbd2477d597084", "status": "OK"}}, "seconds": 75, "time": "2026-10-28T08:05:00+0800", "transitive": 0, "version": 1}
```

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
