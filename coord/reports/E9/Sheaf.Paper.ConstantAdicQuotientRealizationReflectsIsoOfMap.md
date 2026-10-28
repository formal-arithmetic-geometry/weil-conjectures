## What changed

Proved `AlgebraicGeometry.Scheme.constantAdicQuotientRealization_reflects_iso_of_map`
in `Sheaf.Paper.ConstantAdicQuotientRealizationReflectsIsoOfMap`, with its signature
unchanged. A proved private helper shows that constant module sheaves on a scheme
with a supplied point are faithful, using local equality under sheafification.
Existing proved coefficient-encoding comparisons identify the ordinary realization,
after encoding its target, with restriction of scalars followed by constant sheaves
on the nonempty chart. This makes the ordinary realization faithful and therefore
conservative. Its exact derived functor reflects isomorphisms by the natural
homology comparison and `DerivedCategory.isIso_iff`.

Added proof-only imports of `AdicLisseRelativeRestriction`,
`PbcFinitePullbackConstructibility`, `ProEtaleOperations` (all under `Sheaf`), and
`Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced`. The original public import
is retained. No other Lean file, public signature, definition, instance, attribute,
or public import was changed. The item's DAG proof now records the argument.
Its nonexistent `def-weil-pbc-constant-adic-quotient-scalar-comparison` reference
was corrected to the existing `lem-` node; see
`coord/changes/E9-constant-adic-quotient-realization-reflection-route.md`.

The complete file compiled successfully through `lcompile.py` in 20.5 seconds.
The proof covers arbitrary coefficient modules and unbounded complexes, including
zero rings, the zero and unit ideals, and disconnected nonempty charts. No stalk,
finite generation, connectedness, or quotient-map bijectivity is assumed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.constantAdicQuotientRealization_reflects_iso_of_map`
(node `lem-weil-pbc-constant-adic-quotient-realization-reflects-iso-of-map`).
There are zero remaining `sorry`s in the item and zero holes added elsewhere.
No statements were split off. The private constant-sheaf faithfulness helper is
fully proved.

## No longer needed

No original imports were removed and no whole modules were withdrawn.
The planned proof dependency
`lem-sfb-constant-realization-reflects-isomorphism`
(`Sheaf.CategoryTheory.ConstantRealizationReflectsIsomorphism`) is not imported
or applied: the exact faithful ordinary realization argument gives the derived
reflection directly. It is removed from `proof_deps`; its preexisting
`stmt_deps` entry is retained. No claim is made that its module is globally unused.
The proof also does not need the completion-quotient map's bijectivity, a stalk
construction, or any morphism-lifting or homology-lifting split.

## Where the brief, the DAG or earlier work was wrong

The DAG used the nonexistent node id
`def-weil-pbc-constant-adic-quotient-scalar-comparison`; the actual existing node
is `lem-weil-pbc-constant-adic-quotient-scalar-comparison`. The correction is solely
a reference correction and changes no mathematical statement or Lean signature.
The planned stalk argument is unnecessary: constant-section faithfulness and
exactness suffice. The unit statement and its realized proof steps are preserved.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ConstantAdicQuotientRealizationReflectsIsoOfMap": "ca791b241c2c0a344626e34232df1a4793ae3054"}, "results": {"Sheaf.Paper.ConstantAdicQuotientRealizationIsoLift": {"hash": "d6e067f4055721fccc4bf4439f2e0098aa320590", "status": "OK"}}, "seconds": 38, "time": "2026-10-28T12:13:16+0800", "transitive": 0, "version": 1}
```

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
