## What changed

`Sheaf.Paper.DiagonalCyclicUniformizerSource` now constructs the ordinary restriction
comparison and proves its uniqueness. The inverse finite-realization underlying
isomorphisms give the natural isomorphism of abelian sheaves. The cyclic inverse
realization is killed by `l^(n+1)`, so automatic condensed integral linearity lifts
that comparison to modules. Faithful forgetting gives naturality and uniqueness.
The original theorem combines this construction with the supported source equation.
Its signature and public import remain unchanged.

The proof imports two new modules: `CondensedPadicTorsionLinearity` proves the
linearity criterion using the existing reduction cokernel; and
`DiagonalCyclicUniformizerSourceEquation` states only the remaining derived endpoint
calculation for an already given normalized comparison. No existing dependency or
consumer is modified. The original DAG proof records the new route.

## Proved and sorry left

Original holes: one, `diagonalCyclic_uniformizerSource`.
Its body is now complete Lean, using the new endpoint theorem. Added holes: one,
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCyclic_uniformizerSource_equation`,
node `lem-diagonal-cyclic-uniformizer-source-equation`. This is a decomposition,
not a net hole closure: one upper hole removed, one lower hole added.

Fully proved with no new holes:
`AlgebraicGeometry.ProEtale.condensedPadicTorsionLinearity`, and the private
ordinary comparison existence, naturality, normalization and uniqueness arguments.
No `sorry` remains in the item module. The only `sorry` in this delivery is the
public endpoint equation just named.

The remaining equation is strictly the original proof's step 2. It assumes the
normalized comparison rather than constructing it, and asserts neither its
existence nor uniqueness. The substantial ordinary comparison construction and
its torsion-linearity justification are proved in this delivery.

## No longer needed

No existing import is removed and no module or node is withdrawn. The source and
root-frame definition dependencies remain available through the unchanged public
signature. The ordinary comparison does not need an additional equality of the
two coefficient actions: the stronger bounded-torsion linearity criterion supplies
it directly. No root-line endpoint or diagonal-class equation is used.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was found. The original step 1 can be
proved uniformly by the joint epimorphism given by the integral unit and
multiplication by `l^r`, rather than a separate coefficient-map factorization
argument for each inverse realization. The empty-scheme and zero-ring cases need
no extra assumptions. The linearity lemma also includes exponent zero: the target
is then zero because it is killed by one.

## New nodes

`lem-condensed-padic-torsion-linearity`, in
`Sheaf.Paper.CondensedPadicTorsionLinearity`, is fully proved. The pulled-back
integral reduction cokernel and cyclic unit epimorphism imply that the unit and
multiplication by the prime power jointly cover the integral ring. Tensoring this
cover proves linearity of an arbitrary additive map into bounded torsion.

`lem-diagonal-cyclic-uniformizer-source-equation`, in
`Sheaf.Paper.DiagonalCyclicUniformizerSourceEquation`, isolates the supported source
equation for an existing normalized right-functor comparison. Its docstring gives
the adjunction transpositions, endpoint normalizations, ordinary constant-map
comparison and sheafification argument needed to finish it. It does not assert
existence or uniqueness and does not duplicate the parent statement.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CondensedPadicTorsionLinearity": "0ad0db253ace2dbd147e7881a9d768a72e9e167d", "Sheaf.Paper.DiagonalCyclicUniformizerSource": "126d416d952401d0096cc2d2e98b9ea1fbae65cb", "Sheaf.Paper.DiagonalCyclicUniformizerSourceEquation": "9c665c9f28f408ada1680ee5b9074bd96a874720"}, "results": {"Sheaf.Paper.DiagonalCoefficientSourceSquare": {"hash": "385d02e5154ce999fa7205b4fb8f0c191e20bfab", "status": "OK"}}, "seconds": 83, "time": "2026-10-28T14:58:06+0800", "transitive": 0, "version": 1}
```

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
