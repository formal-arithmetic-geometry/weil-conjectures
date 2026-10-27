## What changed

Replaced the single hole in `WeilConjectures.integralDerivedPullback_linear` by
an argument for the existing normalized functor and its existing comparison.
All public imports, signatures and definitions are preserved. The proof-local
command changes are documented in
`coord/changes/X6-integral-derived-pullback-linear-proof.md`. The proof adds
private imports of `IntegralOperationsWellDefined`,
`IntegralScalarExtensionWellDefined` and `IntegralConstructibleLinear`, using
`import all` to reuse their proved private normalization and localization helpers.

On finite coefficients, reduction and inverse image preserve the constant scalar
endomorphisms by their adjunctions: their right adjoints preserve those
endomorphisms sectionwise. Restriction of scalars preserves them by the finite
residue specification of `integralScalarConstant`. The termwise composite is
therefore linear for the completed coefficient action. The diagonal product and
mapping-cone maps defining Roos preserve sums and scalar multiples, as does its
shift. Additivity descends using binary biproducts and essential surjectivity of
the good-complex localization; the scalar equation descends by full faithfulness
of precomposition with that localization. The existing comparison identifies
this descent with the published pullback.

## Proved and sorry left

Original holes: 1. Closed: `WeilConjectures.integralDerivedPullback_linear`
(`lem-sf-integral-derived-pullback-linear`). Added holes: 0. Remaining holes in
the item: 0. No split-off theorem or module is introduced.

The complete proof compiled cleanly through `lcompile.py` in 17.6 seconds.
Removed an unused private module-additivity adapter after that check;
`deliver3.py` recompiles the final file with its axiom/hole probe.
The required delivery checks and push are run by `deliver3.py`.

## No longer needed

No existing import is removed, and no module is withdrawn. The proof uses the
stated finite reduction, strict Roos construction, ambient constant scalar
normalization and good-complex localization. It does not require exactness of
finite inverse image: its adjunction suffices for additivity and scalar
compatibility. Thus `lem-pur-coefficient-pullback-exact` is not a direct proof
dependency of this node. Its module and declarations remain intact and are
still used elsewhere, including by integral-operation well-definedness.

## Where the brief, the DAG or earlier work was wrong

The current blueprint's `def-weil-derived-pullback-tensor-hom` has moved to
`sec-proetale-coefficients` and describes condensed coefficient operations
uniformly, rather than the old rational paragraph cited by this item's
historical docstring. This delivery proves the assigned, unchanged theorem
about the existing normalized finite-reduction/Roos construction. It does not
change that construction or identify it with the newer blueprint's operations.
The direct scalar calculation needs only the finite adjunction, not its
exactness theorem. The existing scalar-extension module already contains proved
generic helpers for biproduct additivity and scalar descent, so no additional
localization obligations need to be split off.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
