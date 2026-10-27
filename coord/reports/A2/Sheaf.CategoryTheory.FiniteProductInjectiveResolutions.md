## What changed

Proved `CategoryTheory.finiteProduct_injectiveResolutions` in
`Sheaf.CategoryTheory.FiniteProductInjectiveResolutions`, retaining its signature and all
public imports. Added the proof-only import `Mathlib.CategoryTheory.Abelian.Exact`.

The proof follows the node's componentwise argument. Private helpers construct the
pointwise preadditive structure, limits, colimits, normal monomorphisms and normal
epimorphisms, hence the abelian structure. Injectivity is equivalent to componentwise
injectivity by extending maps componentwise and, conversely, inserting a lifting problem
at one coordinate. Componentwise kernels and cokernels transfer exactness. The given
resolution complexes are assembled with their actual objects and differentials; the
augmentation is constructed from the given degree-zero maps using
`CochainComplex.fromSingle₀Equiv`. Its quasi-isomorphism follows from the kernel property
in degree zero and componentwise exactness in positive degrees. Choosing component
resolutions from the assumed `HasInjectiveResolutions` then gives that property for the
product category.

The construction also works for an empty index type and arbitrary index types; the
original finite-index hypothesis is retained. All helper declarations are private and
fully proved. No arbitrary resolution is selected from an unproved existence theorem:
the component resolutions used to establish existence come from the theorem's explicit
`HasInjectiveResolutions` hypotheses, and the prescribed-resolution clause constructs
its complex directly from the supplied family.

Validation: the complete file compiled through `lcompile.py` with no warnings.
`#print axioms CategoryTheory.finiteProduct_injectiveResolutions` reported exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Closed the sole original hole, `CategoryTheory.finiteProduct_injectiveResolutions`
(node `lem-weil-pbc-finite-product-injective-resolutions`): proved 1 of 1 original
sorries. Zero sorries remain; zero holes added or split off.

## No longer needed

None. All original public imports and both declared dependencies
`def-sp-abelian` and `def-sp-injective-resolutions` remain relevant. No nodes or modules
are withdrawn. The proof uses only Mathlib and the definitions underlying those leaves;
it introduces no further project dependencies.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The existing four-step DAG plan is realized
without changing the statement or dependency route. For componentwise limits and colimits,
the private construction allows the index universe and hom universe to vary independently;
Mathlib's `CategoryTheory.pi` helpers identify these universes. This is an implementation
detail, not a statement change.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
