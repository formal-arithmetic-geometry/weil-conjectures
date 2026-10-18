## What changed

Proved the seven consistency theorems in `Sheaf.Paper.IntrinsicKoszulCompletion`.
Local bijectivity is inherited from commutative-ring sheafification after forgetting
structure. Constant module sheafification preserves zero maps on underlying abelian
sheaves. Naturality of contraction under the diagonal exterior map proves the
Koszul power transition. The constant unit is constructed from its global section
using `unitHomEquiv`, which also proves uniqueness. Extension by zero proves its
closedness. The total differential formula proves the tensor-unit chain-map law.
Degree-zero exterior naturality proves compatibility with the tower transitions;
product extensionality gives `a ≫ (1-s) = 0`, and the shifted-cone differential gives
the final chain-map law. All auxiliary lemmas are private and proved.

Validation: the complete module compiles through `lcompile.py` (18.8 seconds),
with no warnings and no `sorry`. Every line is at most 100 characters.

All existing signatures, visibility, docstrings, public imports, and definitions
are preserved. The argument is uniform in the empty generating family and permits
zero divisors and unbounded complexes. No regularity or additional completeness
hypothesis is used.

## Proved and sorry left

Closed 7 of the module's 7 original holes, all in namespace
`AlgebraicGeometry.Scheme` and attached to
`def-weil-pbc-intrinsic-koszul-completion`:

- `koszulConstantUnit_local`.
- `koszulConstantFunctor_preservesZero`.
- `koszulPowerTransition_comm`.
- `koszulConstantOne_exists`.
- `koszulSheafUnitZero_closed`.
- `koszulTensorUnitComponent_comm`.
- `koszulCompletionUnit_comm`.

Holes left: none. Holes added: none. Split-offs: none.

## No longer needed

Removed the four unused proof-only imports:

- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `def-weil-derived-limit` is not needed to construct the specified concrete cone.
- `Sheaf.Algebra.Homology.KFlatResolutionGeneral`:
  `lem-pc-kflat-resolution` is not invoked because the representative is supplied
  as an argument. Its type is already supplied through the retained public imports.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`:
  `lem-weil-proetale-countable-products-exact` is not needed for existence of the
  termwise product or for the chain-map identities; exactness is needed for its
  derived interpretation elsewhere.
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts` (a retired re-export of
  `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts`):
  `lem-weil-derived-limit-products-core` is not needed for this concrete definition.

These mathematical interpretation dependencies remain in the definition node's
statement dependencies; no unit route or meaning of the construction is changed.
All public imports remain. No other modules or nodes are bypassed by this proof.

## Where the brief, the DAG or earlier work was wrong

The definition node has no numbered proof plan; the seven theorem docstrings give
its implementation obligations. All seven are true and admit direct proofs from
the existing concrete APIs. The source's `KoszulOpenSystem` confirms the exterior
contraction argument, but importing its affine derived-category infrastructure is
unnecessary: its elementary induction is used locally.

The four original unused proof imports also caused unresolved universe constraints
when elaborating tensor instances inside proofs. Removing them, as required by
pruning, resolves the ambiguity without changing any definition or interface.
No statement dispute, definition repair, or forced consumer adaptation was needed.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
