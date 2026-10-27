## What changed

Replaced the one sorry in `WeilConjectures.ProductOpenTensorProjection.productOpenTensorProjection`
by the five-step argument of its node. The original theorem statement and Assertion are
unchanged. Three independent intermediate modules isolate the one-open counit normalization,
the supported product-open restriction calculation, and transport of the generic proper/open
projection equation to exact-pullback coordinates. All apply to ordinary unbounded objects;
no constructibility, Tor condition, or additional hypothesis is introduced in the item.

The original definitions move verbatim to `ProductOpenTensorProjectionData`, publicly
reexported by the original item, to let these statements share the actual named maps without
an import cycle. The change record is `coord/changes/H5-product-open-tensor-data.md`.

The item proves tensor bifunctoriality and its identity-map equations, naturality of the actual gamma and delta, full
faithfulness of open extension from its invertible adjunction unit, the projection equation
after postcomposition by d and the open compositor, the final identity after precomposition
by k_!(B0) tensor 1, and the two redundant restriction consequences. It obtains IsIso(e)
from the existing `finiteOpenProductSwap` declaration.

## Proved and sorry left

One of one original holes is closed by decomposition:
`WeilConjectures.ProductOpenTensorProjection.productOpenTensorProjection`
(node `lem-pur-product-open-tensor-projection`). No sorry remains in the item or shared data.

Three holes are added, each the whole proof of one public theorem in its own module:

- `WeilConjectures.ProductOpenTensorProjection.productOpenCounitNormalization`
  (`lem-pur-product-open-counit-normalization`), parent Step 1, for one arbitrary open.
- `WeilConjectures.ProductOpenTensorProjection.productOpenSupportNormalization`
  (`lem-pur-product-open-support-normalization`), parent Step 2, containing no proper projection
  or exchange map.
- `WeilConjectures.ProductOpenTensorProjection.exactProperOpenProjectionMate`
  (`lem-pur-exact-proper-open-projection-mate`), parent Step 3 before pasting d or B0.

This is a decomposition, not a net sorry reduction: one original hole closed, three added.
Each statement is strictly a part of the argument, with a source and complete proof in words.
The remaining main identities are derived by actual naturality and functoriality proofs in
Lean, rather than supplied as another restatement of Assertion.

## No longer needed

Removed the unused private proof import `Sheaf.Paper.ExchangeProjectionSuppliedDomains`
from the item. No original public import is removed and no existing module is withdrawn. No unit statement
or unit proof step is bypassed. The generic proper/open equation and open normalization
remain needed through the intermediate statements. The canonical open compositor remains
part of the supported product normalization. No global pruning is claimed.

The new data module imports only `FiniteOpenProductSwap` and `ProperOpenProjectionMate`;
it does not repeat the original statement-only imports for finite-type inputs and witnesses.

The boundedness and etale-origin witnesses are not needed by the calculations, as the
original docstring says; their original binders remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The node's natural-language argument suppresses transport
between exact and total left-derived inverse images, the open-unit normalization, and
composition-unit coherence. These are substantive named steps, not definitional equalities.
The three new statements make these gaps explicit without changing the five-step route.
Identity opens, empty opens, zero inputs, and odd-degree signed symmetries were checked in
the statements' proof plans. No inverse of chi or any proper projection map is taken.

## New nodes

`def-pur-product-open-tensor-projection-data` owns the definitions extracted verbatim from
the item; it introduces no new operation or mathematical choice.

`lem-pur-product-open-counit-normalization` is the single-open counit calculation and its
unit-normalized restriction equations, independent of product geometry.

`lem-pur-product-open-support-normalization` is the product support calculation, independent
of every proper pushforward and compactification exchange B0.

`lem-pur-exact-proper-open-projection-mate` is the generic proper/open equation transported
through canonical exact-pullback comparisons and the open unit. Naturality at d and B0 is
proved in the original item.

Change record: `coord/changes/H5-product-open-tensor-data.md`.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
