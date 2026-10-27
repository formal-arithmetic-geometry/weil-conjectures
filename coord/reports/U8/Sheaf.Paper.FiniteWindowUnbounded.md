## What changed

Proved both declarations in `Sheaf.Paper.FiniteWindowUnbounded` with unchanged
signatures and public imports. Two proved private helpers identify a single-degree
Hom group with Ext and combine strict-tail left-complete devissage with the
boundary-degree truncation triangle. The existing `constructibleInd_extBound`
supplies the sheaf Ext input for both coefficient choices.

Added proof-only imports: `Sheaf.Paper.ConstructibleIndExtBound`,
`WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp`,
`WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi`,
`WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`, and
`WeilConjectures.CategoryTheory.DerivedCategory.CompactOfBoundedExt`.

Exact countable products are obtained from the adopted pro-etale repleteness API
for abelian sheaves, transferred through the module-object forgetful functor.
Grothendieckness supplies K-injective resolutions. The existing fully proved
`DerivedCategory.eq_zero_of_isLE` handles the strict tail; the existing
`eq_zero_of_isGE_of_isLE_self` handles its boundary layer. The Hom exactness
combination is written in this module.

The temporary cohomology class is the union of ind-constructible sheaves with zero
objects. This changes no library definition or theorem hypothesis: it only makes
truncation closure immediate inside a private proof.

## Proved and sorry left

Closed two existing holes:
- `AlgebraicGeometry.ProEtale.finiteWindow_unbounded`;
- `AlgebraicGeometry.ProEtale.finiteWindow_unbounded_padicAlgCl`.

Zero holes remain in the item, and zero holes are added. The proof uses the
existing open theorem `AlgebraicGeometry.ProEtale.constructibleInd_extBound`
(node `lem-finite-window-ind-ext-bound`); it is neither changed nor duplicated.
The new node attaches an already proved source-library theorem and adds no Lean
declaration. This is a proof from an existing stated dependency, not a decomposition.

Validation: the server compiled both proofs in 10.6 seconds. The two letI-style
warnings were corrected to the linter-requested let form before delivery. Delivery
runs the final compile and axiom probes. Both public theorem signatures were
compared verbatim with the current source and are unchanged.

The boundary check includes d_C=0 (N=-1), zero objects, an empty scheme, and an
arbitrarily unbounded lower tail. The strict-tail lemma alone gives only degrees
<=-d_C-2: the final boundary triangle is essential to retain degree -d_C-1.

## No longer needed

Removed proof-only imports:
- `Sheaf.AlgebraicGeometry.ProEtaleLeftComplete`;
- `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived`;
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`;
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`;
- `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT`;
- `Sheaf.Paper.FiniteWindowBounded`.

The specialized nodes `det-pe-left-complete-iso`, `det-pe-products-derived`,
and `det-finite-window-bounded` are no longer direct proof dependencies of this
item. Their mathematics is supplied by the existing generic source-library
left-completeness and bounded-devissage proofs. The unit's bounded-devissage
and Postnikov-convergence route is retained. No module is withdrawn: other
consumers and unfinished parents may still need all these specialized results.
The explicit eventual-transition and 1-minus-shift recursion is unnecessary
because strict-tail devissage kills both relevant Hom groups before attaching
the boundary layer.

The truncation and representable-Hom nodes remain used, through the generic
source proof and the final boundary triangle; their existing tool approvals stay.
All public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

The original plan was mathematically valid, but the fully proved source module
`WeilConjectures.CategoryTheory.DerivedCategory.CompactOfBoundedExt` already
contains the generic lower-tail proof. Its theorem has a one-degree margin;
using it directly at N=-d_C-1 would miss the endpoint. The explicit boundary
triangle repairs that applicability gap without changing either statement.

The rework table lists the item as quarantined during an earlier build. Its
current source exists, and this delivery preserves both declarations and their
mathematical dependencies. No deletion or quarantine withdrawal is requested.

## New nodes

`lem-finite-window-abstract-strict-tail` records the existing, fully proved
`DerivedCategory.eq_zero_of_isLE` in the adopted source library. It states only
the abstract strict-tail step (upper bound N-1), under exact-countable-product
and degreewise Hom hypotheses. It is used together with a separate boundary
argument in the item. The source module is not modified or copied into the
packet. LeanSearch, Loogle, LeanFinder, Mathlib grep, source-library grep, and
blueprint lower-tail searches found no duplicate node for this abstract result;
the blueprint matches are the specialized bounded and unbounded assertions.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
