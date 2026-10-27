## What changed

Replaced the sorry in `WeilConjectures.exists_sfFiniteExceptionalOperations` by a
Lean assembly of the actual full-category restrictions and their bounds. The theorem's
signature is unchanged.

The support-preservation argument is proved directly from the existing open
extension-by-zero and pro-etale direct-image declarations. It gives both membership
and the exact Tor interval `[a,b+2d]`. The middle scheme receives the composite
structure map to the field; properness supplies finite type. `ObjectProperty.lift`
constructs the restricted functors on both objects and morphisms, so their inclusion
equalities are definitional.

Two remaining parts are stated separately: uniform intrinsic exceptional preservation,
and the normalized adjunction for already-given literal restrictions. The latter
supplies the left exact structure. Mathlib's `right_adjoint_additive`,
`commShift_of_leftAdjoint`, and `isTriangulated_rightAdjoint` then give right
additivity, both unit/counit shift compatibilities, and right exactness in the parent.
The selected right shift is definitionally `adj.rightAdjointCommShift`.

Moved the eleven existing realization declarations verbatim into the new
`ExceptionalFiniteRestrictionAdjunction` module, publicly re-exported from the item,
so both separate obligations can use the original formulas without an import cycle.
The change record `coord/changes/Y8-exceptional-finite-realization-relocation.md`
lists all 80 downstream modules; no consumer is adapted and
no definition changes meaning. No data definition uses either new existence theorem.

## Proved and sorry left

Closed the item's one original hole:
`WeilConjectures.exists_sfFiniteExceptionalOperations`
(node `lem-sf-exceptional-finite-operations`). Its proof is complete from named
statements, including the two split obligations below. This is a decomposition,
not a sorry-free proof of the whole mathematical construction: 1 upper hole closed,
2 holes added, net -1 before any closure pruning.

The two added and remaining holes are exactly:

- `WeilConjectures.sfFiniteOperations_restrictedAdjunction`
  (`lem-sf-finite-restriction-normalized-adjunction`), in
  `Sheaf.Paper.ExceptionalFiniteRestrictionAdjunction`.
- `WeilConjectures.sfFiniteOperations_intrinsicExceptionalBounds`
  (`lem-sf-finite-intrinsic-exceptional-bounds`), in
  `Sheaf.Paper.ExceptionalFiniteIntrinsicBounds`.

Validation: all three delivered modules passed server `lcompile.py --all`
with exit code 0 and no errors or warnings.
Each is a public named theorem with proof `:= by sorry`, source and complete
natural-language proof in its docstring and node. No other sorry is added. The
realization definitions retain their original constructed bodies. The restricted
adjunction obligation has no preservation/bound conclusion or coefficient-uniform
choice; its F,G and literal restriction equalities are inputs. The bounds obligation
has no adjunction, shifts, normalization or support conclusion. Thus neither restates
the original existence theorem.

## No longer needed

The parent no longer directly needs `lem-kun-dimension-finite-type`: its statement
already supplies d and its dimension bound. It also does not use
`lem-weil-pbc-finite-type-over-noetherian`: the current ordinary etale left-adjoint
interface has no Noetherian hypotheses. Neither node's declarations are removed.

Removed the following private imports from the item:
`Sheaf.Paper.PurityAffineChartBounds`,
`Sheaf.Paper.CompactSupportDirectImageTriangulated`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`,
`Sheaf.Paper.ProEtaleConstructibleOrigin`, `Sheaf.Paper.FiniteCtfTriangulated`,
and `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`.
The purity and normalized-adjunction dependencies remain in the proof plans of the
new obligations; their mathematics is not declared globally pruned. The original
public imports are retained, preserving the exported interface. No whole module
withdrawal is claimed.

## Where the brief, the DAG or earlier work was wrong

The original step 1 proposed choosing a dimension bound, although the Lean theorem
already has d and hd as inputs. It also listed Noetherian hypotheses that are no
longer required by the published ordinary etale adjunction theorem.

The item's blueprint.from.node is null, so `blueprint_refs.py ancestor` reports None.
Its parent construction node explicitly points to `sk-thm-sf-tensor-hom`; that unit's
current Complement gives the constructible adjunction and shift compatibility.
The new nodes use that actual ancestor and the intervening construction nodes.
No unit route or statement is changed.

Read the current blueprint Complement, the current affine-chart preservation
corollary and proof, and Zheng Propositions 2.23, 2.29, 3.16, Lemma 5.22 and
Proposition 5.24. Tested the obligations conceptually on empty X and middle scheme,
zero objects, identity maps, n=1, and inverted cohomological intervals. The last
case gives a zero input; Tor hypotheses already require ordered endpoints.
Relative separatedness is retained; separated structure maps are never added.
Mathlib searches (LeanSearch, LeanFinder/Loogle and grep) found the categorical
building blocks but no replacement for the specified geometric normalization or
uniform intrinsic bounds.

## New nodes

- `def-sf-finite-operation-realizations`: attachment for the eleven unchanged moved
  helpers; constructed data, zero holes.
- `lem-sf-finite-restriction-normalized-adjunction`: steps 4 and the left exact/shift
  part of step 5, for fixed literal restrictions; one hole.
- `lem-sf-finite-intrinsic-exceptional-bounds`: step 3, including transport from fixed
  coordinates and a chosen compactification to the specified intrinsic functor;
  one hole.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
