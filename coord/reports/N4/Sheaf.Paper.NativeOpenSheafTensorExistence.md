## What changed

`Sheaf.Paper.NativeOpenSheafTensorExistence` now constructs the actual open
extension/restriction adjunction using `IsoAlgebra.mapOfNatIsoLeftAdjunction`.
Its forgotten unit and counit are the specified ordinary components by
reduction. The ordinary open unit is invertible; conservative forgetting lifts
that fact, so extension is fully faithful and reflects isomorphisms.

Proved private generic helpers totalize a natural sheaf projection isomorphism
using the existing, proved `comparisonPrecomposeIso` machinery in
`Sheaf.Algebra.Homology.RingedOpenTotalTensorKFlat`. Exact extension and
restriction preserve quasi-isomorphisms, extension reflects them, and natural
commuting squares transfer the tensor tests. Applying this in both sheaf tensor
orders and using `mapBifunctorFlipIso` proves both categorical K-flat tests for
arbitrary unbounded complexes. The flip uses Mathlib's signed totalization
isomorphism, not an unsigned interchange of degrees.

Two new modules isolate the remaining sheaf-only steps of the original argument:
`Sheaf.Paper.NativeOpenRestrictionTensor` and
`Sheaf.Paper.NativeOpenSheafProjectionTensor`. The latter supplies normalized
pointwise comparisons and natural projection comparisons in both orders. The
natural comparisons need not be identified with the pointwise witnesses:
the original statement does not require this identification, and the K-flat
argument needs only their naturality and invertibility.

The restriction lemma imports only `WeilConjectures.WeilSheaf.Dual`; it does
not require the derived open-tensor data modules.

The item's public theorem signature and public imports are unchanged. All
helpers are private and proved; all new imports in the item are proof imports.
The generic helper module is imported with `import all` to reuse its proved
private totalization construction. Only this item and the two new modules have
Lean changes; no adopted source-library declaration is changed.

## Proved and sorry left

Closed the original body of
`AlgebraicGeometry.ProEtaleWeilSheaf.native_open_sheaf_tensor_existence`
(node `lem-sf-native-open-sheaf-tensor-existence`). The item has zero remaining
`sorry`s. Its adjunction, unit reflection, totalization argument and two-sided
K-flat transfer are proved in Lean.

Added exactly two named theorem holes:

- `AlgebraicGeometry.ProEtaleWeilSheaf.native_open_restriction_tensor`, in
  `Sheaf.Paper.NativeOpenRestrictionTensor`, node
  `lem-sf-native-open-restriction-tensor`: the ordinary balanced restriction
  comparison must commute with the native Frobenius structures.
- `AlgebraicGeometry.ProEtaleWeilSheaf.native_open_sheaf_projection_tensor`, in
  `Sheaf.Paper.NativeOpenSheafProjectionTensor`, node
  `lem-sf-native-open-sheaf-projection-tensor`: lift the slice sheaf projection
  maps, their normalization and their naturality to Weil sheaves.

Thus this delivery is a decomposition: one original hole closed, two strictly
sheaf-level holes added, net minus one before any independent lower proofs.
Neither new statement asserts adjunction existence, totalization, or K-flat
preservation. They are proper parts of original step 2, not renamings of the
item. Their complete natural-language proofs and sources are in their
docstrings and nodes. No data definition contains `sorry`.

The new statements were checked at empty and identity opens and at zero sheaves.
Normalization remains forced by faithful forgetting; no alternative adjunction
or arbitrary restriction comparison is assumed. No boundedness, lisse, finite
rank, or flat-term hypothesis is added.

## No longer needed

No existing import was removed and no module becomes globally unnecessary.
The original ordinary site-localization, tensor-generator and fixed-pair tools
are needed in the two sheaf steps, rather than as direct dependencies of the
completed complex argument. They are retained in those new nodes. No pruning
of these tools is claimed.

No additional chain-level, quasi-isomorphism-reflection, or K-flatness lemma
with a hole is needed: those parts are proved using the existing generic
machinery. The parent proof dependencies now record that actual division.

## Where the brief, the DAG or earlier work was wrong

The original plan was mathematically adequate. Its totalization and reflection
steps did not require new native declarations: the existing generic
precomposition/totalization comparison applies directly to the Weil categories.
This also avoids imposing a flat-term test in place of categorical K-flatness.

During implementation, matching the pointwise normalized maps through large
uncurried functor composites caused excessive kernel reduction. Separating
pointwise normalization from the natural comparison witnesses preserves exactly
the original conclusion and makes the sheaf statements small. Generic private
naturality and K-flat helpers keep the native application from repeatedly
unfolding the tensor implementation. They use preadditivity and Mathlib
`CategoryWithHomology`, so their interfaces do not carry a second abelian
addition structure. The original finite-type and separation binders remain;
the local unused-section-variable linter is disabled for the final declaration
rather than dropping those now-unused original hypotheses. No time or heartbeat limit is raised.

The current queue assigns a one-hole proof item. The historical quarantine row
has a restored source and no current build-error record; no archive withdrawal
or unrelated repair is claimed.

## New nodes

`lem-sf-native-open-restriction-tensor` records the pointwise balanced
restriction/tensor isomorphism with exactly the existing ordinary underlying
map. It belongs to the original native open step 2 and has no complex conclusion.
Its Lean module is `Sheaf.Paper.NativeOpenRestrictionTensor`.

`lem-sf-native-open-sheaf-projection-tensor` records the normalized pointwise
open projection isomorphisms and natural sheaf comparisons in both tensor
orders. Its proof uses the original localized-site balanced generators and
Frobenius reindexing, followed by balanced symmetry. Its Lean module is
`Sheaf.Paper.NativeOpenSheafProjectionTensor`.

Both retain the parent's chapter, unit and blueprint provenance. The parent's
proof, proof dependencies and proof origin are updated to match the Lean
reduction. No existing statement or definition changes, so no change record or
forced adaptation is required.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeOpenRestrictionTensor": "87ae3ff4ce1b837849af4f0195b7ac6ab2ae9c69", "Sheaf.Paper.NativeOpenSheafProjectionTensor": "5a30bb09f1d55361b4852397bc1dd49f416c1061", "Sheaf.Paper.NativeOpenSheafTensorExistence": "86b162e74d9501e5ffb473449ba5070181ac555c"}, "results": {"Sheaf.Paper.NativeOpenDerivedTensor": {"hash": "a399abe957301f14cadc6f5c66ced82b920920fd", "status": "OK"}}, "seconds": 21, "time": "2026-10-28T01:20:34+0800", "transitive": 0, "version": 1}
```

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
