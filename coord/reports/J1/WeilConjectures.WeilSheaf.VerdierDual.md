## What changed

Filled `AlgebraicGeometry.WeilComplex.nonempty_dualizingComplex_iso` in
`WeilConjectures.WeilSheaf.VerdierDual` by a cohomological decomposition in the native
category. The proof uses two new private proof imports:
`Sheaf.WeilSheaf.SmoothDualizingConcentration` and
`Sheaf.WeilSheaf.SmoothDualizingCohomology`.

Mathlib reconstructs the dualizing object from its single nonzero cohomology degree.
The degree `-2d` sheaf is identified with the native Tate line tensor the constant
sheaf. The proof then uses the single-functor shift comparison, the fully faithful
native subcategory inclusion, and the exact ihom functor's compatibility with
single complexes to obtain exactly the existing target. Every existing public
signature, definition body, attribute, public import and previously completed proof
is preserved. No other existing Lean module is changed.

The two new statements quantify an arbitrary right adjoint and its actual native
adjunction to avoid importing VerdierDual back into its own proof dependencies.
They assert separate cohomological facts, rather than repackaging the isomorphism.
Neither alone implies the target: concentration does not identify the surviving
sheaf, and the cohomology identification gives no control of other degrees.

All three delivery modules compiled in import order; the main module took
31.7 seconds. Its only formatting warning was corrected before the final
delivery checks.

## Proved and sorry left

This is a decomposition, not an unconditional proof or a net reduction of holes.
Original item: one hole. Its proof body is now complete:
`AlgebraicGeometry.WeilComplex.nonempty_dualizingComplex_iso`
(node `lem-pur-weil-smooth-dualizing-complex`). The item itself has zero `sorry`s.

Two holes are added, each a public named theorem with its source and full proof
in words in its docstring:

- `AlgebraicGeometry.WeilComplex.smooth_dualizing_concentration`
  (`lem-sf-weil-smooth-dualizing-concentration`): both bounds at degree `-2d`.
- `AlgebraicGeometry.WeilComplex.nonempty_smooth_dualizing_cohomology_iso`
  (`lem-sf-weil-smooth-dualizing-cohomology`): the surviving constructible Weil sheaf.

Thus one upper hole is closed by splitting off two strictly simpler lower holes;
net holes closed minus holes added is -1. No other sorry is left or introduced.
The new statements were checked on `d = 0`, the empty scheme, and disconnected
schemes of pure dimension `d`. They require no connectedness, properness,
nonemptiness, or choice of a lattice. For an empty scheme all objects are zero;
for `d = 0` the degree is zero and the canonical zero twist is used. Any chosen
right adjoint has the same result by counit-normalized uniqueness.

## No longer needed

No existing Lean import was removed: all previous imports remain necessary for
the other completed declarations. No existing module is withdrawn or claimed
to be globally pruned.

The parent's direct proof-dependency list is replaced by the two new nodes.
The former direct dependencies were:
`lem-pod-separated-finite-type-base-change`,
`lem-sbc-smooth-relative-dimension-permanence`,
`lem-pur-constant-purity-frobenius-square`,
`cor-coef-verdier-weil-equivariance`, `prop-weil-operations`,
`lem-pur-fixed-pair-right-adjoint-comparison`, and
`def-weil-weil-sheaf-complex`.
Base-change permanence and the constant-purity square remain in the new nodes'
proofs. Coefficient-stage smooth purity and its unit route remain required.
The native exceptional-forgetting comparison replaces a direct application of
`Sheaf.CategoryTheory.FixedPairRightAdjointComparison` and
`Sheaf.SixFunctors.CoefVerdierWeilEquivariance` to the native derived object.
Those existing declarations and their dependencies remain intact.

The parent no longer directly uses its old approved `tool_uses` entries:
`lem-pod-separated-finite-type-base-change`,
`lem-sbc-smooth-relative-dimension-permanence`,
`cor-coef-verdier-weil-equivariance`, `prop-weil-operations`,
`det-sp-unique-right-adjoint`, and `lem-pur-rational-weil-naturality-mate`.
Its `tool_uses` is therefore empty; the unit's coefficient transport and
Frobenius arguments are retained below the new cohomological statements.

## Where the brief, the DAG or earlier work was wrong

The current server queue row is stage 3, one hole, `proof / route` (checked over SSH).
The current source has one hole, although the historical quarantine row lists the whole
module and its older group of nodes. The archive and live source agree; the
recorded build error says the quarantined source path was absent. This delivery
preserves the module and all its existing dependencies and supplies its remaining
smooth proof assembly.

The old parent plan applies a fixed-pair right-adjoint comparison, whereas the
adopted `WeilComplex` is a full subcategory of the derived category of Weil
sheaves, with derived extension morphisms. It cannot simply be identified with
fixed pairs in the ordinary derived category. The new proof works in that
native category. Its lower obligations use the existing native exceptional
forgetting interface and the cohomological consequence of the canonical
Frobenius purity square. This preserves the smooth-purity transport unit's
finite, integral, rational and common-stage route. The existing parent statement
and its historical attachment are not silently rewritten.

## New nodes

`lem-sf-weil-smooth-dualizing-concentration` is realized by
`Sheaf.WeilSheaf.SmoothDualizingConcentration`. It isolates the vanishing of
cohomology away from degree `-2d`, detected by exact conservative forgetting
and the ordinary smooth purity specialization.

`lem-sf-weil-smooth-dualizing-cohomology` is realized by
`Sheaf.WeilSheaf.SmoothDualizingCohomology`. It isolates identification of one
cohomology sheaf, including its canonical Frobenius action, from the constant
purity Frobenius square. Its statement does not assume or assert concentration.

The parent node's proof, proof dependencies, proof origin and obsolete tool-use
entries are updated. No definition or signature repair is made and no change
record is needed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.WeilSheaf.SmoothDualizingCohomology": "53cf8d293c22d263b2fc9299d93191dded567928", "Sheaf.WeilSheaf.SmoothDualizingConcentration": "3ca62785f3088b295c335e3fccbabd0836a6a45f", "WeilConjectures.WeilSheaf.VerdierDual": "cbd782ced4a4ed0d3932076da1a163a61a8db8c5"}, "results": {}, "time": "2026-10-28T01:00:49+0800", "transitive": 0, "version": 1}
```

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
