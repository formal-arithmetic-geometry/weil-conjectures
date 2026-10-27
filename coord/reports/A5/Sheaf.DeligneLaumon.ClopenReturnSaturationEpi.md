## What changed

Proved `AlgebraicGeometry.WeilSheaf.epi_clopen_return_saturationUnit` with its statement
unchanged. Added three proof modules, each with one public theorem and its DAG node:
`ClopenSheetDisjoint`, `ClopenNonreturnVanishing`, and `ClopenReturnTranslateFactor`.
The item imports the latter two privately. No other existing module is changed.

The categorical helper in the item proves epimorphy directly by cancellation against
the pulled-back image quotient and the coprojections. For nonreturn powers, sheet
intersections and the finite-field Frobenius order give disjointness; inverse image
of extension by zero then vanishes. For return powers, the free algebra's shift
identity and equivariance propagate the zero-th factorization in both integer
directions. This avoids constructing a complete finite-field tensor splitting. The existing
Mathlib leaf `lem-sfb-finite-field-galois-frobenius` supplies the Frobenius order,
and the source-library declarations attached to
`lem-sf-native-adic-open-restrictions` supply disjoint vanishing and the invertible
adjunction unit. Their statements are used directly.

Edge cases checked: the statements allow empty schemes and zero carrier maps.
The nonreturn condition excludes index zero; negative indices use inverse
Frobenius. Degree zero contradicts the finite-field cardinality equation in the
geometric lemma, while the return lemma itself allows it.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.WeilSheaf.epi_clopen_return_saturationUnit`.

The new public theorems are:

- `AlgebraicGeometry.WeilSheaf.clopen_sheet_disjoint_pow`
  (`lem-zl-clopen-sheet-disjoint`).
- `AlgebraicGeometry.WeilSheaf.isZero_clopen_nonreturn_freeObj`
  (`lem-zl-clopen-nonreturn-vanishing`).
- `AlgebraicGeometry.WeilSheaf.clopen_return_freeHom_factor`
  (`lem-zl-clopen-return-translate-factor`).

Holes added: zero. Sorries left in the delivery: zero. No declaration is an
unproved replacement for the item. The new modules implement the geometric,
vanishing and return-shift parts of its argument.

## No longer needed

No existing import, node or module is removed. Both originally declared dependencies
remain in use. The full tensor-product splitting and enumeration of all sheets in
the old proof plan are unnecessary: one hypothetical intersection, epi cancellation
and the order of finite-field Frobenius suffice. These constructions had no separate
declared dependency in the item's node. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The old node's first two steps marked substantive geometry and equivariance as
non-elementary, but supplied only definition modules as dependencies. The delivery
implements these steps rather than moving the saturation-epimorphy obligation.
Checking the return induction directly with concrete sheaf functors exceeded
the kernel checking limit. The induction and the free-algebra factorization
argument, including extraction of equivariance from the lifted algebra map,
are private theorems over abstract categories. A private proposition keeps the
pullback functor and its carrier comparison as parameters; it is specialized
before applying it to the concrete algebra map. This lets the proof use the
source `liftOfStr` API without expanding concrete structure isomorphisms.
No shared definition is changed. Profiling the completed proofs measured about
0.30 seconds of kernel checking for the return module and 0.06 seconds for the
item module. All four modules compiled with `lcompile.py --all`; the temporary
profiling options have been removed.

The nonreturn calculation in fact needs neither the structural compatibility `hc`
nor a Weil structure on its coefficient sheaf. The target retains every binder.

## New nodes

`lem-zl-clopen-sheet-disjoint` records the disjoint-range theorem for a nonreturn
natural power. It does not assume the sheet map is open.

`lem-zl-clopen-nonreturn-vanishing` records vanishing of the restricted integer free
summands, including negative indices. It uses the preceding disjoint-range theorem
and the existing extension-by-zero API.

`lem-zl-clopen-return-translate-factor` records factorization only at return indices.
It does not assume a model monomorphism or a constant-field cardinality equation and
makes no assertion about a saturation or an image.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
