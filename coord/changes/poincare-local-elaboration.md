# WeilConjectures.PoincareDuality.Poincare local elaboration attributes

## Reason

The Poincare item expands expensive derived closed and coefficient pullback structures during
elaboration. Local irreducibility and instance priority keep the item below the single-file
time limit without changing public declarations.

## Old

The item had no module-local irreducibility or bounded-constructible instance-priority
commands. Its trace-cup proof used inferred abstract arguments and its isomorphism proof
unfolded the composite directly.

## New

The item adds local irreducibility attributes for `DerivedCategory.monoidalClosed`,
`CategoryTheory.Mod.monoidalClosed`, and `AlgebraicGeometry.ProEtale.upperStarFromPoint`,
plus local priority for `CategoryTheory.ObjectProperty.fullMonoidalSubcategory`. It imports
the two helper modules, passes the abstract arguments explicitly in the trace-cup proof,
and uses a private fully proved composition helper for the isomorphism proof. These changes
are local to the item module and preserve every public signature and definition.

## Users

Only `WeilConjectures.PoincareDuality.Poincare` is changed; no other module requires an
adaptation. The two helper modules are new public modules and expose only the two named
constructibility lemmas recorded by the new DAG nodes.

## Status

landed 20261017T201726-L-80542 2026-10-17 (merge of deliver/B4/WeilConjectures.PoincareDuality.Poincare)
