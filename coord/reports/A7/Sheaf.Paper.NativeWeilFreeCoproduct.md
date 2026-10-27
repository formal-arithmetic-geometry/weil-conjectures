## What changed

Proved `AlgebraicGeometry.NativeWeilInduction.nativeWeil_free_coproduct` in
`Sheaf.Paper.NativeWeilFreeCoproduct`. The proof constructs the termwise orbit cofan,
localizes it using coproduct preservation, verifies the actual localized adjunction unit
and structure equations, and identifies its legs by integer induction. All supporting
constructions and lemmas are private to the item module. The original theorem signature,
docstring, and public import are unchanged. Added proof imports for exact derived
coproducts, degreewise complex colimits, and exact-functor comparison equations.

Updated the item's node proof to record the implemented argument. No shared interface,
existing dependency module, or other node is changed.

Validation: the server single-file compiler accepted the complete proof in 6.9 seconds.
Removed its unused-section-variable warning before delivery; the delivery tool runs the
final compilation and axiom probes.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.NativeWeilInduction.nativeWeil_free_coproduct`
(node `lem-sf-native-weil-free-coproduct`): one hole closed, zero holes added.
There are no remaining `sorry` declarations in this delivery and no split-off obligations.

## No longer needed

None. The proof retains all three declared proof dependencies:
`lem-sf-free-derived-weil-resolution`, `lem-pur-exact-derived-coproducts`, and
`def-weil-exact-derived-adjunction`. No import, declaration, node, or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The original plan is sufficient once its termwise cocone
and normalization transports are implemented explicitly. The construction applies to
arbitrary derived objects and imposes no boundedness or constructibility hypothesis.
The generic recurrence argument uses both directions of integer induction and requires
only a fully faithful Frobenius equivalence, so it does not depend on identifying the
chosen inverse functors definitionally.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
