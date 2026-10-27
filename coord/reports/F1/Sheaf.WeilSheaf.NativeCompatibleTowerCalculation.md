## What changed

Proved `AlgebraicGeometry.WeilComplex.nativeWeilCompatibleTowerCalculation` in
`Sheaf.WeilSheaf.NativeCompatibleTowerCalculation`, preserving its entire signature,
public imports and existing documentation. Both existing proof imports are used.

Extract the direct-image compositor, open-extension compositor, and preservation
of bounded constructibility from `nativeWeilBasicComparisons`. Lift the restricted
extension by zero into the bounded constructible full subcategory using
`ObjectProperty.lift`. Apply
`nonempty_extensionByZero_rightDerivedLowerStar_iso` to `t,pW,p,i` and `hcart.w`,
whisker its inverse along that lift and the final direct image, and compose the
result with the first comparison. Thus the interchange is evaluated only on the
bounded constructible image of `J_s`, as required.

The node's proof record now describes this lift and omits unused geometric
bookkeeping. No statements, definitions, consumers, or unit routes changed.

Validation: lcompile.py compiled the single module cleanly in 5.6 seconds.
LeanFinder found `ObjectProperty.lift` and `liftCompιIso`; Loogle confirmed
`Functor.isoWhiskerLeft`; grep confirmed the whiskering API. The stipulated
comparisons already provide the shortest route. The proof is uniform for empty
schemes, zero complexes, identity maps, and non-separated schemes: it introduces
no nonemptiness, cohomological bounds beyond objectProperty, or separatedness
assumptions.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.WeilComplex.nativeWeilCompatibleTowerCalculation`
(blueprint: `lem-sf-native-weil-compatible-tower-calculation`).

Zero holes remain in the item. Zero holes or new declarations were added.
The proof uses the existing named proper/open interchange theorem, whose own
proof remains a separate existing item; this delivery does not claim to close
that dependency's hole.

## No longer needed

No imports removed and no modules withdrawn. Both native comparison imports are
needed. Existing public imports are preserved.

Removed the proof dependency on `lem-weil-pbc-proper-fp-permanence`: the explicit
functor statement requires no proof that `p ≫ q` is proper. The open-immersion
and finite-type definitions remain statement dependencies; their separate proof
edges are unnecessary because the comparison theorems and existing instances
already supply the interfaces needed by the calculation. This is pruning of
proof edges only, with no claim that these shared nodes become globally unused.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The DAG's initial verification of the
three compactification factorizations is extra bookkeeping for this explicit
functor statement. Its proof record has been aligned with the compiled argument.
The bounded-source requirement of the interchange theorem is essential and is
satisfied by the actual lifted `J_s` functor.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
