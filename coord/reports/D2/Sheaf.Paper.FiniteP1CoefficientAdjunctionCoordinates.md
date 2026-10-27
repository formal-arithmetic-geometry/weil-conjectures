## What changed

Proved `finiteP1_coefficient_adjunction_coordinates` with its statement unchanged.
The proof first constructs normalized coefficient coordinates on both schemes,
then constructs the inverse-image comparison and its invertible adjunction mate.

The shorter route is that the statement permits choosing `p`. Lift the discrepancy
between its initial coefficient-unit component and the given evaluated coefficient
isomorphism through the equivalence `H`. Extend this unit automorphism to every
object by tensoring and conjugating with unitors. Adjust `p` by that natural
automorphism, then take its mate `q`. This gives both required equations without a
separate normalization theorem about a previously fixed choice of `p`.

Added five modules: `FiniteP1CoefficientCoordinateDefinitions` moves the three
existing definitions unchanged to break the helper-import cycle;
`FiniteP1AdjunctionTransport` constructs native and projective pull comparisons
and proves the generic mate equation; `FiniteP1IntrinsicRootTensor` proves the
unique normalized root-tensor realization from the two existing universal
properties; `FiniteP1CoefficientExistence` composes the constant and root
comparisons with their section equations; `FiniteP1UnitAdjustment` proves the
unit-automorphism adjustment. The original module publicly reexports the moved
definitions and imports the other helpers only for its proof.

The six item and helper modules compile cleanly through `lcompile.py`, with no
warnings and a maximum file time of 30.6 seconds. The main theorem signature
was checked unchanged, and the three relocated definitions were checked
verbatim against their original signatures and bodies.

The unclaimed consumer `FiniteP1KummerChernRealization` receives one proof-only
performance adaptation: replace two large `simpa` conversions by explicit
unfolding and `exact`. Its original source exceeded the file limit both with
this delivery and against published dependencies. Profiling attributed about
50 seconds to linting those conversions; the adaptation took 14.7 seconds.
Every statement, definition, instance, attribute and import stays unchanged.
The final clean compile took 27.3 seconds; its caller
`DiagonalTraceFiniteChernComparison` compiled in 16.0 seconds. The other direct
consumers, `FiniteP1KummerBoundaryTransport` and `FiniteP1KummerComparisonIso`,
compiled unchanged in 43.3 and 12.5 seconds respectively.

Change records are `coord/changes/D2-finite-p1-coordinate-definitions.md` and
`coord/changes/D2-finite-p1-chern-consumer-performance.md`.

## Forced adaptations

None. The delivered proof-only edit of the unclaimed consumer
`Sheaf.Paper.FiniteP1KummerChernRealization` (replacing two `simpa` conversions with
`unfold` and `exact`) was not forced, and the reviewer withdrew it. The published original
compiles against the delivered modules in 48.5 s and against the published build in 45.9 s,
measured in the same run. Both are under the 60 s limit. The module is restored to its
published text. The change record `D2-finite-p1-chern-consumer-performance` has status
withdrawn. The paragraph above that describes this adaptation is superseded.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.ProEtale.DiagonalTrace.finiteP1_coefficient_adjunction_coordinates`
(node `lem-sfb-finite-p1-coefficient-adjunction-coordinates`). Added zero holes;
zero `sorry` remain in the delivery. This is a proof, not a decomposition into
new obligations.

The new proved public theorems are
`AlgebraicGeometry.ProEtale.DiagonalTrace.finiteAdjunctionCoordinates`,
`AlgebraicGeometry.ProEtale.SpTowerP1.finiteP1_intrinsic_root_tensor`,
`AlgebraicGeometry.ProEtale.SpTowerP1.finiteP1_coefficient_coordinates_exists`, and
`finiteP1_adjust_coordinate_unit`. The native/projective comparison maps are
explicit constructions, and the three relocated definitions retain their bodies.

The tensor construction includes all scalar sections and roots, not only tensors
with scalar one. It uses the module-sheafification adjunction and
`finiteTateLine_universal`, and proves uniqueness through injectivity of the
corresponding Hom-equivalence. No arbitrary object is chosen from an unproved
existence theorem. Empty schemes, the zero coefficient ring, and level zero are
covered by the same proofs.

## No longer needed

No existing module is withdrawn or pruned. The original public imports
`TowerP1CoefficientCoordinates` and `GeoP1Cohomology` now enter through the
publicly imported definition module; their effective public availability stays
the same. Every new proof import is used.

The parent's old proof step comparing `cp.normalization` with a fixed native
pullback coordinate is unnecessary: the existential comparison can be adjusted
on its coefficient unit. No ordinary normalization lemma, geometry-adjunction
evaluation lemma, Chern-class comparison, cohomological decomposition, or
projective-line cohomology theorem is used to prove this item. The
`GeoP1Cohomology` module remains needed for the ordinary functor and unit
*definitions*, so its node is retained. The definitions in
`def-sp-tower-class-diagonal`, `def-sp-p1-coefficient-coordinates` and
`def-sp-finite-intrinsic-direct-adjunction` are still needed, together with the
proved root-tensor and constant-module comparisons listed in the new nodes.
No realized unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan required proving that a particular canonical choice of `p`
already satisfies the coefficient equality. That is stronger than the unchanged
existential statement. The natural unit adjustment proves exactly the statement
and allows the two adjunction equations to be handled independently.

The current coordination row was checked before work. Its assigned item is a
one-hole proof-route item; the older build-error record concerned imports, while
the initial source compiled unchanged against the published dependencies. No
zero-hole no-op or archived-module withdrawal is part of this delivery.

An existing statement is disputed independently of this item:
`STATEMENT-DISPUTED: finiteP1_kummer_chern_realization_of_boundary` quantifies
an arbitrary line isomorphism `t`, but its hypothesis `FiniteP1BoundaryData` does
not constrain `t`. Replacing `t` by `-t` negates the left side and keeps the right
side fixed. For the degree-one hyperplane class with odd residue characteristic,
the right side is not killed by two. A normalization condition on `t`, or a
canonical construction of it, is missing. This was checked in the current source;
`Sheaf.Paper.FiniteP1KummerBoundaryTransport` is held by D3, so this report passes
the issue to the maintainer without editing that held module. The proof of this
item does not use this boundary statement. The performance adaptation of its
existing consumer retains its current statement and dependency route.

## New nodes

`def-sfb-finite-p1-coefficient-coordinate-definitions` records the unchanged
unit/source-coordinate definitions in their new publicly reexported module.

`lem-sfb-finite-p1-adjunction-transport` records the explicitly constructed
native/projective pullback comparisons and the fully proved generic invertible
mate unit equation.

`lem-sfb-finite-p1-intrinsic-root-tensor` records the fully proved unique
realization comparison of the fixed and intrinsic finite root tensors, with its
pure-tensor equation on every test object.

`lem-sfb-finite-p1-coefficient-existence` records the fully proved existence of
normalized constant and Tate-line coefficient coordinates on any scheme where
the exponent is a unit.

`lem-sfb-finite-p1-unit-adjustment` records the fully proved categorical extension
of a tensor-unit automorphism and its application to natural comparisons through
an equivalence.

Change records: `coord/changes/D2-finite-p1-coordinate-definitions.md` and
`coord/changes/D2-finite-p1-chern-consumer-performance.md`.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.FiniteP1AdjunctionTransport": "b9bc61c07178f29136ee7e418cacb233ec12421e", "Sheaf.Paper.FiniteP1CoefficientAdjunctionCoordinates": "137c7c8f5d96af2ce77b4c3a3e5d6bd34909b952", "Sheaf.Paper.FiniteP1CoefficientCoordinateDefinitions": "a64774d2783ff1fe72abd6801b2b58ab3b328903", "Sheaf.Paper.FiniteP1CoefficientExistence": "84e0b327bd9b8db2cd45bb5929a143cdb3c7152c", "Sheaf.Paper.FiniteP1IntrinsicRootTensor": "b80cf3cbdcfb4b9e5dec0ef8d3b6e9c8d030c8e7", "Sheaf.Paper.FiniteP1KummerChernRealization": "cfd1afa12c3a4b58789ec798605dc6405d7fad88", "Sheaf.Paper.FiniteP1UnitAdjustment": "835afb9206eb976b5fe5d4e3caca4941714515e7"}, "results": {"Sheaf.Paper.FiniteP1KummerBoundaryTransport": {"hash": "debc0041f891825a43690816c655b5422a188805", "status": "OK"}, "Sheaf.Paper.FiniteP1KummerComparisonIso": {"hash": "e9a37d237a018552b392a35393cc1e94dd2d7305", "status": "OK"}}, "seconds": 109, "time": "2026-10-28T03:31:26+0800", "transitive": 0, "version": 1}
```

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

Reviewer note (2026-10-28). The new node files now cite the direct owners of the
declarations in their Lean statements (stmt_deps):
- coordinate definitions: tower-shriek data, tower-class systems/diagonal, extension-by-zero, sk-d-lines;
- adjunction transport: extension-by-zero, pbc pro-etale operations, finite upper star, sk-d-lines;
- coefficient existence: tower-shriek data;
- intrinsic root tensor: p1 tensor-ordinary coordinates, tower-class diagonal, intrinsic direct adjunction, roots-of-unity sheaf, finite Tate line, tower-shriek data.

The item node's stmt_deps also gain `def-sfb-finite-p1-coefficient-coordinate-definitions`, the new owner of the three relocated definitions its statement uses.
