# DefEq Internal Cost Experiments

Case: `EtaleHomComparisonReversedExact`
Lean: 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`)
Root: instantiated argument 26 (`hv`) of `derivedTensorHomShiftComparison_component`.
Instrumentation: observational counters/trace build; baseline and diagnostic controls from the same source snapshot.

## C1: Original instantiated domain

Baseline root: `original.lean` (the exact `hv` application). Measured counters-only root time was 36.191 s, with 3,180,470 recursive calls, maximum depth 111, 18.707 s comparison-exclusive and 17.484 s WHNF-exclusive. There were 132,807 Pi-domain events, 60,717 proof-irrelevance entries, and 60,717 proposition comparisons. The proposition timer is inclusive and is not added to the root partition. The trace captured 1,046,492 repeated exact entries in its 5,000,000-call sample; sampled repeated immediate exclusive time was 0.399 s.

The root is mixed and dependent: the expensive work is in the fully instantiated proposition after earlier binders, with `Add`/`AddGroup`/`AddHom` and coercion heads among the largest trace children. This identifies the dependent body as the measured root, but not one unique binder field.

## C2: Whole-proposition transport

Control: `aligned-Transport.lean`, replacing the expected proposition with the definitionally equal transported form while retaining the same application and consumer. The release diagnostic completed in 3.40 s; the zero-threshold instrumented run had no root over 100 ms (largest recorded root 83.711 ms, 7,014 calls). The elaborated obligation is preserved and the costly instantiated domain is removed by transport.

## C3: Restored expanded predicate

Restoration: `restored.lean`, exposing the named predicate while retaining the original domain mismatch. The largest counters root returned to 3,179,834 calls and 36.007 s. A diagnostic replay of the same restored source took 114.25 s wall because diagnostics add substantial overhead; it is used only as a restoration check, not as a comparable timing baseline.

## Conclusion

The transport control removes the dependent proposition comparison and its recursive tree; restoration brings it back. The available patch does not expose binder paths or non-overlapping instantiated-domain timers, so the result attributes cost to the instantiated proposition as a whole, not to a particular `Functor.obj` or `NatTrans.app` field. Allocation/GC and local-context pair identity were unavailable.

## READY2 round 2

The READY2-4.35.0 counters reran the same instantiated `hv` root. The original root was 24.140 s with 3,180,470 calls, 12.301 s comparison-exclusive time, and 11.839 s reduction-exclusive time. Its dependent labels were 9.866 s comparison and 9.353 s reduction (19.219 s of the root partition); 132,807 Pi-domain events and 412,714 instantiations were recorded. The C++ Expr proxy created 140,620,668 expressions / 4,699,706,856 bytes, with a 2,374,303,744-byte RSS/commit delta.

The detailed trace took 31.825 s (31.9% trace overhead over the counters root). The largest measured path was the instantiated `DFunLike.coe` -> `NatTrans.app` chain under `root/binder_body[1]/argument[2]`, with 31,817 ms subtree time; its `tensorLeft` proposition children contributed 14,395 ms and the `Quiver.Hom` child 9,034 ms. The proposition timer remains overlapping and is not added to the root partition. The aligned transport had no root over 100 ms (3,249,232 KB process RSS); the restored expanded predicate returned an 81.640 s root with 9,535,141 calls and 421,570,091 Expr constructions / 14,089,375,944 bytes.
