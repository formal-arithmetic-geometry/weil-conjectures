# DefEq Internal Cost Experiments

Case: `F66Adj`
Lean: 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`)
Root: instantiated argument-39 counit proposition.
Instrumentation: observational counters/trace build; diagnostic controls from the same source snapshot.

## C1: Original argument-39 proposition

Baseline root: `original.lean`. Counters measured 44.174 s root wall, 3,897,905 recursive calls, maximum depth 121, 22.801 s comparison-exclusive and 21.373 s WHNF-exclusive. There were 176,636 Pi-domain events, 73,771 proof-irrelevance entries, and 73,771 proposition comparisons. The trace sample had 1,290,616 exact repeats and 0.639 s sampled repeated immediate exclusive time.

The profile is mixed and deep. Top children include `Add.add`, `Eq`, `DFunLike.coe`, `LinearMap.mk`, `HAdd.proj`, and scalar-operation heads. The proposition timer overlaps the root partition and is not treated as an independent cost share.

## C2: Restriction-counit transport

Control: `aligned-Transport.lean`, replacing only the `hR` proof representation in the argument-39 proposition. The release diagnostic completed in 3.73 s; the threshold-zero instrumented control's largest root was 26.484 ms and 2,881 calls. The consumer and argument-39 obligation remain the same, while the dependent proof proposition is aligned.

## C3: Restored preceding transport

Restoration: `restored.lean`, changing only the preceding tensor-isomorphism argument and leaving `hR` in its original form. The main root returned to 3,901,014 calls and 44.295 s. A diagnostic replay of the original `hR` form took 119.55 s wall; that run is retained as a restoration check because diagnostics add overhead.

## Conclusion

The `hR` representation is a causal component of the instantiated dependent proposition: replacing it removes the large root, while changing an earlier argument does not. The current instrumentation cannot map the cost to one `Over` or scheme field, and it cannot provide allocation/GC attribution.

## READY2 round 2

The READY2-4.35.0 original root was 29.544 s with 3,897,905 calls, split into 15.058 s comparison and 14.486 s reduction. Dependent comparison/reduction accounted for 12.108 s / 11.593 s; the root entered 176,636 Pi domains and 531,910 instantiations. The Expr proxy recorded 170,987,170 constructions / 5,714,525,816 bytes and a 2,870,804,480-byte RSS/commit delta.

The trace root was 38.829 s (31.4% overhead). Its dominant path was `root/argument[1]/argument[0]/argument[7]`, through nested `DFunLike.coe` and `NatTrans.app`; the deepest repeated `NatTrans.app` path carried 34,886 ms subtree time. A `tensorHomAdjunctionQhObj` child accounted for 2,026 ms and the `DerivedCategory.instMonoidalCategory` proof child 1,899 ms. The transport control had no root over 100 ms (2,907,388 KB RSS); restoration returned a 76.595 s root with 9,536,477 calls and 421,630,510 Expr constructions / 14,091,341,096 bytes.
