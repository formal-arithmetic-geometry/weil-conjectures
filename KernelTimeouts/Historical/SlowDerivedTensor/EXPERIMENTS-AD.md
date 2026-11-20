# DefEq Internal Cost Experiments: Slow Derived Tensor

Lean 4.33.1 (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`), Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, source
`bdab171985a`. The targeted Tensor import closure was rebuilt. The
observational patch is `../Anatomy/kernel/lean-v4.33.1-ad.patch`.
`probes/ad/profile.txt` contains the measured root, branch, path, and top-20
child lines; `probes/ad/provider-variants.lean` contains the B/A2 attempt.
All runs used one target Lean thread, `timeout 3600`, and `/usr/bin/time -v`.

## Experiment A1: standalone instance argument

**Baseline.** The exact root is the `Kernel.isDefEq` comparison of argument
2 (`MonoidalCategoryStruct`) inside the historical `tensorObj` inferred and
declared type pair, reached by `probes/anatomy/argument2.lean`. The two
expressions have head `inferInstance`, but sizes 1,785 and 11,973 in the
probe; their types are definitionally equal and not structurally equal.
The unpatched source run returned true in 44,532 ms at the Lean timer,
46.95 s process wall, 7,002,984 kB peak RSS. Final counters returned true
in 50.17 s process wall (+6.9%); the near-final path trace returned true
in 61.87 s (+31.8%). The final counter root was 42.201 s; trace root was
55.322 s. Times from these modes are not added to each other.

**Internal cost.** The counter root made 6,269,622 recursive calls at maximum
depth 96. Exclusive comparison was 22.994 s (54.5%) and outer WHNF was
19.207 s (45.5%). It entered 18,804,316 WHNF requests, 10,639,573 Delta
unfolds (0.802 s direct Delta time), 9,414,298 Beta, 10 Iota, 209,669
Zeta, and 1,409,880 projection steps. Branch-exclusive comparison plus
reduction was largest in projection (15.961 s), application (15.278 s),
and second-WHNF exits (6.458 s). The Delta and proof-irrelevance exit
branches contributed 1.853 s and 1.700 s respectively; these are exit
labels, not independent cost categories.

The disjoint dependent-labelled recursive subtree consumed 18.163 s
comparison plus 15.920 s reduction; the proposition-labelled remainder
consumed 4.830 s plus 3.287 s. These labels partition nearly all root
time, but binder-body work nested inside a proposition is assigned to
dependent, so the latter is not merely Pi-domain checking. There were
46,522 Pi-domain comparisons, 367,208 measured binder instantiations
(0.392 s), 79,290 proof-irrelevance exits, and 79,290 proposition-type
entries. The older nested `proposition_ms=243.887 s` overlaps itself and
the root partition and is not a time share.

**Component attribution.** In the trace, `root/argument[2]/binder_body[2]`
leads through `Functor.obj` to the proposition type of
`Functor.HasDerivedMonoidalCategory.curriedTensor_hasLeftDerivedFunctor₂`
(55.103 s subtree). Within its `Functor.obj` argument 4, argument 7
consumed 37.565 s and sibling argument 5 consumed 16.437 s. These two
exclusive-subtree sums cover 97.6% of the 55.322 s trace root. The first
enters a `Functor.uncurry._proof_3` equality proposition and nested
`CategoryStruct.comp` pairs. The second enters `CategoryStruct.comp`,
`DFunLike.coe`, and `NatTrans.app`. Direct time at the immediate argument
nodes is under 0.1 ms; cost is in descendants. The largest individual
child-exclusive times were `AddCommGroup.proj` 339.550 ms,
`instNegHomFunctor` 329.725 ms, `Add.proj` 158.655 ms, and
`NSMul.nsmul` 158.375 ms. The full top-20 list, with IDs and paths, is in
`profile.txt`.

The high-frequency Delta heads from the preceding phase are not direct
hotspots: direct Delta time is only 0.802 s of the 42.201 s counter root.
The root is a deep mixed comparison/reduction workload concentrated in two
dependent proposition subtrees.

**Repetition and memory.** Trace captured the first five million general
pairs: 3,333,872 distinct ordered node pairs, 1,666,128 exact repeats,
and 2,513,274 raw-hash groups. Repeated captured calls account for 0.309 s
immediate exclusive time, not descendant replay. All 79,290 captured
proposition pairs were exact-distinct. The final counters recorded
238,999,955 C++ Expr constructor outputs and 7,986,065,736 bytes of their
object sizes; this omits Lean-generated constructors and non-Expr objects.
RSS rose by 3,528,916,992 process bytes during the root. Neither these
output counts nor RSS is a process-wide allocation or GC-time measure.

## Experiment A2: targeted ablation

The measured candidates are the two sibling argument subtrees above.
`provider-variants.lean` tested an explicit same-path instance and a
shared local `MonoidalCategoryStruct` at the same outer `tensorObj`
consumer. Both replace the entire provider, not just the measured nested
argument 7 or 5. The shared variant also adds a binder. The complete
inferred/declared conversion became millisecond-scale, so its slow root
was no longer demanded. These controls fail the A2 requirement to retain
the original root obligation; no causal cost reduction is assigned to
either inner component. The unchanged `argument2.lean` was rerun after
the attempt as the original/restored reference.

## Experiment B: shared versus independently constructed provider

The original pair has the two different 1,785/11,973-size elaborated
providers. Explicitly requesting the same instance path on both sides
produced 1,785/1,785-size *structurally equal* expressions, so this is
not evidence for two independent objects. The shared-local variant
produced the same local variable on both sides (size 1/1) but changed
the theorem telescope. All provider types checked as definitionally
equal. The probe's final-type comparisons were reported as 0 ms for
all three variants, while two timeout-scale recursive roots occurred
elsewhere during elaboration; those roots cannot be assigned to B0/B1/B2
at the fixed conversion site. Thus the required three-way B experiment
is invalid here. The measured original standalone pair remains expensive;
the data do not isolate independent construction from construction-path
divergence, pointer sharing, or a changed trigger.

**Conclusion.** A1 directly locates the cost in two dependent subtrees of
a `HasLeftDerivedFunctor₂` proposition type, with millions of recursive
`CategoryStruct.comp`, `DFunLike.coe`, and `NatTrans.app` descendants and
substantial WHNF work. A2 and B have no valid fixed-root causal estimate.

## Round 2 validity check

The provider probe was rerun with the validated READY2 4.33.1 counters
binary. It reproduced the two expensive independent-provider roots and the
shared-binder fast path, but also exposed why the latter is not a fixed-root
comparison: `adTensorOriginal` has inferred/declared type sizes 5,361/18,817,
whereas `adTensorShared` has 2,283/3,917 because it adds the `MC` instance
to the theorem telescope. The direct meta-level checks report 0 ms only
after those declarations have already been elaborated. Thus the rerun
confirms the structural control change, not a causal B2 sharing effect.
