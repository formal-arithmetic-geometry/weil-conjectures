# ImageHomCounit

Origin: commit `212f97dd22a5f9bb594ab5bbbd035ef628eb913e` (2026-11-05), `WeilConjectures/AlgebraicGeometry/IndEtaleMapping/IndEtaleDerivedImageHomCounit.lean`, declaration `imageHomIso_counit`. No direct Zulip message ID was attached to the commit. The original issue was a kernel-expensive concrete comparison in the global-Hom counit proof; the commit message describes it as a cheap-kernel-check fix rather than a remaining hard timeout.

`Before.lean` uses the old direct `conjugateEquiv_counit` proof. On 4.35.0 it succeeds, but takes 55.53 s wall time and 7,466,068 KB maximum RSS (54.42 s user CPU). `After.lean` checks the same statement through the fixed theorem and takes 2.60 s wall time and 2,795,040 KB RSS (1.66 s user CPU). Both files set `maxHeartbeats 200000`; `autoImplicit` and the instance-size option match the source module.

The fix introduces a heterogeneous-equality helper for evaluated conjugation isomorphisms. It eliminates category, functor, adjunction, and object arguments one at a time, so the kernel can use `rfl` after the arguments are aligned instead of unfolding the derived adjunctions to discover that the two presentations coincide.

Reproduce with:

```sh
cd the master build tree
LEAN_NUM_THREADS=1 /usr/bin/time -v timeout 1800 nice -n 10 lake env lean KernelTimeouts/ImageHomCounit/Before.lean
LEAN_NUM_THREADS=1 /usr/bin/time -v timeout 1800 nice -n 10 lake env lean KernelTimeouts/ImageHomCounit/After.lean
```

