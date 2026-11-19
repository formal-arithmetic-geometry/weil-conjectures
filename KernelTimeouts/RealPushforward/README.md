# RealPushforward

Origin: commit `ed3d39ddb5d71b885681c16e4d3267aa918c87bb` (2026-11-07), `WeilConjectures/DeligneLaumon/AffineLine/RealPushforward.lean`, declaration `isReal_higherLowerShriek_one`. No direct Zulip message ID was attached to this commit. The commit records the original failure as a kernel deterministic timeout after about 90 seconds at default heartbeats; the second theorem in the file was only a cascade and is omitted from the Before reproduction.

`Before.lean` keeps the old closing step, which rewrites `FrobeniusModule.localPolynomial` directly on the concrete stalk. On current 4.35.0 it still fails with `(kernel) deterministic timeout` at line 18: 53.72 s user CPU, 54.94 s wall time, 4,717,104 KB maximum RSS. `After.lean` imports the fixed declaration and checks the same statement by applying it: 1.76 s user CPU, 2.80 s wall time, 3,126,236 KB RSS, `ok`. Both files set `maxHeartbeats 200000`.

The fix adds a universe-polymorphic generic lemma
`M.frobeniusEnd.charpolyRev = M.localPolynomial := rfl`, then rewrites the fibre equation through that lemma before the final coefficient calculation. This forces the kernel to compare the two instance paths once for an abstract module, instead of unfolding the concrete stalk, Frobenius module, and scheme geometry while checking the closing term.

Reproduce with:

```sh
cd the master build tree
LEAN_NUM_THREADS=1 /usr/bin/time -v timeout 1800 nice -n 10 lake env lean KernelTimeouts/RealPushforward/Before.lean
LEAN_NUM_THREADS=1 /usr/bin/time -v timeout 1800 nice -n 10 lake env lean KernelTimeouts/RealPushforward/After.lean
```

