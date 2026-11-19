# Image-Hom naturality

Origin: `f66ad18a9ed` (2026-11-05), `WeilConjectures/AlgebraicGeometry/IndEtaleMapping/IndEtaleDerivedImageHomAdjunction.lean`, declaration `imageHomIso_naturality`. The commit describes a cheap kernel check for image-Hom naturality. No Zulip message ID was attached to the commit.

`Before.lean` is the parent revision of that module; `After.lean` is the fixing revision. Both use the source's heartbeat setting (the parent scopes `maxHeartbeats 400000` over the target; the fixed revision removes that raise, leaving the project default of 200000). On Lean 4.35.0, Before succeeds in 1:56.47 wall time with 12,639,544 KB peak RSS; After succeeds in 3.40 seconds with 2,835,572 KB peak RSS. This is a cost reproduction, not a current hard failure. Both runs used `LEAN_NUM_THREADS=1`, `timeout 1800`, `nice -n 10`, and `/usr/bin/time -v` in `the master build tree`.

The fixed abstract naturality helper takes the target coefficient variance as an explicit parameter and then substitutes its equality. Its application also uses the new restriction comparison. This makes the target transformation and adjunction arguments syntactically match, avoiding a large kernel reduction of definitionally equal derived functors.

Reproduce with `cd the master build tree` and:

```sh
LEAN_NUM_THREADS=1 /usr/bin/time -v timeout 1800 nice -n 10 lake env lean KernelTimeouts/F66Adj/Before.lean
LEAN_NUM_THREADS=1 /usr/bin/time -v timeout 1800 nice -n 10 lake env lean KernelTimeouts/F66Adj/After.lean
```
