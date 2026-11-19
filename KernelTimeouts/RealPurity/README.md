# RealPurity

Origin: `e2d8b540cba` (2026-11-07), `WeilConjectures/WeilSheaf/RealPurity.lean`, declaration `IsReal.exists_isPunctuallyPureOfWeight_cokernel_detWeight`. No direct Zulip message ID was attached. The fixing commit split a long proof into `as_aux_lemma` blocks.

`Before.lean` is the complete parent source and reproduces `(kernel) deterministic timeout` at line 241 in 58.94 s wall, 5,590,352 KB peak RSS. `After.lean` is the complete fixing revision, but its generated auxiliary proof still times out at line 327 in 58.84 s, 5,584,740 KB RSS on Lean 4.35.0. Thus the historical fix is no longer sufficient on this tree. The current master source, kept as `Master.lean`, passes in 6.10 s and 4,015,364 KB RSS. The historical sources were already compatible with current imports; no proof-term port was made.

With `-DElab.async=false -Ddebug.skipKernelTC=true`, Before and After finish in 7.40 s and 7.80 s. This confirms that the timeout is in Kernel checking. The split changes proof abstraction boundaries for the constituent representation, local polynomial, and final stalk calculations. Master contains later changes beyond this split, so its success must not be attributed to `e2d8b540cba` alone. See `CLASSIFICATION.md` for the phase and mechanism record.

Reproduce from `the master build tree` with `LEAN_NUM_THREADS=1 /usr/bin/time -v timeout 1800 nice -n 10 lake env lean KernelTimeouts/RealPurity/{Before,After,Master}.lean`, running each file separately.
