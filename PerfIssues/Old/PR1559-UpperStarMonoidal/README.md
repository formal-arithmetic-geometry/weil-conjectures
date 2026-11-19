# PR1559: UpperStarMonoidal

The historical before source was ported from the merge parent, but it does not compile cleanly against the current 4.35.0 build: three unrelated API/instance errors occur before the target comparison declarations. Its run consumed 217.50 user CPU seconds and peaked at 9,047,180 KB before exiting 1. The current fixed source (PR merge `0dd6d4a3ff04a02f2ab476b7fb48cd5d7ffbd93c`) is part of master and is described by the PR's controlled measurement: 697 s / 7.0 GB before versus 140 s / 2.4 GB after, with target kernel checks 707 s and 637 s before versus 42 s and 3.3 s after.

The porting stop is recorded because the old source's API drift exceeded the 20-minute time box. The review's requested mechanism is clear from the change: a named `Prop` (`LaxSquareHδ`) and a named `app_app_comp_of_eq` keep the kernel from unfolding the commutative square and compare instances argument by argument. This is a representation/interface mismatch with reduction-heavy conversions (E primary, A contributing), supported by the PR's target timings and source diff; no current before/after proof pair is claimed.

