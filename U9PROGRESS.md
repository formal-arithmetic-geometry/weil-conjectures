# K4a — Nailin strategy 1

2026-11-05 19:41 CST: Started from C1-k4repro c6a69c87e. Target is finite Tate reading kernel conversion, then canonical Tate scalar. This overrides the historical projection-formula leaf assignment in the boilerplate; route (B) comparison is unrelated to this assigned implementation bottleneck. No local Lean/Lake; no heartbeat increases.

19:42: Baseline ucheck ec39b3fb1f: CoeffSynInstance + original reading (inherited 2M diagnostic remains unchanged at this baseline only). Log /home/ubuntu/u9/logs/K4a-20261105T194229.log, poolr:43.157.132.198. Read NOTES and k4-experiments. Prior C1 Syn log193556 confirms synHread kernel56.8s and bridge59.6s timeouts.

19:46: Prepared new K4CoefficientInterface / K4CoefficientComposition. Explicit no_expose coeffType/coeffRingObj, all instances and data consistently use synonyms, rfl characterizations, individually normalized input squares, separate consumer. profiler.threshold 0 measures all declarations. This avoids editing C1-owned files and tests real import opacity. Baseline still running.
