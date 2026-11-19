# EtaleHomComparisonReversedExact

Origin: `8ca2e912b93` (2026-11-05), `WeilConjectures/AlgebraicGeometry/Etale/Hom/EtaleHomTransposeExactCommShiftComponent.lean`, declaration `etaleHomComparison_reversedExact_commShift_component`. No direct Zulip message ID was attached. The commit describes a 9.6 GB kernel conversion in the direct `exact` handoff.

`Before.lean` is the parent source with one mechanical current-master rename in the local irreducibility attribute: `_root_.DerivedCategory.instMonoidalCategory_weilConjectures` to `_root_.DerivedCategory.instMonoidalCategory`. The latter is defined in `WeilConjectures/FromJoel/Algebra/Homology/DerivedCategory/Monoidal.lean`; neither the theorem statement nor proof body changed. Without this rename, the parent fails at line 31 after 1:50.17 and 12,486,464 KB RSS, so that failure is not a theorem result. The ported Before succeeds in 1:50.07 and 12,487,664 KB RSS on 4.35.0. The fixed After succeeds in 3.50 s and 3,196,476 KB RSS. Both use the source's default 200000 heartbeat budget.

Kernel-skipped synchronous runs take 3.40 s and 3.30 s, respectively, which attributes the large difference to Kernel checking. The fix stores the generic shift-comparison theorem in `h`, transports the transpose premise along small leaves, then closes the concrete endpoint with `transport_exact`. This avoids unfolding `derivedHom` inside the final proof conversion. See `CLASSIFICATION.md` for the cost-site record.

Reproduce from `the master build tree` with `LEAN_NUM_THREADS=1 /usr/bin/time -v timeout 1800 nice -n 10 lake env lean KernelTimeouts/EtaleHomComparisonReversedExact/{Before,After}.lean`, running each file separately.
