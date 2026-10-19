# Q05 trace/logarithmic-determinant route maintenance

The retained stage-1 split of thm-weil-grothendieck-lefschetz-trace removes an unused downstream determinant premise. This exposed the transport unit's missing independent sk-prop-logdet route: its Euler-product node cited prop-trace-determinant, whose geometric clause depends through prop-every-iterate-trace to the trace theorem. Previously the only sk-prop-logdet carrier in that closure was reached through the removed premise.

Repaired only thm-trf-l-function-euler-product Steps 1 and 5 and their dependency/tool records. The E-stage now cites the closed pure linear-algebra lemma lem-weil-exp-trace-determinant; the algebraically closed Frobenius-module case cites lem-zl-euler-product-identity, exactly as blueprint main-20261015 Step 0 does. Finite alternating products use the already-cited exponential homomorphism. No statement, coefficient hypothesis, unit route, worker item, checker, launcher, or Lean source changed.

Read both identity statements and the main-20261015 Euler-product proof. The general lemma covers arbitrary characteristic-zero E and noninvertible endomorphisms. The Qbar lemma is used only on the finite-dimensional Frobenius modules supplied by Step 2. Empty graded families give 1; a shift reverses the determinant exponent. The existing Lean records mark both identity declarations closed.

Validation before installation: server-side unit/route comparison with the retained Q05 worker overlay introduces no findings, the logdet finding is absent, no dependency cycle is introduced, and review_split passes for both the repaired node and the worker item. Full worker delivery preflight will be recorded in the maintenance run REPORT.md.

Backup: dag/nodes/sec-trace-formula/thm-trf-l-function-euler-product.json.maint-Q05-logdet-1792207044.bak.
