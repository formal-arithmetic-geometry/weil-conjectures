# Q2 scalar-shift maintenance: correct dependency ownership

The repeated stage-3 rejection of Sheaf.Paper.CompactSupportScalarShiftNormalization
is caused by dependency records that conflate early coefficient-map definitions and
one proved generic mate identity with the later integral coefficient-comparison
theorem. The latter legitimately depends on scalar-shift normalization. Citing the
whole theorem from those earlier consumers creates a return path to normalization.

One explicit base cycle is normalization -> integral/rational compact-support
definition -> qcqs normalized lift -> integral coefficient comparison -> normalization.
There is a second qcqs finite-comparison route and a longer route through completed
compactification realization. Correcting only the first route leaves the item blocked.

This maintenance changes three records, with their mathematical statements and Lean
attachments preserved verbatim:

- lem-qcqs-compact-support-normalized-lift: the statement's finiteReductionIso and
  finiteImageIso are owned by the existing def-pur-finite-compact-support-scalar-data.
  The already cited def-sf-open-reduction-coefficient-mate owns reduction. Replace
  the broad coefficient-theorem statement prerequisite with the finite data node.
- lem-qcqs-compact-support-finite-comparison: its statement uses comparison from
  def-pur-integral-compact-support-coefficient-data and reduction from its existing
  open-reduction definition dependency. Remove the unrelated coefficient theorem
  from stmt_deps. Its proof uses the generic ordered mate identity, separately
  attached below; replace that proof_deps/step uses entry. Record it as a generic
  tool for the same proper/open argument, with no change to the unit route.
- lem-fix-compactification-completed-realization: its complete Lean proof uses
  comparison_factorization in a simpa step, rather than integralCoefficientComparison.
  Replace that proof dependency and step use with the exact helper attachment.

The new lem-pur-compact-support-comparison-factorization attaches the already proved
WeilConjectures.PurCompactSupport.comparison_factorization in
lean/Sheaf/Paper/IntegralCompactSupportCoefficientComparison.lean. Its proof is the
existing application of Mathlib mateEquiv_vcomp and definitional simplification.
Its actual maps are owned by the existing coefficient-data and finite-scalar-data
nodes. No theorem, proof, import, instance, mathematical statement, definition or
Lean source file is changed. No new hole is introduced.

The normalization item, the coefficient-comparison theorem and all their real
dependencies remain intact. This is a correction of the prerequisite ownership and
proof plan, not a statement_change and not a weakened statement.

Read-only verification of the retained six-module/eight-node packet invokes the
unmodified production edge_fails function: five cycle refusals before, none after.
All three corrected consumers and the exact helper attachment have no return path
to normalization. Controls still reject a first cycle and a missing dependency.
The final correction is also checked not to make any previously acyclic old node
cyclic, and not to introduce blueprint-record errors. Existing unrelated graph
cycles remain outside this repair.

Two optional Lean checks exposed limitations of the current server baseline.
The unchanged coefficient module exceeded the 60-second acceptance limit (82.6 s).
A scratch import check failed on the existing duplicate declaration
SheafOfModules.tensor_acyclic_of_isKFlat, supplied by both the Sheaf and
WeilConjectures AcyclicKFlatTensor modules; it was also rejected at 62.1 s.
Neither compile is claimed as a pass. There is no Lean change to validate in this
record-only repair; the earlier worker logs record successful compilation of all
six retained item modules. A fresh normal dry run must check the current baseline.

The previous maintenance diagnosis c665185e8935 identified the inherited-cycle
checker limitation but left the data unrepaired. This repair fixes the erroneous
prerequisites instead of editing or bypassing that protected checker. No launcher,
landing, review, admission, provider, concurrency, dispatch-state or retry-count
file is changed. Every changed server file has a .bak alongside it; absent new
files have an empty pre-creation backup.

Next worker: retain the existing sandbox decomposition and four named helper
holes. Refresh the shared repository, then run the normal deliver3.py Q2
Sheaf.Paper.CompactSupportScalarShiftNormalization --no-push. The five inherited
cycle refusals should be gone. Treat any compiler/artifact issue separately and
preserve its exact diagnostic. Continue through the ordinary delivery and review
path; this maintenance commit is not a proof delivery or review acceptance.

## Verified outcome, 2026-10-26

Dependency correction commit: 4f85eb86d8ce1acdaf99913d1e345d9e2b76fa7d.
The normal deliver3.py Q2 Sheaf.Paper.CompactSupportScalarShiftNormalization
--no-push completed with OK (dry run): compiles and passes the server preflight.
Its review class still requires independent reading of the proof decomposition.
The ordinary active worker then pushed delivery
bb474e6a275584436862e58a57b59fd1bb43a9ae; dispatcher recorded DELIVERED and
reset its failure count at 2026-10-26 00:00:47. The delivery branch exists on
the server. This is delivery success, not a claim that review or landing finished.

The full DAG check remains non-green on unrelated baseline findings. The repair
reduces cyclic-node membership from 193 to 175 in the observed live snapshots,
with no new missing-dependency or blueprint findings. The exact controlled
before/after regression separately checks no previously acyclic existing node
became cyclic. Protected production checkers and launcher files remain unchanged.
