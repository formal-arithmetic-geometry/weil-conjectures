STRUCTURE EXPOSURE AUDIT REPORT
==============================

Scope: seven PerfIssues cases assigned to this share.
Snapshot: Lean 4.35.0, revision 1ef1fddac73.
All fresh probes were invoked with one Lean thread, timeout 3600, and
/usr/bin/time -v from the generated build tree. No library source was
changed.

CASE RESULTS

| Case | Principal cost site | Initial mismatch | Boundary | R7 classification | Confidence | Evidence |
|---|---|---|---|---|---|---|
| NativePullTensor | Iso endpoint / Exists.choose domains | Functor.obj major premise | abbrev Functor.obj projection | P1/P3 | confirmed | Level 3 trigger; Level 2 exposure |
| PR1556 | congr proposition domain | NatTrans.app Iso.hom major premise | CategoryStruct.comp -> NatTrans.app | P1 | confirmed | Level 3 |
| PR1563 | Eq.mpr final domain | seven dependent comp arguments | Eq.mpr -> CategoryStruct.comp | P2/P3, possible P4 | plausible | Level 1 |
| PR1624 | isoWhiskerLeft final domain | four dependent endpoint arguments | Iso -> Functor.comp | P2/P4 | strongly supported exposure | Levels 1-2 |
| PR1625 | final Eq type | nested NatTrans.app major premise | CategoryStruct.comp -> NatTrans.app | P1/P3 | confirmed | Level 3 |
| PR1627 | generated law values | id argument-1 proposition domain | dependent forall/id domain | P3, inner U | plausible | Level 2 repeated exposure |
| PR2122 | Exists.casesOn value branches | unknown | motive/witness/final dependent branch | U | unclassified | Level 1 branch cost only |

ROUND-2 PROBE EXECUTION

| Case | Probe | Result | User CPU / wall | Peak RSS |
|---|---|---|---:|---:|
| NativePullTensor | probes/sa/ExposureAlignment.lean | success | 93.80 s / 1:38.53 | 6,176,600 KB |
| PR1556 | probes/sa/ExposureAlignment.lean | success | 213.20 s / 3:39.24 | 7,841,544 KB |
| PR1563 | probes/sa/CompositionChildren.lean | success | 155.77 s / 2:40.14 | 8,060,484 KB |
| PR1624 | probes/sa/EndpointChildren.lean | invalid final dependent replacement | 19.14 s / 0:17.98 | 3,232,132 KB |
| PR1625 | probes/sa/ExposureAlignment.lean | diagnostics emitted; source probe errors | 454.86 s / 7:26.64 | 8,681,504 KB |
| PR1627 | probes/sa/GeneratedFields.lean | success | 160.38 s / 2:42.20 | 8,202,080 KB |
| PR2122 | probes/sa/BranchAudit.lean | diagnostics emitted; dependent branch errors | 274.86 s / 4:36.59 | 14,398,876 KB |

The nonzero probes are retained as bounded diagnostics. Their measured
outputs are used only where the exact pair and checked type were valid;
the valid committed probes are the source for the corresponding baseline
and restoration numbers.

SECTION 6: ORIGINAL / ALIGNED / RESTORED

| Case | Original | Aligned | Restored | Same consumer/obligation | Outcome |
|---|---:|---:|---:|---|---|
| NativePullTensor endpoint Functor.obj | 11.396/11.355 s | 0 ms | 11.284/11.301 s reverse | yes for checked replay | trigger and reversible cost return confirmed |
| PR1556 NatTrans.app | 49.548 s (fresh 49.100) | 0 ms | 50.585 s committed (fresh 46.355) reverse | yes for checked replay | trigger and reversible cost return confirmed |
| PR1625 nested NatTrans.app | 95.869 s (fresh 94.368) | 0 ms | 93.567 s committed (fresh 94.907) reverse | yes for checked replay | trigger and reversible cost return confirmed |

"Restored" is the aligned-term reverse control: the original mismatching
representation is reintroduced while the aligned term is held fixed.
This preserves the exact replay consumer; it is not a new source
declaration.

SECTION 10: DATASET COVERAGE

A. Corpus coverage
All 7/7 cases have an exact cost site or a bounded branch-local site,
an exposed-structure tree, and a direct/inferred evidence label.
Exact trigger-to-inner-pair extraction is complete for NativePullTensor,
PR1556, and PR1625; partial for PR1563, PR1624, and PR1627; unresolved
for PR2122.

B. Causal coverage
Three cases (NativePullTensor, PR1556, PR1625) have same-site,
type-preserving alignment that removes both the expensive conversion and
the measured child footprint. Four cases have no valid one-factor
alignment because dependent bundles or branch telescopes would change.

C. Kernel-time coverage
Using one principal historical/in-situ target per case:
NativePullTensor 265 s, PR1556 54.9 s, PR1563 68.2 s, PR1624 102 s,
PR1625 87.6 s, PR1627 97.7 s (three generated fields), and PR2122
172.0 s for the replayed final value: 847.4 s total.
The confirmed P1/P3 alignment cases account for 407.5 s, 48.1% of this
principal total. Including the distributed/bundle PR1563 and PR1624
sites gives 577.7 s, 68.2%, but their trigger is not isolated.
PR2122 remains excluded from causal coverage.

SECTION 15.4: PRODUCER-MECHANISM GROUPING

- Accessor over separately constructed major premises:
  NativePullTensor, PR1556, PR1625. Each has a Functor.obj or NatTrans.app
  abbrev boundary and a type-preserving major-premise alignment.
- Concrete dependent composition bundle:
  PR1563 and PR1624. CategoryStruct.comp or Functor.comp exposes several
  coupled functor/morphism endpoint arguments; independent substitutions
  are ill-typed or insufficient.
- Generated proof/data construction:
  PR1627. Hand-built Functor.mk law fields create repeated dependent id
  domains; the generic helper removes the generated checks.
- Dependent recursor branch construction:
  PR2122. Exists.casesOn motive and witness checks are expensive, but the
  producer mismatch is not yet extracted.

SECTION 16: MATCHED FAST CONTROLS

| Slow case | Fast control | What it shows |
|---|---|---|
| NativePullTensor | same-module self comparisons / aligned major premise | large Iso/Functor vocabulary is cheap when representations share a regular path |
| PR1556 | preceding theorem in same prefix, about 2.03 s | surrounding derived-category context is not sufficient for the 50 s hotspot |
| PR1563 | shared helper, 32.4-32.7 s in both old/fixed forms | helper/import cost is distinct from the old target proof cost |
| PR1624 | earlier declarations, about 2 s in both forms | the category hierarchy alone does not explain the endpoint hotspot |
| PR1625 | earlier declaration, about 15.4 s in both forms | derived-category context is shared while the nested component is not |
| PR1627 | generic IsoAlgebra helper, 9.38 CPU s and no generated checks above threshold | generated concrete law fields drive the repeated cost |
| PR2122 | current factored module, 29.87 CPU s | statement-level factoring helps, but is not a same-site alignment |

SECTION 17: EVIDENCE LEVELS AND FALSIFICATION

- NativePullTensor: Level 3. Falsifier: a valid fixed-trigger
  endpoint abstraction leaves the same endpoint cost.
- PR1556: Level 3. Falsifier: a typed whole-bundle abstraction leaves
  the congr-domain cost after the major premise is fixed.
- PR1563: Level 1. Falsifier: a valid whole-endpoint alignment leaves
  the distributed composition cost unchanged.
- PR1624: Level 1 localization / Level 2 exposure. Falsifier: a typed
  whole-endpoint control fails to change the endpoint footprint.
- PR1625: Level 3. Falsifier: a typed bundle abstraction leaves the
  nested NatTrans.app cost after major-premise alignment.
- PR1627: Level 2 repeated exposure. Falsifier: the two generated fields
  remain equally expensive after the first inner pullback-functor premise
  is aligned.
- PR2122: Level 1 branch cost only. Falsifier: a fully instantiated
  branch-local pair shows that the branch data are cheap and the cost is
  elsewhere.

OBSERVATIONS (DIRECT MEASUREMENTS)

1. NativePullTensor, PR1556, and PR1625 each have a same-site major-
   premise alignment changing approximately 11.4, 49-50, and 94-96
   seconds to 0 ms, with structurally identical checked result types.
2. PR1563 distributes measured work across seven composition arguments;
   PR1624 distributes it across complete dependent endpoints; neither
   accepts a valid isolated replacement.
3. PR1627 repeats the dependent id-domain shape in two generated fields.
4. PR2122 has valid 16.115 s motive and 18.419 s witness branch checks,
   but its final dependent branch cannot be checked independently.
5. Native's counters include 1,104,002 Functor.obj and 463,500
   Functor.map unfolds in the first hot check; counters are downstream
   reduction activity, not an execution trace.
6. The fresh PR1624 and PR2122 probes rejected dependent replacements;
   the fresh PR1625 probe emitted the alignment timings before unrelated
   source-probe errors.

INTERPRETATIONS (LABELLED)

- The three reversible cases support P1: a small accessor major-premise
  difference can expose a large data-bearing functor/natural-transformation
  comparison.
- PR1563 and PR1624 support a bundle/repeated-work interpretation, but
  their exact first trigger is not established; do not count them as
  confirmed P1 causal coverage.
- PR1627 supports repeated generated-field exposure, not a proven
  concrete-functor leaf trigger.
- PR2122 is a negative/unresolved control. Its Exists recursor is a
  consumer boundary, not an established cause.
- The share therefore has confirmed Level-3 amplification for three of
  seven cases, partial Level-1/2 exposure for three, and one unresolved
  case. This is strong local evidence for the high-level mismatch to
  large-structure mechanism, without claiming that it explains all seven.
