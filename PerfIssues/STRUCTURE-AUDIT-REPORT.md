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
| NativePullTensor | Iso endpoint / Exists.choose domains | Functor.obj major premise | abbrev Functor.obj projection | P1/P3 | confirmed child amplification | Level 3 child; Level 2 parent |
| PR1556 | congr proposition domain | NatTrans.app Iso.hom major premise | CategoryStruct.comp -> NatTrans.app | P1 | confirmed trigger | Level 2 exposure; object ablation negative |
| PR1563 | Eq.mpr final domain | seven dependent comp arguments | Eq.mpr -> CategoryStruct.comp | P2/P3, possible P4 | plausible | Level 1 |
| PR1624 | isoWhiskerLeft final domain | four dependent endpoint arguments | Iso -> Functor.comp | P2 candidate / U | historical localization only | Level 1; target counters blocked |
| PR1625 | final Eq type | nested NatTrans.app major premise | CategoryStruct.comp -> NatTrans.app | P1/P3 | confirmed trigger, bounded source | Level 2 exposure; object ablation negative |
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
Three cases (NativePullTensor, PR1556, PR1625) have type-preserving
same-site trigger alignment. Fixed-trigger abstraction of a non-trigger
object establishes amplification only for NativePullTensor's two accessor
children; the corresponding PR1556 and PR1625 object abstractions are
valid negative controls. Four cases still lack a type-preserving
one-factor alignment of their relevant dependent bundles or branches.

C. Kernel-time coverage
Using one principal historical/in-situ target per case:
NativePullTensor 265 s, PR1556 54.9 s, PR1563 68.2 s, PR1624 102 s,
PR1625 87.6 s, PR1627 97.7 s (three generated fields), and PR2122
172.0 s for the replayed final value: 847.4 s total.
The three principal targets associated with established trigger
alignments sum to 407.5 s (48.1% of the 847.4 s historical total), but
that is an association, not attributed kernel cost. The localized
controlled accessor children total about 168.5 s across those cases
(two 11.4 s Native endpoints, 50 s PR1556, 95.7 s PR1625), or 19.9%
of the historical principal total. Only the two Native children, about
22.8 s, have a positive fixed-trigger subtree ablation. These site
totals use different scopes and cannot establish project prevalence.
PR1563, PR1624, and PR2122 are excluded from causal cost coverage.

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

- NativePullTensor: Level 3 for the shared object at the accessor child;
  the full Iso/Exists parent remains Level 2. Falsifier: a wider
  dependent bundle control leaves the full parent cost unchanged.
- PR1556: Level 2. A valid object ablation leaves about 50 s of cost;
  a wider typed dependent-bundle control is the next falsifier.
- PR1563: Level 1. Falsifier: a valid whole-endpoint alignment leaves
  the distributed composition cost unchanged.
- PR1624: Level 1 historical localization; the current source fails
  before the target, so target-level reduction and Level 2 remain open.
- PR1625: Level 2. A valid object ablation leaves about 99 s of cost;
  a wider typed transformation bundle is the next falsifier.
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
- The share has one confirmed Level-3 child amplification, two other
  confirmed accessor triggers whose selected object subtrees do not
  amplify cost, three partial bundle/repeated-work cases, and one
  unresolved recursor case. The broad large-structure mechanism remains
  a case-level hypothesis outside the Native accessor child.

ROUND 3: KERNEL UNFOLD AND ABLATION RESULTS
-------------------------------------------
The exact three-way rows below are synchronous checks of the same stored value/proof against original, aligned, and restored types. Other rows are original versus best historical source controls and therefore change the producer. Counts are kernel unfolds, not a trace of field traversal.

| Case | Counter (original / aligned or best / restored) | Fixed-trigger E result | Validity |
|---|---|---|---|
| NativePullTensor | `Functor.obj` 1,550,252 / 1,033,514 / 1,550,252 | object helper 11.5 s / 2 ms / 11.3 s; positive at child | exact declaration replay and helper pass |
| PR1556 | `Add.add` 715,237 / 14 / 715,237 | object helper 53.3 / 50.4 / 46.8 s; negative for object | exact proof-domain replay and helper pass |
| PR1563 | `Add.add` 1,287,366 / 246,362 / n.a. | no established trigger for E | both source controls pass; changed producer |
| PR1624 | target table unavailable | E not assigned | old and fixed sources fail before target; missing `constantSheafTowerIsoQuotPow` |
| PR1625 | `NatTrans.app` 1,044,058 / 33,124 / 1,044,058 | object helper 94.0 / 98.7 / 97.5 s; negative for object | target clone checks pass; earlier source errors remain |
| PR1627 | `Eq.ndrec` 1,939,320 / no matching generated check / n.a. | E not assigned | both source controls pass; changed construction |
| PR2122 | no round-three table requested | E not assigned | prior branch-local result remains unresolved |

For Native, the aligned whole-declaration check still takes 51.6 s and retains about two thirds of the selected unfolds; the 2-3 ms result belongs specifically to the fixed-trigger accessor child. PR1556's exact aligned proof-domain check takes 9 ms and its selected counters fall to 2-44 events. PR1625's exact aligned theorem check takes 2.7 s and retains roughly 3% of the selected unfolds. Restored counts in all three exact replays match the original counts exactly.

Level 3 amplification is established for Native's selected object subtree at two accessor children. The valid PR1556 and PR1625 object abstractions leave the trigger cost and so weaken amplification claims for those particular subtrees; a wider typed dependent bundle remains untested. No Level 4 or Level 5 project conclusion follows from this share. PR1624's target-level R6 remains blocked by the concrete source errors stated in its case report.
