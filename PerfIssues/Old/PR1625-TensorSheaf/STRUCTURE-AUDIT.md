STRUCTURE EXPOSURE AUDIT
========================

Case: PR1625-TensorSheaf
Source snapshot: Lean 4.35.0, revision 1ef1fddac73
Module identity: WeilConjectures.SixFunctors.ProEtale.TensorSheaf

1. EXACT KERNEL COST SITE
-------------------------
Operation: final inferred/declared Eq type conversion for leftDerivedUpperStarTensorComparison_app_app_fac.
Exact pair: shared Eq headed result; left CategoryStruct.comp argument 5 is an outer NatTrans.app, whose argument 6 is a nested NatTrans.app major-premise pair.
Committed timings: outer final conversion 95.520 s; nested NatTrans.app 95.717 s; outer composition 96.236 s; aligned replay 0 ms; reverse 93.567 s. Fresh SA replay measured nested arg 6 at 92.732 s, outer original 94.368 s, aligned 0 ms, reverse 94.907 s before nonzero source-probe errors.
Stored value/application checks are cheap (stored replay 335 ms; last application domains 0/338/0/0 ms).

2. INITIAL MISMATCH SET
-----------------------
Mismatch 1: concrete NatTrans.app major premise at the nested argument 6 differs.
The outer and inner NatTrans.app heads and all other arguments are shared or cheap. The type is data-bearing even though the final theorem is proposition-valued.
Single trigger repeated at two nested accessor boundaries.

3. CANDIDATE EXPOSURE BOUNDARY
------------------------------
CategoryStruct.comp and NatTrans.app are abbrev accessors. One-step bodies are projections CategoryStruct.2 and NatTrans.0.
The outer Eq reaches the left composition, then outer NatTrans.app, then nested NatTrans.app argument 6. This path is directly measured in ResultLhsArguments/NatTransMajor and the fresh SA output.

4. EXPOSED DATA-BEARING STRUCTURE
---------------------------------
  +-- Eq result
      +-- CategoryStruct.comp
          +-- outer NatTrans.app
              +-- nested NatTrans.app
                  +-- concrete natural-transformation major premise (causal)
                  +-- Functor.obj parameters and derived tensor comparison data
                  +-- component object and category instances
          +-- other composition arguments (cheap)
      +-- dependent Eq proposition
The nested transformation and derived tensor functor data are comparison-relevant and actually expensive at the accessor pair. Individual underlying fields are visible but not independently attributed.

5. COST DISTRIBUTION
--------------------
One dominant nested NatTrans.app conversion repeats inside the outer composition. Parent outer-composition timing is inclusive. The old target check is 87.6 s in situ and 95.520 s imported replay; the fixed theorem target is 2.43 s. Fresh SA meta compile had source errors but still emitted the same-site 94.368/0/94.907 s replay.
Reduction footprint: profiler target 87.6 s versus 2.43 s; aligned replay 0 ms and no nested slow node. No unfold counters were emitted.

6. CAUSAL CONTROL
-----------------
Original: nested NatTrans.app major-premise pair 95.869 s committed; 94.368 s fresh replay.
Aligned: replace only right nested major premise with left; checked result type structurally identical; 0 ms.
Restored: right-original versus aligned-right 93.567 s committed; 94.907 s fresh replay. This holds the aligned term fixed and restores the original mismatch in reverse orientation.
Same consumer/obligation: yes for the direct replay, but the fresh SA source file has unrelated proof-probe errors and is not treated as a valid source proof.
Experiment E: a typed helper successfully abstracts the final object while keeping the nested major-premise mismatch, but the same accessor still costs about 99 s; a wider dependent bundle remains untested.

7. CLASSIFICATION
-----------------
P1, with repeated nested accessor exposure (P3).
Confidence: Confirmed for the major-premise trigger and same-site removal/restoration; strongly supported for the nested data structure.
Directly measured: exact heads, projection bodies, argument timings, alignment/restoration, before/after profile.
Inferred: precise reduction order and inner major-premise provenance.
Unresolved: same-body regular-hint separation and a valid fixed-trigger ablation.

8. MOST IMPORTANT RESULT
------------------------
A single nested NatTrans.app major-premise difference accounts for about 95 s of the final conversion. Aligning it removes the cost while preserving the result type; reverse restoration returns the cost.

STRUCTURE EXPOSURE AND AMPLIFICATION ADDENDUM
=============================================

A. MISMATCH SEMANTICS
Syntactic divergence: nested NatTrans major premise.
DefEq obstruction: independently equal only after expensive reduction.
Causal trigger: established by type-preserving alignment.
Single trigger or bundle: single trigger at a nested repeated boundary.

B. EXPOSURE
Candidate boundary: Eq -> CategoryStruct.comp -> NatTrans.app -> nested NatTrans.app.
One-step body: projections CategoryStruct.2/NatTrans.0.
Visible-only: outer Eq proof data and non-hot component fields.
Measured comparison: nested NatTrans.app major premise.
Measured cost: 92.732-95.869 s.

C. COST MECHANISM
Structural traversal: natural-transformation/component data.
Reduction-heavy conversion: yes; profiler and projection path support this.
Repeated conversion: outer plus nested NatTrans.app, one dominant inner hotspot.
Inclusive/exclusive: outer composition includes nested app; direct nested replay is separate.
Reduction footprint: 87.6/2.43 s profiler, 0 ms aligned child, and source declaration unfold counters tabulated below.

D. FIXED-TRIGGER ABLATION
Trigger preserved exactly: yes, at the nested NatTrans.app major premise.
Subtree abstracted: final object argument in a typed accessor helper.
Dependent telescope preserved: yes outside the new object parameter; E3 re-instantiates it.
E0/E1/E3: 93.985/98.710/97.520 s.
Conclusion: valid negative control for this object subtree; the dependent functor bundle is untested.

E. REDUCTION-PATH AUDIT
Same regular head: Eq and composition heads shared; app accessors are abbrev.
Reducibility hints: no same-body regular control.
Argument results: outer arguments 0-5 and 7 are 0-3 ms; nested arg 6 is about 93 s.
One-sided exposure: app projection exposes the nested major premise.
Wrapper placement: concrete transformation under abbrev accessor.
Directionality: both directions slow.
Inference: internal delta path unresolved.

F. MISMATCH PROVENANCE
Producer: concrete derived tensor natural transformation construction.
Imported/local/generated: local historical proof with imported derived-category data.
Instance path: category and object parameters are cheap.
Wrapper/raw path: NatTrans.app abbrev over concrete transformation.
Proof abstraction/zeta/simp: fixed proof establishes whole-NatTrans equality; historical component proof keeps concrete path.
Dependent instantiation: final Eq result and component application.
First provenance divergence: concrete nested transformation major premise.

G. CONCLUSION
P1/P3; Level 2 measured exposure; Level 3 amplification is not established.
Strongest supporting result: same-site alignment and restoration around 95 s.
Strongest contrary result: fixed-trigger abstraction of the final object leaves about 99 s of cost.
Next falsifying experiment: typed bundle abstraction retaining the complete dependent natural-transformation telescope.

ROUND 3: FIXED-TRIGGER TEST AND UNFOLD FOOTPRINT
-------------------------------------------------
`probes/sa/FixedTriggerAblation.lean` retains the original nested `NatTrans.app` major-premise pair and abstracts only the final object into a typed lambda helper whose body is the same outer accessor. The helper and its re-instantiation Kernel-check; the generic result types are syntactically different but definitionally equal.

| E0 original accessor | E1 generic object | E3 helper at original object |
|---:|---:|---:|
| 93,985 ms | 98,710 ms | 97,520 ms |

The selected object is not a substantial amplifier: the fixed trigger remains expensive when that object is abstract. The earlier Level 3/no-valid-ablation statements are superseded. The adjacent functor arguments are dependent on the retained transformation major premise; a wider E2 control must abstract their complete typed telescope. This probe emitted the checked child results despite unrelated earlier errors at source lines 108 and 390, and exited nonzero. Its whole-run CPU/wall/RSS was 659.45 s / 655.90 s / 8,697,404 KB; those whole-run numbers are not valid theorem-check benchmarks.

The historical `Before.lean` and `After.lean` diagnostics at threshold 1000 emitted these final-target kernel unfold tables. Both source runs also failed at earlier proofs (lines 108 and 390), so the tables are bounded target-check diagnostics rather than successful full-file measurements. The fixed proof changes construction, not just the exact major premise.

| Kernel unfold | Original target | Fixed target |
|---|---:|---:|
| `AddGroup.toSubNegMonoid` | 1,380,313 | 43,713 |
| `Functor.obj` | 1,319,711 | 39,306 |
| `Preadditive.homGroup` | 1,317,524 | 41,720 |
| `NatTrans.app` | 1,044,058 | 33,098 |
| `Add.add` | 508,722 | 16,162 |
| `CategoryStruct.comp` | 376,956 | 11,886 |

No listed unfold vanishes entirely; these counts shrink roughly 96-97% in the changed-proof target. They show reduction-heavy work but do not prove that the final object subtree contributes. P1 trigger alignment and P3 nested hotspots remain supported; amplification of the surrounding bundle is not established (Level 2, not Level 3).

ROUND 3: SAME-VALUE DECLARATION REPLAY
--------------------------------------
`probes/sa/DeclarationDiagnostics.lean` synchronously Kernel-checks the same original theorem value against three full types under its original telescope. The middle type changes only the expected nested `NatTrans.app` major premise; the third restores the original full type. Kernel counting is reset before every variant and the run uses `-j1`. The three target declarations each pass the synchronous kernel check. The probe file exits nonzero because of the earlier source errors at lines 108 and 390, so these remain bounded target-check measurements.

| Kernel unfold / check | Original | Aligned | Restored |
|---|---:|---:|---:|
| `AddGroup.toSubNegMonoid` | 1,380,313 | 43,761 | 1,380,313 |
| `Functor.obj` | 1,319,711 | 39,268 | 1,319,711 |
| `Preadditive.homGroup` | 1,317,524 | 41,768 | 1,317,524 |
| `NatTrans.app` | 1,044,058 | 33,124 | 1,044,058 |
| `CategoryStruct.comp` | 376,956 | 11,900 | 376,956 |
| Synchronous kernel check | 102,896 ms | 2,671 ms | 97,859 ms |

All listed unfold families shrink about 97% on alignment and return exactly under restoration, but none disappears entirely. The remaining 2.7 s and roughly 3% of unfolds belong to other reduction in the same checked theorem; the nested child comparison is the dominant trigger but not the only work. The fixed-trigger object abstraction above leaves the child slow, so this table does not establish Level 3 amplification of that object or the wider dependent bundle. Whole-probe wall/RSS were 378.71 s / 8,628,164 KB; the exit status was 1 solely because of the earlier source errors.
