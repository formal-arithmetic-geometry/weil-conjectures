STRUCTURE EXPOSURE AUDIT
========================

Case: PR1556-AmbientCounterexampleCoproducts
Source snapshot: Lean 4.35.0, revision 1ef1fddac73
Module identity: WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts

1. EXACT KERNEL COST SITE
-------------------------
Operation: inferred proposition type versus instantiated dependent domain of the final congr proof argument, inside Eq.mp in the original stored value.
Exact pair: the left CategoryStruct.comp in the congr proposition versus the expected composition; the outer Eq and carrier are cheap.
Profile: target type checking 54.9 s in situ; the precise congr-domain pair 50.090 s; the CategoryStruct.comp pair 49.758 s; NatTrans.app argument 6 is 47.366 s. Fresh SA replay: NatTrans.app original 49.100 s, aligned 0 ms, reverse right/aligned 46.355 s.
Stored value replay is 63.062 s; the expensive work is inside the proof value, not the final theorem type.

2. INITIAL MISMATCH SET
-----------------------
Mismatch 1: the NatTrans.app major premise, a concrete Iso.hom component, differs under the left CategoryStruct.comp.
Other NatTrans.app arguments compare in 0-2 ms. The enclosing proposition is proof-valued, but its type contains the data-bearing Iso/NatTrans composition.
Single causal trigger, not a bundle at the localized boundary.

3. CANDIDATE EXPOSURE BOUNDARY
------------------------------
CategoryStruct.comp is an abbrev with one-step projection body CategoryStruct.2. Its argument 6 is NatTrans.app, also an abbrev field accessor with projection body NatTrans.0.
The exact congr proposition domain is the comparison boundary. Directly measured in ClosingCongrDomain/ClosingComp/ClosingNatMajor and fresh probes; internal reduction order is inferred.

4. EXPOSED DATA-BEARING STRUCTURE
---------------------------------
  +-- congr proposition (Eq)
      +-- CategoryStruct.comp
          +-- Quiver.Hom carrier (cheap)
          +-- concrete morphism/category data (cheap at outer level)
          +-- NatTrans.app
              +-- eight arguments, mostly cheap
              +-- Iso.hom major premise (causal difference)
              +-- Functor.comp whiskering data
      +-- zero_comp proof and dependent proof domain
  +-- enclosing Eq.mp/id/Exists.intro proof spine
The data-bearing Iso and natural transformation are comparison-relevant. The proposition and proof wrappers are visible; they are not themselves sufficient to claim proof-only cost.

5. COST DISTRIBUTION
--------------------
Exists.intro arguments 0-2 check in 1/2/2 ms; final proof lambda checks in about 63 s. Eq.mp and congr descent localize the cost. Eight NatTrans.app arguments are individually 0-2 ms, while the accessor pair is 47-50 s. Profiler records 54.9 s target checking before and no target line above threshold after the fixed proof. No exact unfold counter table was emitted for this replay; the disappearance of the 50 s profiler node and 0 ms aligned replay is the reduction-footprint comparison.

6. CAUSAL CONTROL
-----------------
Original: same dependent congr proposition; NatTrans.app 49.100 s fresh, committed exact pair 49.548 s.
Aligned: replace only the right NatTrans.app major premise with the left; checked result type is structurally identical; 0 ms.
Restored: right original versus aligned right is 46.355 s fresh (50.585 s in the committed reverse replay). This restores the same accessor mismatch with the aligned term fixed, although pair orientation is reversed.
Same consumer/obligation: yes for the aligned/reverse probes. The elaborated pair changed at the intended major premise: yes.
Fixed-trigger object abstraction is valid and negative: the unchanged NatTrans.app major-premise mismatch still costs about 50 s; the wider dependent Iso/NatTrans bundle remains untested.

7. CLASSIFICATION
-----------------
P1, with a proof-domain boundary; contributing P3 only if repeated NatTrans occurrences in the enclosing proof are counted.
Confidence: Confirmed trigger and same-site cost removal; strongly supported exposure.
Directly measured: exact nested path, heads, projection bodies, all eight argument timings, alignment/restoration.
Inferred: precise Kernel delta order and field traversal.
Unresolved: separate contribution of reducibility hints versus the major premise.

8. MOST IMPORTANT RESULT
------------------------
A single concrete Iso.hom major-premise difference under an abbrev NatTrans.app prevents cheap comparison of a proof proposition's data-bearing type. Aligning it removes 49-50 s at the same dependent consumer; the reverse control restores the cost.

STRUCTURE EXPOSURE AND AMPLIFICATION ADDENDUM
=============================================

A. MISMATCH SEMANTICS
Syntactic divergence: concrete Iso.hom major premise.
DefEq obstruction: independently equal in about 2 ms, but expensive in the enclosing accessor.
Causal trigger: established by type-preserving major-premise alignment.
Single trigger or bundle: single trigger.

B. EXPOSURE
Candidate boundary: CategoryStruct.comp -> NatTrans.app projection.
One-step body: CategoryStruct.2 and NatTrans.0.
Visible-only: outer Exists/Eq/id proof wrappers and proof fields.
Measured comparison: NatTrans.app pair, then its major premise path.
Measured cost: 47.366-50.090 s.

C. COST MECHANISM
Structural traversal: concrete Iso/NatTrans component structure.
Reduction-heavy conversion: yes, inferred from abbrev projection path and profiler node.
Repeated conversion: enclosing proof spine repeats checks, but only one dominant NatTrans hotspot is localized.
Inclusive/exclusive: parent congr-domain timing includes nested composition; NatTrans timing is a child replay.
Reduction footprint: target profiler node 54.9 s versus aligned 0 ms; source declaration unfold counters are tabulated below, with exact-pair counters measured separately.

D. FIXED-TRIGGER ABLATION
Trigger preserved exactly: yes, at the NatTrans.app major premise.
Subtree abstracted: final object argument in a typed accessor helper.
Dependent telescope preserved: yes outside the new object parameter; E3 re-instantiates it.
E0/E1/E3: 53.328/50.375/46.789 s.
Conclusion: valid negative control for this object subtree; the larger dependent functor bundle is untested.

E. REDUCTION-PATH AUDIT
Same regular head: Eq and outer composition shared; CategoryStruct.comp/NatTrans.app are abbrev.
Reducibility hints: no same-body regular-hint matrix; contribution unresolved.
Argument comparison: eight NatTrans arguments all 0-2 ms.
One-sided exposure: projection body reached at the accessor.
Wrapper placement: concrete Iso.hom component is the differing major premise.
Directionality: both directions are slow.
Inference: exact branch order and proof irrelevance handling are inferred.

F. MISMATCH PROVENANCE
Producer: old closing proof's concrete whiskered derived-functor shift-isomorphism component.
Imported/local/generated: local closing proof inside imported theorem context.
Instance path: derived-functor/category instances are present but outer instance args are cheap.
Wrapper/raw path: NatTrans.app and CategoryStruct.comp abbrev accessors.
Proof abstraction/zeta/simp: historical simpa proof; fixed cancellation proof changes producer.
Dependent instantiation: congr proof argument is instantiated as a dependent domain under Eq.mp/id.
First provenance divergence: concrete Iso.hom component construction; first conversion-relevant divergence is NatTrans.app major premise.

G. CONCLUSION
P1; Level 2 measured exposure, with the aligned trigger established; Level 3 amplification is not established.
Strongest supporting result: same-consumer trigger alignment from about 50 s to 0 ms and reverse restoration.
Strongest contrary result: fixed-trigger abstraction of the final object leaves about 50 s of cost.
Next falsifying experiment: construct a typed whole-bundle abstraction preserving the congr proposition and test the fixed trigger.

ROUND 3: FIXED-TRIGGER TEST AND UNFOLD FOOTPRINT
-------------------------------------------------
`probes/sa/FixedTriggerAblation.lean` preserves the exact two `NatTrans.app` major-premise expressions, including their mismatch. It abstracts only the final object argument into a typed lambda whose body is the original accessor consumer; both helpers and their applications to the original objects Kernel-check. The generic helper result types differ syntactically and compare definitionally equal.

| E0 original accessor | E1 generic object | E3 helper at original object |
|---:|---:|---:|
| 53,328 ms | 50,375 ms | 46,789 ms |

This is a valid fixed-trigger ablation of one non-trigger subtree, but that subtree is not a substantial amplifier: the full accessor cost remains. The earlier claim of Level 3 amplification and the statement that no ablation was possible are superseded. Trigger alignment is still directly supported (53,328 ms to 0 ms in this run); surrounding-structure amplification remains unproved. The complete source/target functor arguments 4 and 5 are dependent on the retained `Iso.hom` major premise, so an additional wider helper must parameterize that telescope as one typed bundle. Whole-probe user CPU/wall/RSS: 317.39 s / 323.51 s / 7,849,224 KB.

Both historical source files check with diagnostics threshold 1000. The original target proof emits the following kernel table; the fixed target proof emits no kernel entry above threshold. The preceding theorem still emits the same 38,416 `Add.add` and 26,790 `Functor.obj` unfolds in both files.

| Kernel unfold | Original target | Fixed target |
|---|---:|---:|
| `Add.add` | 894,776 | below 1,000 |
| `Functor.obj` | 824,845 | below 1,000 |
| `DFunLike.coe` | 440,752 | below 1,000 |
| `NatTrans.app` | 129,110 | below 1,000 |
| `CategoryStruct.comp` | 27,257 | below 1,000 |

The target table disappears under the changed proof construction; it is not by itself the footprint of the exact major-premise alignment. Whole-file user CPU/wall/RSS: 60.46 s / 61.54 s / 7,838,908 KB original and 4.90 s / 5.73 s / 3,123,048 KB fixed. Round-three classification remains P1 for the aligned trigger, with Level 2 exposure and no established Level 3 amplification of the surrounding bundle.

ROUND 3: SAME-PROOF DECLARATION REPLAY
--------------------------------------
`probes/sa/DeclarationDiagnostics.lean` abstracts the original congr proof argument over its complete original telescope and synchronously Kernel-checks that same proof value against three domains: original, only the expected `NatTrans.app` major premise aligned, and the original domain restored. The checked helper is the original proof consumer at the exact congr argument site. Kernel diagnostics are reset between checks; all three checks are single-threaded (`-j1`) and the probe succeeds.

| Kernel unfold / check | Original | Aligned | Restored |
|---|---:|---:|---:|
| `Add.add` | 715,237 | 14 | 715,237 |
| `Functor.obj` | 700,986 | 44 | 700,986 |
| `DFunLike.coe` | 353,056 | 6 | 353,056 |
| `NatTrans.app` | 103,449 | 2 | 103,449 |
| `CategoryStruct.comp` | 21,625 | 4 | 21,625 |
| Synchronous kernel check | 50,228 ms | 9 ms | 47,224 ms |

The five large unfold families nearly vanish under exact major-premise alignment and return exactly when the original expected domain is restored. This is Level 1 trigger evidence and Level 2 measured exposure/reduction, not Level 3 amplification: the fixed-trigger object ablation above leaves the accessor cost. The three-check probe succeeded; whole-run wall/RSS were 221.63 s / 7,820,416 KB.
