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
Fixed-trigger ablation: invalid. Abstracting the surrounding Iso/NatTrans bundle changes the dependent congr proposition and the proof obligation.

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
Reduction footprint: target profiler node 54.9 s versus aligned 0 ms; counters unavailable.

D. FIXED-TRIGGER ABLATION
Trigger preserved exactly: not valid for a non-trigger subtree.
Subtree abstracted: surrounding whiskered Iso/NatTrans data.
Dependent telescope preserved: no.
Original/aligned/restored: 49.100/0/46.355 s fresh; committed reverse 50.090/0/50.585 s.
Conclusion: invalid ablation; restoration of the trigger is valid.

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
P1; evidence level 3 for trigger plus surrounding bundle, level 2 for measured exposure.
Strongest supporting result: same-consumer alignment from about 50 s to 0 ms and reverse restoration.
Strongest contrary result: no fixed-trigger subtree ablation and no unfold counter table.
Next falsifying experiment: construct a typed whole-bundle abstraction preserving the congr proposition and test the fixed trigger.
