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
Experiment E: fixed-trigger non-trigger subtree abstraction is invalid because dependent transformation application and Eq result type would change.

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
Reduction footprint: 87.6/2.43 s profiler and 0 ms aligned child.

D. FIXED-TRIGGER ABLATION
Trigger preserved exactly: no valid non-trigger abstraction.
Subtree abstracted: surrounding transformation/composition bundle.
Dependent telescope preserved: no.
Original/aligned/restored: 95.869/0/93.567 s committed; fresh 94.368/0/94.907 s.
Conclusion: invalid ablation; restoration is valid.

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
P1/P3; evidence level 3.
Strongest supporting result: same-site alignment and reverse restoration around 95 s.
Strongest contrary result: no valid subtree ablation and no unfold counters.
Next falsifying experiment: typed bundle abstraction retaining the complete dependent natural-transformation telescope.
