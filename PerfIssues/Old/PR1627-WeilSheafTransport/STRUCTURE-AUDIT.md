STRUCTURE EXPOSURE AUDIT
========================

Case: PR1627-WeilSheafTransport / powFunctor generated fields
Source snapshot: Lean 4.35.0, revision 1ef1fddac73
Module identity: WeilConjectures.WeilSheaf.BaseChangeField.Transport

1. EXACT KERNEL COST SITE
-------------------------
Operation: generated field value checks for powFunctor._proof_1 and _proof_2, specifically the dependent id argument-1 proposition-domain conversions.
Fresh SA field replay: _proof_1 value 20.902 s; _proof_2 value 33.713 s; both final inferred/declared conversions 0 ms. Existing generated-prefix replay localizes id-domain conversions at 7.508 s and 33.863 s. In-situ generated checks are 27.8, 55.3, and 14.6 s.
The final theorem type is structurally identical and not the hot site.

2. INITIAL MISMATCH SET
-----------------------
Mismatch 1: the proposition type supplied to id argument 0 differs from the instantiated dependent domain of id argument 1.
The exact first inner data mismatch below that proposition has not been dumped in this round. Historical source diagnosis names frobeniusPowPullback versus WeilSheaf.frobeniusPullback, but that is structurally inferred here.
Bundle status: one dependent proposition/domain mismatch per generated law; repeated across two generated fields.

3. CANDIDATE EXPOSURE BOUNDARY
------------------------------
The outer value is id with two arguments; id is regular. The costly boundary is the forall/proposition domain for argument 1 after preceding binders are instantiated.
No outer projection is present. The dependent domain is directly measured; the nested data-bearing boundary is inferred.

4. EXPOSED DATA-BEARING STRUCTURE
---------------------------------
  +-- concrete Functor.mk value for powFunctor
      +-- carrier/object/map data
      +-- generated law _proof_1
      |   +-- id proposition domain
      |       +-- Functor-law Eq proposition
      |       +-- concrete frobenius pullback functor data
      +-- generated law _proof_2
          +-- id proposition domain
              +-- longer dependent telescope
              +-- same pullback/functor vocabulary
The id domains are comparison-relevant and actually expensive. Functor fields and law propositions are visible; the exact inner leaf is not measured.

5. COST DISTRIBUTION
--------------------
Repeated generated-field work: _proof_1 20.902 s and _proof_2 33.713 s fresh; historical in-situ fields 27.8/55.3/14.6 s. The first two share id argument-1 dependent-domain shape but have different telescopes. After generic helper control has no generated checks above 50 ms and costs 9.38 CPU s versus 107.63 old prefix.
Reduction footprint: generated value replay and profiler nodes above; final conversions 0 ms. No per-operation unfold counter table was emitted.

6. CAUSAL CONTROL
-----------------
Original: concrete Functor.mk generated fields with id-domain conversion.
Aligned: no valid one-factor major-premise alignment; replacing the generated proof or data would change the generated law proposition.
Restored: not applicable.
Experiment E: invalid without inventing proof constants or changing the law telescope. The generic IsoAlgebra helper is a whole-construction control, not fixed-trigger ablation.
Same consumer: yes for the field replay; no valid representation symmetry matrix.

7. CLASSIFICATION
-----------------
P3 repeated generated-field exposure; P2 dependent bundle is plausible; U for the exact inner trigger.
Confidence: Strongly supported for repeated field/domain cost; plausible for concrete functor mismatch.
Directly measured: generated declarations, id heads, binders, value/final split, field replay timings.
Inferred: historical pullback-functor mismatch and downstream data exposure.
Unresolved: first inner differing expression and fixed-trigger restoration.

8. MOST IMPORTANT RESULT
------------------------
The project pays the same dependent id-domain conversion mechanism in two generated law fields. The generic construction removes those concrete generated checks, but no valid single mismatch alignment has yet been isolated.

STRUCTURE EXPOSURE AND AMPLIFICATION ADDENDUM
=============================================

A. MISMATCH SEMANTICS
Syntactic divergence: proposition type versus instantiated id argument-1 domain; inner data divergence unknown.
DefEq obstruction: proposition types are definitionally equal but expensive to compare.
Causal trigger: dependent id-domain mismatch established as the hot boundary; concrete functor leaf remains unproven.
Single trigger or bundle: repeated dependent bundle across two fields.

B. EXPOSURE
Candidate boundary: id argument-1 dependent forall domain.
One-step body: id is regular lambda; no projection at outer body.
Visible-only: concrete Functor.mk fields and generated proof constants.
Measured comparison: id proposition domain.
Measured cost: 7.508/33.863 s domain comparisons; field values 20.902/33.713 s.

C. COST MECHANISM
Structural traversal: generated law proposition and functor data.
Reduction-heavy conversion: yes, but exact operations unknown.
Repeated conversion: confirmed across _proof_1 and _proof_2.
Inclusive/exclusive: field value includes its proof-domain work; domain replay is a child.
Reduction footprint: field replays and profiler nodes; no counters.

D. FIXED-TRIGGER ABLATION
Trigger preserved exactly: no isolated trigger.
Subtree abstracted: concrete functor/proof construction.
Dependent telescope preserved: no.
Original/aligned/restored: original measured; aligned/restored invalid.
Conclusion: invalid fixed-trigger ablation.

E. REDUCTION-PATH AUDIT
Same regular head: id is regular; no projection at outer body.
Reducibility hints: no differing-head hint control.
Argument comparison: id argument 0 cheap; argument 1 proposition domain 7.508/33.863 s.
One-sided exposure: dependent forall domain after argument 0.
Wrapper placement: concrete Functor.mk law construction.
Directionality: not measured.
Inference: exact inner pullback-functor path remains inferred.

F. MISMATCH PROVENANCE
Producer: hand-built concrete Functor.mk and generated law fields.
Imported/local/generated: generated declarations from local powFunctor.
Instance path: concrete WeilSheaf/frobenius pullback data; no leaf dump.
Wrapper/raw path: concrete functor construction versus generic IsoAlgebra helper.
Proof abstraction/zeta/simp: generated id proof wrappers; no source simp control.
Dependent instantiation: preceding binders determine id argument-1 domain.
First provenance divergence: generated proposition construction; first conversion-relevant domain is id argument 1.

G. CONCLUSION
P3, with U/P2 at the inner trigger; evidence level 2 for repeated exposure and level 1 for trigger provenance.
Strongest supporting result: two independent generated fields reproduce the same hot dependent-domain shape.
Strongest contrary result: no one-factor alignment or restoration.
Next falsifying experiment: print and align the first inner pullback-functor major premise while preserving each generated law telescope.
