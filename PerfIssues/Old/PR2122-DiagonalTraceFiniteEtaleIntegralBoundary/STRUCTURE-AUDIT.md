STRUCTURE EXPOSURE AUDIT
========================

Case: PR2122-DiagonalTraceFiniteEtaleIntegralBoundary
Source snapshot: Lean 4.35.0, revision 1ef1fddac73
Module identity: WeilConjectures.SixFunctors.ProEtale.DiagonalTrace

1. EXACT KERNEL COST SITE
-------------------------
Operation: stored value check of diagonalTrace_finiteEtale_integralBoundary, with terminal Exists.casesOn and dependent motive/witness/branch arguments.
Existing valid branch replay: motive check 16.115 s; stored witness/predicate branch 18.419 s, with branch body 2.212 s; final dependent branch cannot be checked independently.
Existing value replay: about 172.014 s; final inferred/declared conversion about 1 ms. Fresh SA in-situ audit reaches terminal Exists.casesOn (five arguments), runs 274.86 CPU s / 4:36.59 wall, and exits nonzero on dependent branch/type errors.
The exact inner branch conversion remains unisolated.

2. INITIAL MISMATCH SET
-----------------------
No proven first mismatch. The branch-local motive and witness types contain concrete DiagonalAb/sheaf-category, functor-composition, ring, and derived-category data named by the historical PR diagnosis. These are structural candidates only.
The stored value is proof-valued but its branch types contain data-bearing objects. Do not attribute cost to Exists.casesOn itself.

3. CANDIDATE EXPOSURE BOUNDARY
------------------------------
Terminal head is Exists.casesOn with five arguments. The candidate boundaries are motive, stored witness predicate, and final dependent branch. The final branch expected type depends on the recursor motive and witness and cannot be checked independently.
Directly measured: terminal head, branch-local checks from the valid committed probe, fresh failure location. Inferred: any concrete category/functor mismatch beneath the branch.

4. EXPOSED DATA-BEARING STRUCTURE
---------------------------------
  +-- Exists.casesOn
      +-- motive proposition
          +-- finite-etale/integral boundary data
          +-- category and functor parameters
      +-- witness/predicate branch
          +-- Kummer/Ext and derived-category objects
          +-- ring and site/module structures
      +-- dependent final branch
          +-- branch locals and instantiated expected type
          +-- evaluated integral Kummer class data
The motive and witness branches are comparison-relevant and actually expensive as branch checks. The final branch is visible but not independently attributable.

5. COST DISTRIBUTION
--------------------
Branch-local costs: motive 16.115 s; witness/predicate 18.419 s; witness branch body 2.212 s. The final dependent branch cannot be separated. Whole old value replay 172.014 s; current split module 29.87 s versus old 347.37 CPU s, but the split changes helper/import boundaries.
Reduction footprint: branch checks are the available same-context footprint; no unfold counter table or profiler node attribution was emitted for the fresh failing probe. The fresh probe's nonzero status is a validity failure, not a successful control.

6. CAUSAL CONTROL
-----------------
Original: full Exists.casesOn stored value and branch-local context.
Aligned: not available; no exact inner pair or type-preserving representation alignment.
Restored: not applicable.
Whole-bundle control: current split/factored module is a statement-level control only, not an in-situ branch replacement.
Experiment E: invalid because replacing or abstracting a branch changes the dependent motive and expected branch type.
Same consumer and obligation: preserved only in the original replay and branch inspection; no aligned pair exists.

7. CLASSIFICATION
-----------------
U (unclassified); P2/P4 are hypotheses only, not established.
Confidence: Confirmed branch-local cost and dependent recursor shape; unclassified exposure-to-cause connection.
Directly measured: terminal recursor, motive/witness checks, body check, old value replay, fresh failure.
Inferred: historical concrete category/functor candidates.
Unresolved: exact inner conversion and causal trigger.

8. MOST IMPORTANT RESULT
------------------------
The expensive work is inside the motive and witness branch checks of a dependent Exists.casesOn consumer, but no exact inner pair connects it to a data-bearing mismatch. This case remains a required negative/unresolved control.

STRUCTURE EXPOSURE AND AMPLIFICATION ADDENDUM
=============================================

A. MISMATCH SEMANTICS
Syntactic divergence: unknown at the expensive inner pair.
DefEq obstruction: branch checks are expensive; no specific obstruction isolated.
Causal trigger: unknown.
Single trigger or bundle: unknown.

B. EXPOSURE
Candidate boundary: Exists.casesOn motive/witness/final branch interface.
One-step body: terminal Exists.casesOn application with five arguments.
Visible-only: category/functor/ring structures listed by source.
Measured comparison: motive and witness branch checks.
Measured cost: 16.115/18.419 s; final branch unavailable.

C. COST MECHANISM
Structural traversal: possible dependent branch data.
Reduction-heavy conversion: possible, not isolated.
Repeated conversion: two measured branch components.
Inclusive/exclusive: branch checks are separate replays; whole value includes them.
Reduction footprint: branch timings only; no counters.

D. FIXED-TRIGGER ABLATION
Trigger preserved exactly: no trigger.
Subtree abstracted: branch/motive bundle.
Dependent telescope preserved: no.
Original/aligned/restored: original only; aligned/restored invalid.
Conclusion: invalid until an inner branch pair is extracted.

E. REDUCTION-PATH AUDIT
Same regular head: recursor head is shared for the original value, but no comparison matrix.
Reducibility hints: not available.
Argument results: motive and witness branch checks expensive; final branch type dependent.
One-sided exposure: branch locals after opening the recursor.
Wrapper placement: concrete categories/functors are source-guided only.
Directionality: not measured.
Inference: all inner reduction claims remain inferred.

F. MISMATCH PROVENANCE
Producer: old diagonal finite-etale/integral-boundary construction with local lets and concrete category/functor data.
Imported/local/generated: local theorem using imported derived-category infrastructure.
Instance path: historical candidates include ULift.ring versus CommRing.toRing; not re-extracted.
Wrapper/raw path: historical concrete category/functor representations.
Proof abstraction/zeta/simp: 12 lets and branch proof construction; zeta alone not shown causal.
Dependent instantiation: Exists motive supplies final branch type.
First provenance divergence: unknown; branch boundary is the first conversion-relevant interface observed.

G. CONCLUSION
U; evidence level 1 for branch-local cost, level 0 for trigger-to-structure causality.
Strongest supporting result: valid same-context motive/witness timings.
Strongest contrary result: final branch cannot be checked alone and fresh in-situ probe failed type checks.
Next falsifying experiment: extract a branch-local actual/expected pair after fully instantiating the motive and witness, then time its inner application arguments.
