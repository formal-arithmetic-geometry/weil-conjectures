STRUCTURE EXPOSURE AUDIT
========================

Case: PR1624-IntegersSheafHomologyTower
Source snapshot: Lean 4.35.0, revision 1ef1fddac73
Module identity: WeilConjectures.SixFunctors.ProEtale.IntegersSheafHomologyTower

1. EXACT KERNEL COST SITE
-------------------------
Operation: final isoWhiskerLeft argument-domain conversion in the seven-argument Iso.trans application.
Exact pair: inferred type of isoWhiskerLeft versus the instantiated final Iso.trans domain. Both are Iso-headed; source and target endpoints are Functor.comp applications.
Committed timings: final domain 47.636 s; source endpoint 14.706 s; target endpoint 28.640 s; target in-situ Kernel check 102 s; stored-value replay 117.578 s.
The fresh SA EndpointChildren probe attempted the same endpoint inspection and ran 17.98 s CPU before failing to Kernel-check its constructed final iso argument; its errors are recorded as an invalid isolated replacement, not as a new timing.

2. INITIAL MISMATCH SET
-----------------------
Mismatch bundle: endpoint arguments 2, 3, 6, and 7 are independently structurally unequal (0-8 ms checks) under the shared Functor.comp heads.
At the whole endpoint, the actual argument 6 is a Functor.comp while the expected side has higherDirectImageQuotPowTower. Four dependent endpoint differences are jointly coupled.

3. CANDIDATE EXPOSURE BOUNDARY
------------------------------
Outer heads: Iso, then Functor.comp. Functor.comp is regular height 1 with one-step body Functor.mk.
The shared Iso carrier and category instance compare in 0 ms; endpoint comparison is the boundary where congruence fails.
These observations are from committed IsoDomainArguments/IsoCompArguments probes; exact Kernel branch order is inferred.

4. EXPOSED DATA-BEARING STRUCTURE
---------------------------------
  +-- Iso.trans
      +-- Iso carrier Functor and category instance (cheap)
      +-- isoWhiskerRight endpoint
      +-- isoWhiskerLeft endpoint
          +-- Functor.comp source and target
              +-- concrete derived-category functor data
              +-- higherDirectImageQuotPowTower
              +-- object/map fields and nested whiskering parameters
              +-- four dependent endpoint arguments
The complete endpoint bundle is comparison-relevant. Functor.mk fields are visible after one-step reduction; individual fields were not isolated as expensive.

5. COST DISTRIBUTION
--------------------
The final isoWhiskerLeft value checks in 63.855 s; its final domain conversion is 47.636 s. Source/target endpoint conversions are 14.706/28.640 s. Four corresponding endpoint arguments are independently unequal in 0-8 ms, so the expensive work is in complete endpoint reduction rather than one cheap child. Before/after target checks are 102/3.18 s; previous declarations are about 2 s in both forms.
Reduction footprint: target profiler 102 s versus 3.18 s. Eleven let-bindings remain after value-frame substitution; explicit zeta does not remove the endpoint cost. No unfold-counter table was emitted.

6. CAUSAL CONTROL
-----------------
Original: final Iso domain with four dependent endpoint differences.
Aligned: no valid single-argument replacement; Kernel.check rejects substitutions because endpoint data changes dependent types.
Restored: not applicable.
Same consumer preserved: yes for the failed negative controls; no valid whole-endpoint generic replacement was available in the SA probe.
Whole-bundle control required by the assignment: the fixed source passes functors to homologyIntegersTowerIsoAux, but this changes the producer and is not a same-site alignment.
Experiment E: invalid until a whole endpoint bundle can be abstracted without changing the Iso.trans telescope.

7. CLASSIFICATION
-----------------
P2 bundle-triggered exposure; P4 reduction-heavy concrete endpoint expansion is plausible.
Confidence: Strongly supported for the complete endpoint exposure, plausible for causal amplification.
Directly measured: exact dependent domain, endpoint times, shared heads, unequal child arguments, failed type-preserving replacements.
Inferred: downstream Functor.mk field traversal and exact reduction order.
Unresolved: whole-endpoint aligned/restored footprint.

8. MOST IMPORTANT RESULT
------------------------
Four dependent endpoint differences jointly force reduction past shared Functor.comp into complete concrete Functor data. Independent leaf replacements are ill-typed, so this case is evidence for bundle coupling rather than a single mismatch.

STRUCTURE EXPOSURE AND AMPLIFICATION ADDENDUM
=============================================

A. MISMATCH SEMANTICS
Syntactic divergence: four endpoint arguments.
DefEq obstruction: complete endpoints are equal only after expensive concrete reduction; corresponding leaves are independently unequal.
Causal trigger: bundle-level endpoint representation; no single leaf trigger.
Single trigger or bundle: bundle.

B. EXPOSURE
Candidate boundary: Iso.trans final domain -> Functor.comp endpoints.
One-step body: Functor.mk.
Visible-only: eleven let-bound values and proof fields.
Measured comparison: complete source/target endpoints.
Measured cost: 14.706/28.640 s and final domain 47.636 s.

C. COST MECHANISM
Structural traversal: complete Functor endpoint bundles.
Reduction-heavy conversion: yes; regular Functor.comp expansion is necessary.
Repeated conversion: two endpoints and four coupled argument positions.
Inclusive/exclusive: final domain includes endpoint work; source/target are child replays.
Reduction footprint: profiler 102/3.18 s; no counters.

D. FIXED-TRIGGER ABLATION
Trigger preserved exactly: no isolated trigger.
Subtree abstracted: one endpoint argument.
Dependent telescope preserved: no.
Original/aligned/restored: original measured; aligned/restored invalid.
Conclusion: invalid one-factor ablation; whole endpoint control required.

E. REDUCTION-PATH AUDIT
Same regular head: Iso outer and Functor.comp endpoints.
Reducibility hints: regular height 1; no hint asymmetry shown.
Argument results: endpoint args 2/3/6/7 unequal in 0-8 ms; complete endpoint is slow.
One-sided exposure: Functor.comp -> Functor.mk.
Wrapper placement: concrete compositions under iso whiskering.
Directionality: no valid aligned direction.
Inference: exact field comparison sequence is unknown.

F. MISMATCH PROVENANCE
Producer: direct construction of concrete derived-functor compositions under two iso whiskerings.
Imported/local/generated: local historical theorem with imported functor infrastructure.
Instance path: category carrier/category instance cheap; concrete functor data differ.
Wrapper/raw path: concrete Functor.comp versus named higherDirectImageQuotPowTower.
Proof abstraction/zeta/simp: eleven lets substituted; zeta alone does not remove cost.
Dependent instantiation: final isoWhiskerLeft domain after six Iso.trans arguments.
First provenance divergence: endpoint composition bundle.

G. CONCLUSION
P2/P4; evidence level 1 for localization, level 2 for exposure, not level 3.
Strongest supporting result: complete endpoint timings and invalid independent substitutions.
Strongest contrary result: no valid whole-endpoint alignment.
Next falsifying experiment: construct a whole dependent endpoint bundle control with the original Iso.trans consumer.
