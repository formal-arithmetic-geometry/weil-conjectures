STRUCTURE EXPOSURE AUDIT
========================

Case: PR1563-RawModuleScalarPullback
Source snapshot: Lean 4.35.0, revision 1ef1fddac73
Module identity: WeilConjectures.AlgebraicGeometry.RawModuleScalarPullback

1. EXACT KERNEL COST SITE
-------------------------
Operation: fourth Eq.mpr application-domain conversion under the original 12 binders.
Exact pair: actual type of Eq.refl versus the instantiated final Eq.mpr binder domain; both Eq-headed. The differing right CategoryStruct.comp is the inner cost site.
Baseline committed measurements: target Kernel check 68.2 s; stored-value replay 93.833 s; final domain pair 30.254 s; right composition 31.026 s.
Fresh SA replay compiled successfully. Its seven outer composition arguments individually compare in 0, 1, 0, 0, 1, and 3 ms at the inspected prefix; this is a child-localization probe, not a replacement for the original in-situ cost.

2. INITIAL MISMATCH SET
-----------------------
Mismatch bundle: all seven CategoryStruct.comp arguments are structurally different in the exact pair. Independent timings from the committed EqCompArguments replay are 1 ms, 0 ms, 2.245 s, 2.079 s, 2.146 s, 6.601 s, and 22.155 s; nested argument 6 is another composition.
This is not a single established trigger. The final Eq.refl proof is proof-valued, but the cost is in data-bearing composition types.

3. CANDIDATE EXPOSURE BOUNDARY
------------------------------
Eq.mpr is regular, height 1, and one-step exposes Eq.rec. CategoryStruct.comp is an abbrev whose one-step body is projection CategoryStruct.2.
Shared Eq and composition heads allow descent until the right composition's concrete arguments diverge. The exact first inner divergence is not isolated.

4. EXPOSED DATA-BEARING STRUCTURE
---------------------------------
  +-- Eq.mpr / Eq.rec
      +-- Eq proposition
          +-- AddCommGrpCat carrier (cheap)
          +-- left CategoryStruct.comp (cheap)
          +-- right CategoryStruct.comp
              +-- seven concrete functor/morphism/category arguments
              +-- nested CategoryStruct.comp at argument 6
                  +-- higherDirectImageRawOverFunctor path
                  +-- raw module source/coefficient maps
                  +-- unop/op Over and derived-category data
      +-- Eq.refl proof
The full composition bundle is visible and comparison-relevant. Measured cost exists for every outer argument in the committed replay, with the nested composition dominant. No individual field is proven causally sufficient.

5. COST DISTRIBUTION
--------------------
Outer right composition: 31.026 s; nested argument 6: 22.155 s as an independent child (parent timings overlap). Outer arguments 2-5 cost 2.079-6.601 s. The shared helper takes 32.4-32.7 s in both old and fixed forms; target checks are 68.2/15.2 s. Fresh SA compile CPU/wall 155.77/160.14 s with seven child timings 0-3 ms; this compile includes imports and meta inspection.
Reduction footprint: profiler target 68.2 s versus 15.2 s; no per-operation unfold counter table was emitted for this probe. The measured repeated child costs establish distributed conversion rather than one independently sufficient leaf.

6. CAUSAL CONTROL
-----------------
Original: complete dependent Eq.mpr domain with seven differing composition arguments.
Aligned: no valid single-argument replacement; Kernel.check rejects it because dependent morphism endpoints change.
Restored: not applicable; no type-preserving trigger alignment exists.
Same consumer preserved: yes for the negative control; no valid whole-bundle replacement was available.
Experiment E fixed-trigger ablation: invalid because abstracting one composition argument changes the dependent morphism type. The required whole-bundle control is the existing fixed helper, but it changes the producer and is not a same-site alignment.

7. CLASSIFICATION
-----------------
P2 bundle-triggered exposure plus P3 distributed/repeated composition work; P4 remains possible for the reduction-heavy composition.
Confidence: Plausible for the bundle shape; unclassified for one causal trigger.
Directly measured: exact Eq.mpr boundary, common heads, seven child timings, nested composition, before/after target profile.
Inferred: which divergence first forces the expensive path.
Unresolved: valid whole-endpoint alignment and reduction counters.

8. MOST IMPORTANT RESULT
------------------------
Several dependent composition differences jointly prevent cheap comparison of the right CategoryStruct.comp. Work is distributed across seven arguments, with nested argument 6 dominant; no one-factor alignment is type-preserving.

STRUCTURE EXPOSURE AND AMPLIFICATION ADDENDUM
=============================================

A. MISMATCH SEMANTICS
Syntactic divergence: seven composition arguments.
DefEq obstruction: independent children range from milliseconds to seconds; the whole dependent composition is not cheap.
Causal trigger: bundle only; no isolated trigger established.
Single trigger or bundle: bundle.

B. EXPOSURE
Candidate boundary: Eq.mpr domain -> right CategoryStruct.comp.
One-step body: Eq.rec and CategoryStruct.2.
Visible-only: proof Eq.refl and some category instances.
Measured comparison: all seven composition arguments and nested comp.
Measured cost: 2.079-22.155 s child timings; 31.026 s parent.

C. COST MECHANISM
Structural traversal: multiple concrete functor/morphism arguments.
Reduction-heavy conversion: likely; shared helper and historical proof unfold concrete definitions.
Repeated conversion: yes, seven arguments plus nested composition.
Inclusive/exclusive: nested argument timing overlaps the parent.
Reduction footprint: profiler 68.2/15.2 s; no counters.

D. FIXED-TRIGGER ABLATION
Trigger preserved exactly: no trigger isolated.
Subtree abstracted: any single comp argument.
Dependent telescope preserved: no.
Original/aligned/restored: original only; aligned/restored invalid.
Conclusion: invalid ablation; whole-bundle control remains needed.

E. REDUCTION-PATH AUDIT
Same regular head: Eq.mpr regular and CategoryStruct.comp abbrev.
Reducibility hints: no same-body matrix.
Argument results: seven arguments all structurally differ; fresh probe sees 0-3 ms at its reduced child prefix, committed replay sees seconds at exact domain.
One-sided exposure: Eq.rec then CategoryStruct.2.
Wrapper placement: concrete raw pullback versus abstract module-factor helper.
Directionality: not measured as a valid aligned pair.
Inference: exact first reduction path remains unknown.

F. MISMATCH PROVENANCE
Producer: old concrete higherDirectImageRawOverFunctor/raw pullback construction.
Imported/local/generated: local theorem using imported concrete functors and factors.
Instance path: category argument leaf is cheap; no instance-only cause.
Wrapper/raw path: concrete higherDirectImageRawOverFunctor versus raw-pullback helper.
Proof abstraction/zeta/simp: historical simp/rfl proof unfolds multiple definitions.
Dependent instantiation: Eq.mpr fourth binder supplies the dependent Eq.refl domain.
First provenance divergence: concrete composition bundle; first conversion-relevant divergence is right composition.

G. CONCLUSION
P2/P3, evidence level 1 localization and below level 2 causal exposure.
Strongest supporting result: seven exact child timings and nested composition distribution.
Strongest contrary result: no valid one-factor alignment; fresh SA child timings are cheap in a reduced replay context.
Next falsifying experiment: build a typed whole-endpoint control preserving all seven dependent arguments, then compare its footprint.
