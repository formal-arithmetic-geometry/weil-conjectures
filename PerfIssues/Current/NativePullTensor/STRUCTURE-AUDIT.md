STRUCTURE EXPOSURE AUDIT
========================

Case: NativePullTensor / nativePullTotalTensor
Source snapshot: Lean 4.35.0, revision 1ef1fddac73
Module identity: WeilConjectures.WeilSheaf.Native.NativePullTensor

1. EXACT KERNEL COST SITE
-------------------------
Operation: application-domain and final Iso conversions in the stored value/type of nativePullTotalTensor; the same endpoint conversion recurs in adjacent declarations.
Exact final pair: inferred and declared Iso expressions under the original 12 binders, both headed by CategoryTheory.Iso, with Functor.comp source and target endpoints.
Nested exact pair: corresponding Functor.obj applications under the two Functor.comp endpoints.
Baseline: final replay 23.422 s; endpoint children 11.453 s and 11.390 s; Functor.obj children 11.346 s and 11.240 s. The two Exists.choose dependent-domain conversions are 23.012 s and 23.065 s. The source prefix has four hot checks of 51.5, 80.5, 79.3, and 52.5 s (committed HEAD-AUDIT record).
Stored value checks are individually cheap at the localized endpoint; the expensive work is in inferred/declared type and application-domain conversion.

2. INITIAL MISMATCH SET
-----------------------
Mismatch 1: Functor.obj major-premise argument (the concrete Functor.uncurry term) differs between inferred and expected endpoint objects.
Mismatch 2: the full positional diff also contains generated _proof_3 versus Sheaf.monoidalPreadditive; that difference was inspected but not independently timed.
The first causal mismatch is a single accessor major-premise difference. The Exists.choose domains are dependent manifestations of the same representation difference.

3. CANDIDATE EXPOSURE BOUNDARY
------------------------------
Outer heads: Iso, then Functor.comp, then Functor.obj.
Functor.comp is regular (height 1), with one-step body Functor.mk. Functor.obj is an abbrev whose one-step body is projection Functor.0.
All six Functor.obj arguments compare in 0-1 ms; the enclosing accessor comparison is slow.
Directly measured: heads, bodies, arguments, and timings in probes/sa/ExposureAlignment.lean and committed head probes. Inferred: the exact internal Kernel reduction order.

4. EXPOSED DATA-BEARING STRUCTURE
---------------------------------
Conversion root: Iso source/target endpoint.
  +-- Functor.comp source/target
  |   +-- category and functor parameters (cheap at this level)
  |   +-- Functor.obj accessor
  |       +-- concrete Functor.uncurry major premise (first causal boundary)
  |       +-- object nativeTensorTotal (structurally identical)
  |       +-- dependent object/map arguments
  +-- Exists.choose predicate and witness domains
      +-- Iso endpoint type
      +-- concrete functor/instance parameters
      +-- proof-valued dependent proposition
Visible structure is the Iso/Functor/Exists tree. The Functor.obj major premise is comparison-relevant and actually expensive. The surrounding Functor fields and proof field are visible; their independent costs are not isolated. Major-premise replacement is causally contributing.

5. COST DISTRIBUTION
--------------------
Conversion tree: final Iso -> two Functor.comp endpoints -> one Functor.obj child per endpoint. The two Exists.choose domain conversions are separate repeated sites. Endpoint timing is inclusive of its child.
Reduction footprint: committed NativeDiagnostics records, on the first hot check, 1,104,002 Functor.obj, 463,500 Functor.map, 204,584 NatTrans.app, and 129,480 CategoryStruct.comp unfolds; later checks have about 1.55 million Functor.obj unfolds. These counters are downstream activity, not a Kernel trace. Same-body regular/regular replay is 0 ms, while abbrev/abbrev is 11.251 s.

6. CAUSAL CONTROL
-----------------
Original: Functor.obj major-premise pair 11.396/11.355 s; full final replay 23.422 s.
Aligned: replace only the right Functor.obj functor argument with the left one; result type remains structurally identical and Kernel-checks; both endpoint comparisons are 0 ms.
Restored: reverse original-right versus aligned term is 11.284/11.301 s, restoring the same slow accessor conversion with the aligned term held fixed. This is the available reversible control; it reverses the pair orientation rather than rebuilding the source declaration.
Same consumer and obligation: yes for the aligned term. Elaborated pair changed at the intended major premise: yes. Footprint/cost changed: yes at the measured site; aligned replay has no measurable child work.

7. CLASSIFICATION
-----------------
P1, with repeated exposure at two endpoints and two Exists.choose domains; contributing P3.
Confidence: Confirmed for the Functor.obj abbrev/major-premise causal factor; strongly supported for the larger downstream functor structure.
Directly observed: exact heads, projection body, child timings, type-preserving alignment, reverse restoration, and unfold counters.
Inferred: internal reduction sequence and which individual Functor fields account for the counters.
Unresolved: independent role of _proof_3 and the exact source of every downstream unfold.

8. MOST IMPORTANT RESULT
------------------------
A small concrete Functor.obj major-premise difference blocks the useful regular-head comparison and opens the surrounding Functor.comp/Exists endpoint structure. Aligning that one premise removes the same conversion; restoring the mismatch restores the cost. A fixed-trigger subtree ablation was invalid: parameterizing the surrounding endpoint would change the dependent Iso/Exists consumer.

STRUCTURE EXPOSURE AND AMPLIFICATION ADDENDUM
=============================================

A. MISMATCH SEMANTICS
Syntactic divergence: yes, at the concrete Functor.uncurry major premise.
DefEq obstruction: the terms are definitionally equal only after expensive reduction; the direct comparison is not cheap.
Causal trigger: the Functor.obj major-premise difference, established by alignment.
Single trigger or bundle: single trigger at each endpoint; repeated across two endpoints.

B. EXPOSURE
Candidate boundary: abbrev Functor.obj projection under regular Functor.comp.
One-step body: projection Functor.0; Functor.comp exposes Functor.mk.
Visible-only nodes: most concrete Functor fields and _proof_3.
Measured comparison: Functor.obj major-premise pair and Exists.choose domains.
Measured cost: 11.2-11.4 s per endpoint and 23.0 s per dependent domain.

C. COST MECHANISM
Structural traversal: endpoint and dependent-domain comparisons.
Reduction-heavy conversion: yes; unfold counters are large.
Repeated conversion: yes, two endpoints and two choose domains.
Inclusive/exclusive: endpoint times include their Functor.obj child; child timings are separate.
Reduction footprint: counters above; aligned child is 0 ms.

D. FIXED-TRIGGER ABLATION
Trigger preserved exactly: no valid in-situ ablation.
Subtree abstracted: endpoint Functor/Exists bundle.
Dependent telescope preserved: no; abstraction would alter the consumer.
Original/aligned/restored cost: 11.396/0/11.284 s (reverse restoration).
Conclusion: invalid ablation, but major-premise restoration is valid.

E. REDUCTION-PATH AUDIT
Same regular head: Iso and Functor.comp yes; Functor.obj is abbrev.
Reducibility hints: regular/regular same-body 0 ms; abbrev/abbrev 11.251 ms.
Argument results: all six Functor.obj arguments independently 0-1 ms.
One-sided exposure: Functor.obj exposes Functor.0; both-sided aligned premise is immediate.
Wrapper placement: regular wrapper removes the cost only when both sides share the regular head.
Directionality: original and reverse are both about 11.3 s.
Inference: exact Kernel branch order is not directly observable.

F. MISMATCH PROVENANCE
Producer: separate concrete functor construction in the native tensor declaration and its expected type.
Imported/local/generated: local declaration with generated proof fields; expected type stored by elaboration.
Instance path: concrete coefficient/category instances; no independently expensive instance leaf.
Wrapper/raw path: Functor.obj abbrev over Functor.uncurry.
Proof abstraction/zeta/simp: let-bound endpoint data and generated proof field are present; no proof-only causal claim.
Dependent instantiation: Exists.choose domains instantiate the predicate after preceding binders.
First provenance divergence: concrete Functor major premise; first conversion-relevant divergence is the Functor.obj accessor.

G. CONCLUSION
P1/P3; evidence level 3 for the accessor trigger and level 2 for surrounding-structure exposure.
Strongest supporting result: type-preserving alignment and reverse restoration at the same child conversion.
Strongest contrary result: no valid fixed-trigger subtree ablation and no direct Kernel trace.
Next falsifying experiment: parameterize a whole dependent endpoint bundle while retaining the exact Iso/Exists consumer, then restore it.
