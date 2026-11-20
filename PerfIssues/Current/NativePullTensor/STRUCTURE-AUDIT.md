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
A small concrete Functor.obj major-premise difference blocks the useful regular-head comparison. Aligning it removes the accessor cost; a fixed-trigger helper that abstracts the shared object reduces the same accessor comparison to 2-3 ms and re-instantiation restores about 11.3 s. The full Iso/Exists parent remains only partially attributed.

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
Trigger preserved exactly: yes, at both Functor.obj major premises.
Subtree abstracted: the shared object argument 5 in a typed accessor helper.
Dependent telescope preserved: yes outside the new object parameter; E3 re-instantiates the original data.
E0/E1/E3: 11.488/0.002/11.261 s at endpoint 2 and 11.300/0.003/11.271 s at endpoint 3.
Conclusion: Level 3 amplification of this object subtree at the accessor child.

E. REDUCTION-PATH AUDIT
Same regular head: Iso and Functor.comp yes; Functor.obj is abbrev.
Reducibility hints: regular/regular same-body 0 ms; abbrev/abbrev 11.251 s.
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
P1/P3; Level 3 for the fixed-trigger object ablation at the accessor child; Level 2 for the full Iso/Exists parent.
Strongest supporting result: 11.4 s original, 2-3 ms generic, and 11.3 s re-instantiated with the trigger unchanged.
Strongest contrary result: no direct Kernel trace or fixed-trigger ablation of the entire Iso/Exists parent.
Next falsifying experiment: parameterize a whole dependent endpoint bundle while retaining the exact Iso/Exists consumer, then restore it.

ROUND 3: FIXED-TRIGGER OBJECT ABLATION
--------------------------------------
`probes/sa/FixedTriggerAblation.lean` keeps both original `Functor.obj` major-premise expressions unchanged at each endpoint. It abstracts only argument 5, the shared concrete object, into a typed lambda helper whose body is the original accessor consumer. Both helper values and their re-instantiations Kernel-check. The helper's generic result types are not structurally identical, but the kernel finds them definitionally equal.

| Endpoint | E0 original | E1 generic object | E3 helper at original object |
|---|---:|---:|---:|
| source (2) | 11,488 ms | 2 ms | 11,261 ms |
| target (3) | 11,300 ms | 3 ms | 11,271 ms |

The original major-premise pair is byte-for-byte unchanged in E1. The generic helper retains the `Functor.obj` consumer and the original dependent telescope outside the new object parameter; E3 restores the original object and cost. This establishes Level 3 amplification for this non-trigger object subtree at the accessor child, not a field-by-field trace of the full `Iso`/`Exists` parent. The earlier statement in section D that no fixed-trigger ablation was valid is superseded. Whole-probe user CPU/wall/peak RSS: 116.18 s / 117.37 s / 6,182,556 KB.

The original source-level diagnostics (`probes/NativeDiagnostics.lean`, threshold 1000) show the following first hot declaration; later hot checks reach 1,550,252 `Functor.obj` unfolds. These declaration counts are inclusive of their own kernel checks and do not isolate the accessor child.

| Kernel unfold | Original first hot declaration |
|---|---:|
| `Functor.obj` | 1,104,002 |
| `Functor.map` | 463,500 |
| `NatTrans.app` | 204,584 |
| `CategoryStruct.comp` | 129,480 |

The source-level run checks successfully (271.97 s wall, 8,016,840 KB peak RSS). The exact E0/E1/E3 accessor timing above is the causal attribution; declaration counters remain reduction evidence only.

ROUND 3: SAME-VALUE DECLARATION REPLAY
--------------------------------------
`probes/sa/DeclarationDiagnostics.lean` synchronously Kernel-checks the original `nativePullTotalTensor` value three times under the original binder telescope. The middle type aligns only the two expected `Functor.obj` major premises at endpoints 2 and 3; both replacements have the same checked type as the original endpoint. The third type restores the original expected expressions. Diagnostics were reset before each check, with kernel counting enabled in each returned environment (`-j1`, threshold 1000 for the source comparison above).

| Kernel unfold / check | Original | Aligned | Restored |
|---|---:|---:|---:|
| `Functor.obj` | 1,550,252 | 1,033,514 | 1,550,252 |
| `Functor.map` | 650,880 | 433,920 | 650,880 |
| `NatTrans.app` | 287,292 | 191,528 | 287,292 |
| `CategoryStruct.comp` | 181,752 | 121,168 | 181,752 |
| `Eq.ndrec` | 107,712 | 71,808 | 107,712 |
| Synchronous kernel check | 72,873 ms | 51,621 ms | 79,526 ms |

Each listed unfold shrinks by about one third under alignment and returns exactly on restoration; none disappears. The still-expensive aligned parent demonstrates additional reduction beyond these two accessor triggers. These counts are per whole cloned declaration, so they do not prove which individual Functor fields were traversed. The separate fixed-trigger object ablation above establishes the object's causal contribution only at the accessor child. The three-check probe succeeded; whole-run wall/RSS were 253.50 s / 7,942,012 KB.
