## Worker report

Item: lem-trf-invariant-coordinate-transfinite-filtration. Group NK, stage 1, 2026-10-23.

Files written:
- dag/nodes/sec-trace-formula/lem-trf-invariant-coordinate-transfinite-filtration.json: item, split into six steps; statement unchanged.
- dag/nodes/sec-trace-formula/lem-trf-well-order-ordinal-enumeration.json: statement, Mathlib leaf, exact Ordinal.enum at Mathlib/SetTheory/Ordinal/Basic.lean:472 (read 466–490).
- citations.json: one verbatim statement quotation for each dependency of every proof step.
- report.md and the actual msearch.py log searches.jsonl.

Attachments: none. Searching lean/WeilConjectures/ by the exact item/tag and by invariant coordinate, transfinite, Kaplansky and 058X found no declaration giving the item. The Kaplansky hits concern the UFD criterion. The existing Sheaf/RingTheory/CoordinateSubmodule.lean defines the coordinate submodule, but does not prove the item. No Lean was written or compiled.

WANTED: none.

The imported node is mathematically correct. Its statement, statement dependencies, source, inherited citations and search records are retained. There was no prior sandbox item or report; searches.jsonl was absent initially. The item was an unsplit helper of the Kaplansky direct-summand split. Its source already assumes the countable invariant blocks here, so this proof must not redo countable-coordinate-closure or add countable generation of the N_j. A_α is tracked as a subset, not inferred from M_{A_α}: if N_j=0, equality of coordinate submodules does not imply equality of subsets.

The latest blueprint ancestor lem-trf-local-term-locality and its latest proof now concern contracting correspondences and no longer contain the old flatification branch. I read the latest statement and proof and the chapter/unit records. The inherited source chain through 0593, 058Y and 058X is historical provenance. This delivery splits the still-live 058X helper without altering the ancestor, chapter, unit or parent proof route; no SGA source is used.

Unfinished work: none for this one-level split. The only newly introduced node is an exact Mathlib leaf, with no proof or proof dependencies.

## Searches and reuse

Whole-DAG searches for transfinite recursion, well-ordering, ordinal enumeration, order type, Ordinal.enum, Ordinal.typein, Cardinal.mk_ord_toType, and the source tags 058X and 05N1 were read. Existing lem-weil-pbc-well-ordering-theorem and lem-weil-pbc-transfinite-recursion are Mathlib leaves and are cited unchanged. I opened their statements and their recorded Mathlib source ranges: Cardinal/Order.lean:535–570 and Order/RelClasses.lean:285–315. Both apply to set-indexed constructions here, so no off-route unsplit statement is used. They are tools automatically by their Mathlib status.

Before creating the new leaf I searched the whole blueprint with tools/blueprint_refs.py for transfinite, well-order, well-ordering, well ordered, ordinal, enumeration, enumerat, order type, 058X and 05N1. Only the directed-finite-upper-bound definition and a classical-framework remark were incidental hits; neither is an ordinal-enumeration theorem. ancestor printed lem-trf-local-term-locality. The existing coordinate-projective-exhaustion node assumes an ordinal enumeration and constructs a different tensor/projectivity filtration; it does not provide the general enumeration tool. The sharp-filtered-poset-subsets node concerns cardinal-directedness, not ordinal representations. Whole-DAG searches for the new id found no existing node.

All new searches ran using the required msearch.py command and their log records are preserved. Two semantic phrasings were used for the enumeration question: the initial bijection question and the more precise given-well-order question. Loogle Ordinal.enum and LeanSearch's precise order-isomorphism question both return Ordinal.enum. Its source at Basic.lean:472 is a relation isomorphism with precisely domain Iio (type r), and the inverse equations at 476 and 485 confirm bijection; enum_lt_enum at 489 confirms order preservation/reflection. A corrected directory grep supplies the full filename and line. The earlier single-file grep's formatter omitted the filename; its record is retained in searches.jsonl but not used as the leaf's file evidence.

The item was searched again by its own mathematical content with LeanFinder, LeanSearch, Loogle and whole-Mathlib grep. I retained the inherited actual queries without claiming to have rerun them. The new semantic hits are IsModuleFiltration, ideal filtrations, or measurable-space constructions. I read FilteredAlgebra/Basic.lean:85–110, MeasurableSpace/Card.lean:40–65, PartitionFiltration.lean:100–123 and Process/Filtration.lean:224–240. None constructs an exhaustive invariant coordinate filtration for arbitrary f and specified D_j. No service was unavailable.

## Not duplicates

lem-trf-well-order-ordinal-enumeration vs lem-weil-pbc-well-ordering-theorem: the existing node produces a well-order on an arbitrary set; the new exact Mathlib leaf takes an already given well-order and supplies its order-preserving bijection from an ordinal initial segment. The existing statement has no ordinal or enumeration.

lem-trf-well-order-ordinal-enumeration vs lem-weil-pbc-transfinite-recursion: recursion defines values from earlier values on a given well-ordered index; it neither gives an ordinal representation nor an enumeration. The new leaf supplies only that representation.

lem-trf-well-order-ordinal-enumeration vs lem-trf-coordinate-projective-exhaustion: the latter assumes the well-order and its ordinal enumeration and constructs module/tensor-image filtrations with projective quotients; the new leaf has no ring, modules, filtration or enlargement property.

No existing node carries Tag 05N1. All existing Tag 058X statements were read: countable-coordinate-closure and its two helpers build one countable stable block; split-transfinite-module-filtration and its two successor-map helpers split an already given module filtration; idempotent-coordinate-filtration-quotients studies images and quotients for an already supplied filtration; projective-kaplansky-direct-summand and projective-countable-decomposition prove decomposition results. None states the given-well-order enumeration leaf. The coordinate-submodule definition is reused unchanged. No new coordinate continuity or successor-invariance node was created, since each has an explicit few-line argument from the definitions.

lem-trf-well-order-ordinal-enumeration vs lem-trf-invariant-coordinate-transfinite-filtration: the new node is the general exact Mathlib order-type representation of a given well-order, for any set without a ring, endomorphism, blocks or filtration. The item constructs and proves the invariant filtration; its six steps carry that argument. The new node is a general-purpose Mathlib leaf, not an unsplit restatement of a filtration clause.

lem-trf-well-order-ordinal-enumeration vs def-trf-coordinate-submodule: the existing definition specifies supported finite families in a module direct sum; the new node states an ordinal order isomorphism of a given well-ordered set and does not define or mention any module.

lem-trf-well-order-ordinal-enumeration vs lem-trf-countable-coordinate-closure: the existing node constructs one countable invariant coordinate block for a module endomorphism from countable generation; the new Mathlib leaf has no countability, modules or invariance hypothesis or conclusion.

lem-trf-well-order-ordinal-enumeration vs lem-trf-countable-successor-coordinate-exhaustion: the existing node proves countability and finite-support continuity of an N-indexed support-closure sequence; the new node identifies any well-ordered set with its ordinal order type and has no support-closure construction.

lem-trf-well-order-ordinal-enumeration vs lem-trf-countably-generated-image-support: the existing node bounds the union of supports of the image of a countably generated module; the new leaf has no linear map or support and concerns an arbitrary given well-order.

lem-trf-well-order-ordinal-enumeration vs lem-trf-idempotent-coordinate-filtration-quotients: the existing node assumes an ordinal filtration and computes idempotent images, retractions and successor quotients; the new leaf only supplies a bijective order enumeration and makes no module-filtration assertion.

lem-trf-well-order-ordinal-enumeration vs lem-trf-projective-kaplansky-direct-summand: the existing node decomposes a direct summand of a sum of countably generated modules; the new leaf is an order-type theorem with no decomposition or module data.

lem-trf-well-order-ordinal-enumeration vs lem-trf-countable-unions: the newly landed existing Mathlib leaf states countability of unions of countable sets, sequences and pairs; the new leaf represents a given arbitrary well-ordered set by its ordinal order type, with no countability restriction or union conclusion.

## Review by NK

I read Stacks algebra.tex, Tag 058X, theorem-kaplansky-direct-sum, from the theorem through the recursion and exhaustion paragraphs (20471–20570). The relevant portion chooses a well-order, takes a union at a limit and adjoins the least omitted coordinate block; its final transfinite-induction paragraph proves exhaustion. In this item's version, D_j and its invariance/countability are hypotheses, replacing the source's countable-matrix construction. This is why the generalization to arbitrary N_j is valid. I also read sets.tex, Tag 05N1, section-ordinals, especially lines 113–115, and checked the tag-label mapping in tags/tags. The new leaf states exactly that order-type fact, with no extra nonemptiness assumption. Its statement is self-contained, its well-order and ordinal order are explained inline, and it has no postponed proof or hidden proof sketch.

Step 1 uses exactly the existing well-ordering statement and the new ordinal-enumeration statement: the former orders J, and the latter gives κ and η in that order. The enumeration leaf by itself does not assert every set has a well-order, so both citations are needed. The empty set gives κ=0.

Step 2 uses the existing transfinite-recursion node's assertion for arbitrary well-ordered set E and a rule on earlier values. Here E is the set {α:α≤κ}, V is the set P(J), and the zero, successor and nonzero-limit cases are mutually exclusive. At a nonstationary successor, η's surjectivity makes the set of omitted indices nonempty, and ordinal well-ordering provides its least member. The rule uses only earlier values, so the recursion hypothesis holds. The explicit monotonicity induction then needs no further lemma: successors contain their predecessor and limits contain every earlier stage. No proper-class recursion is used.

Step 3 cites the coordinate-submodule definition for membership by vanishing coordinates and the direct-sum definition for finite support and componentwise operations. I copied their actual statements into citations.json and read CoordinateSubmodule.lean's carrier. Restricting the support to B and its complement in B∪C proves M_{B∪C}=M_B+M_C directly, including overlaps. Linearity and the assumed invariance of each selected block then give successor invariance. This is elementary linear algebra; no exactness, flatness, countable generation or decomposition theorem is hidden here.

Step 4 uses precisely those same two definition statements. For a vector with finite support in the limit union, each support coordinate occurs earlier, and the maximum of finitely many witness indices is still below λ. The empty support takes stage zero because λ is nonzero. This gives equality of submodule sets at the limit, then invariance by choosing the single stage containing the input vector. The two-case finite-maximum argument is written, not taken from the proof of another node. It does not claim that arbitrary supports fit in one stage. The successor and limit arguments together constitute an explicit transfinite induction, with base zero given in step 3.

Step 5 is the routine induction for η({β<α})⊆A_α, with no extra theorem cited. At a successor, if η(α) is missing then every smaller index is already present, so α itself is the least omitted index and D_{η(α)} contains it. At a nonzero limit, β+1<λ gives an earlier stage containing η(β). The terminal equality follows from η's surjectivity. This argument uses membership of j in D_j, not nonvanishing of N_j. It also covers stages that reach J early and are stationary thereafter.

Step 6 restricts the injection witnessing countability of the chosen D_j to the successor difference, with the empty difference in the stationary case. It uses only the coordinate-submodule definition for M_empty=0 and M_J=M. There is no hidden countable-union claim. The recursion itself gives the exact successor formula requested in the statement.

I checked B1–B10: the only new node is a self-contained statement-only exact Mathlib leaf; it uses no nonstandard notions needing separate definition nodes; TeX has one backslash after JSON decoding; its source is the verified Stacks tag/label and its Mathlib declaration has the source file and line. Blueprint fields and same_as searches are filled. I checked C1–C8 by opening every cited statement; citations.json contains verbatim quotations for all uses. The two old Mathlib leaves are allowed generic tools, and no new tool_uses field is set. I checked D1–D5: the proof itself constructs the sets and verifies every clause; no node restates a filtration clause, no proof is moved wholesale to a helper, and no dependency returns to the item. All six proof steps are below 2000 characters.

For E1–E7 I tested J empty, one index, finite J with overlapping blocks, arbitrary zero summands, all zero summands, f=0, f=id, early exhaustion D_j=J when J is countable, and J=ω with singleton blocks. The latter gives A_n={0,…,n−1}, A_ω=ω and illustrates why finite support is exactly what limit continuity needs. Non-idempotent f is allowed: only linearity is used. None of these tests needs countably generated N_j or countable R. No source error or statement correction was found. The only correction during drafting was to keep the ordinal representation as its own general Mathlib leaf rather than pretend the existing well-ordering node already states it.

Dry-run repair: the duplicate gate also reads 058X in the new leaf’s source-use note. I had already opened every listed same-tag statement; I added the required individually named comparisons above (including the item), rather than removing the truthful source-use reference. No mathematical field changed.

Second dry-run repair: preflight requires a node citation even when every notion in a new leaf is defined inline. The leaf now cites lem-weil-pbc-well-ordering-theorem for its well-order notion (whose total-order/least-element description I read), and lists it in stmt_deps. Its fixed-given-order conclusion is unchanged and remains exactly Ordinal.enum. The step-1 quotation was refreshed verbatim.

Live-base update after the passing dry run: the push gate found the newly landed lem-trf-countable-unions, also tagged 058X. I opened its whole node and compared its three union-countability conclusions with the order-type leaf; they are unrelated statements. Added the required named comparison and reran the dry run on the updated base before pushing again.
