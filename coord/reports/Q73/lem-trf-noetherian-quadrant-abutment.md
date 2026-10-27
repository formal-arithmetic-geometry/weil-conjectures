## Worker report

Files written: `dag/nodes/sec-trace-formula/lem-trf-noetherian-quadrant-abutment.json` (item, split; not a Mathlib leaf), `citations.json`, and this report. There are no new nodes and no new Mathlib leaves. The scratch script `write_split.py` is not a delivery file.

Attachments: none. Searched the read-only `lean/WeilConjectures/` for the item tag and quadrant/finite-abutment notions. The spectral-sequence vanishing and low-degree files do not give the item's finite-generation assertions. The short-complex module-finiteness theorem proves only a module extension fact, not this item.

WANTED: none.

The statement was not changed and is not disputed. The original node had an empty proof; its existing searches, citations, creation record and blueprint provenance have been preserved. The parent `lem-trf-bounded-above-coherent-rhom` identifies exactly the two Ext spectral sequences in Stacks 0D0C. This split supplies their final algebraic finite-generation inference, without introducing another convergence hypothesis or trying to construct convergence. An abutment and its finite filtration are hypotheses of this item.

Mathlib searches: ran the required leanfinder, loogle, grep and leansearch commands under Q73 and read their results. A second semantic phrasing returned short-complex finiteness, categorical exactness and filtration facts, not this full statement. The first phrasing returned derived-category bounds. Loogle found no result. The spectral-sequence grep hits at Basic.lean:127,132 describe finitely many rows rather than finite module terms. LeanSearch returned the Noetherian finite-module instance and finite presentation. None states the quadrant support, specified stabilization bound and finite filtered abutment together. Every new recorded search is copied from the actual `searches.jsonl` record; the inherited NX searches remain intact.

DAG/blueprint reuse: searched the whole DAG by spectral-sequence/finite-generation/subquotient/submodule notions and searched the whole blueprint with `blueprint_refs.py search` for spectral sequence, quadrant, subquotient, finitely generated and Noetherian. Existing `lem-trf-noetherian-submodule-finitely-presented` is a Mathlib leaf with the precise submodule-finiteness clause needed for kernels. `lem-pc-noetherian-finite-kernels-cokernels` also exists, but is unnecessary once the quotient generator argument is written explicitly. No new module-extension or finite-filtration node was created: the proof writes the two-line lifting-of-generators argument. The nearest blueprint ancestor is `lem-trf-local-term-locality`; the existing, detailed `from.place` records the supporting algebra branch. The split_report identifies the five steps realizing this branch.

Unfinished work: none in this one-level split. The statement of the reused Mathlib leaf is not re-proved here.

## Review by Q73

I read the statement and proof of perfect.tex, `lemma-coherent-internal-hom` (Stacks Tag 0D0C), particularly both displayed Ext spectral sequences and the final finite-generation inference. The item isolates the elementary spectral-sequence bookkeeping implicit there. I also read homology.tex `definition-spectral-sequence` and the bigraded variant `remark-allow-translation-functors`: the incoming differential has source (p-s,q+s-1), and the next page is exactly kernel modulo incoming image, with the specified page isomorphism. I read algebra.tex `lemma-Noetherian-finite-type-is-finite-presentation`, Tag 00FP(2), which states that every submodule of a finite module over a Noetherian ring is finite. This agrees with the exact clause quoted from the existing DAG leaf. No SGA source is used.

Step 1 cites `def-sp-spectral-sequence`, whose statement explicitly supplies the homology-to-next-page isomorphisms, not merely a definition of page differentials. Starting from page 2, a zero middle module has zero homology, so the support induction has its base and step. This is elementary from the definition.

Step 2 cites that same page-isomorphism statement, `lem-trf-noetherian-submodule-finitely-presented`, and `def-weil-finitely-generated-module`. I opened all three statements. The submodule leaf applies because the ring is Noetherian and the current page term is finite by the induction hypothesis; its statement actually says G is finitely generated (the additional finite-presentation conclusion is unused). Quotient finiteness is proved by images of a generating set, rather than inferred from a definition node cited as if it were a theorem. Isomorphisms carry the explicit generating set to the next page. This step is marked non-elementary because it uses the Noetherian submodule theorem.

Step 3 cites only the spectral-sequence definition: its other inputs are Steps 1 and 2, not hidden external stabilization results. I checked both inequalities separately: s>p-a makes the incoming source vanish, and s>q-b+1 makes the outgoing target vanish. The integer s0=max(2,p-a+1,q-b+2) works also outside the quadrant. Every subsequent transition is an isomorphism from the zero-differential homology calculation. Choosing the term at s0 and composing these isomorphisms supplies the eventual stable term without asserting that page objects are literally equal.

Step 4 cites the actual definition of finite filtration in `def-sp-filtration`, which gives endpoints equal to the whole module and zero, and the generating-set definition. It uses only the assumed A-linear graded-piece isomorphisms and Step 3, not an unproved convergence theorem. I wrote the downward induction and the subtraction argument for lifting generators. This proves the extension inference directly; no Noetherian condition on the abutment is assumed. The empty set generates the zero base term.

Step 5 cites the same finite-filtration endpoints. When n<a+b, each pair (p,n-p) is outside the supported quadrant; all graded pieces vanish. The equality of consecutive filtration submodules follows directly from a zero quotient, and finite descent forces the entire module to be zero. This is an elementary quotient calculation, not an invocation of a separate spectral-sequence vanishing theorem.

B1–B10: no new nodes, so there are no statement-only, self-containment, definition-dependency, duplicate, or Mathlib-leaf-format issues to introduce. The item's objects and hypotheses were retained. TeX uses single mathematical backslashes after JSON decoding. Its actual definition dependencies were opened. Mathlib searches are logged exactly, and the item is not relabelled as a Mathlib leaf.

C1–C8: every external non-elementary input is the cited submodule theorem. Every cited statement was opened as described above; citations.json contains verbatim statement quotes for every step/node pair. Internal references to earlier numbered steps are the arguments of this proof, not new DAG dependencies. There is no citation of the parent or any downstream spectral-sequence consumer, hence no intentional cycle. The reused submodule leaf is in this item's chapter and unit; the definition nodes supply notions, not a replacement route.

D1–D5: the proof carries the support induction, module induction, stabilization inequality and lifted generators itself; nothing was moved into a node restating a clause. Each step is below 700 characters, so none exceeds the 2000-character threshold or hides an extended comparison lemma.

E1–E7 and small cases: checked the zero ring, zero pages, negative a and b, positions outside the quadrant, the corner (a,b), and n=a+b-1. At the corner every s>=2 satisfies the strict bound. Equality at the stabilization threshold is intentionally not claimed. In degree n=a+b only the corner may survive, consistent with the claim of vanishing strictly below a+b. A filtration with identical endpoints can only occur for the zero module, which the generator argument covers. No finite dimension, finite coefficient ring, global bound on the number of pages, or uniformly bounded filtration in n was used. I found no mathematical statement correction necessary; the correction made was to replace the empty proof with explicit arguments and the precise reused input.

## Not duplicates

No new nodes were created. The existing Noetherian submodule node is cited directly.

## Validation

The first required deliver.py --no-push completed with exit 0 and printed OK at 70a0df66cc1. After that pass, added the final logged grep query `ab_finite` to the item record, having read Mathlib/Algebra/Homology/ShortComplex/Ab.lean:150–173; it is about finite underlying sets, not this claim. No mathematical statement or proof changed. The final dry run and delivery follow this search-record update.
