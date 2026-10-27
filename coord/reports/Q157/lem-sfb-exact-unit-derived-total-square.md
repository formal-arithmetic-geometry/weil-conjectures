# Stage-1 report: lem-sfb-exact-unit-derived-total-square

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-exact-unit-derived-total-square.json`: existing statement, split into seven steps; no exact Mathlib match found.
- `citations.json`: one verbatim statement quotation for each step/node citation.
- `report.md`: this report. Existing `searches.jsonl` is retained.

New nodes: 0. Mathlib leaves: 0. All writes are in this item's sandbox.

## Attachments

None. Searching `lean/WeilConjectures/` for the blueprint id and derived-total terminology found no declaration giving all the hypotheses and clauses. Exact derived descent and ordinary derived natural transformations alone do not state this item.

## WANTED

None. The source texts needed here are present locally.

## Findings and changes

The live item is an unsplit, agent-formulated lemma, not a theorem asserted verbatim by Stacks 015F. Its statement is unchanged. I retained the earlier sandbox proof, citations, recorded searches, and inherited metadata, comparing them with the current repository. There is no item-specific released repair note or return entry. No delivery process was active when resuming.

The proof explicitly constructs the strict map and its totalization by naturality on summand inclusions, descends the natural transformation using localization, and calculates the required derived square using existing canonical nonnegative totalization. It does not apply H to an injective resolution or assume that any of H, P, S preserves injectives. The last two steps treat actual augmentation maps and composition with a further exact functor. I clarified that the augmentation used in step 6 is a strict map const(A) -> K and that c is its induced total augmentation, matching the input lemma exactly.

The blueprint origin is inherited: main-20261015 `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), through the chain of created nodes recorded in `blueprint.from.via`. That paragraph supplies the direct-image route; it does not itself prove this formal compatibility. `blueprint_refs.py ancestor` returns null, and I preserved that inherited origin rather than inventing an ancestor. Whole-blueprint searches for derived total and natural transformation did not identify a duplicate of the full assertion. Chapter and unit routes are unchanged; this is not the unit's key theorem and no realization fields were edited.

## Mathlib search assessment

I read the existing searches.jsonl and the corresponding results already recorded in the item and did not rerun unchanged queries. The initial five records are inherited from the live node; subsequent searches are logged in this sandbox. The unavailable LeanSearch request remains unavailable, and the later successful LeanSearch request remains separate. The second phrasings address additive totalization and ordinary derived natural transformations.

The hits `CategoryTheory.Functor.mapDerivedCategory` and `mapDerivedCategoryFactors` (read in `Algebra/Homology/DerivedCategory/ExactFunctor.lean`, lines 36 and 41) provide exact derived descent. `AlgebraicTopology.map_alternatingFaceMapComplex` (read at line 183 in `AlgebraicTopology/AlternatingFaceMapComplex.lean`) concerns the alternating complex and additive postcomposition. `CategoryTheory.NatTrans.rightDerived` and `rightDerived_comp` (read at lines 219 and 233 in `CategoryTheory/Abelian/RightDerived.lean`) concern ordinary right derived functors and transformation composition. None supplies the resolved nonnegative cosimplicial derived-total comparison, its specified unit square, and augmentation compatibility under arbitrary exact postcomposition in one specialization. The existing DAG already contains the needed smaller exact-descent facts, so no duplicate leaves were created.

## Not duplicates

No new nodes. In particular, the replacement and canonical-total comparison are cited as the existing `lem-sfb-cosimplicial-injective-total-replacement` and `lem-sfb-nonnegative-derived-totalization`; the proof does not create aliases of them or move the item's clauses into new nodes.

## Review by Q157

I read delivery-errors B through E, the chapter and unit records, and the current blueprint paragraph (3). For the item's source I read Stacks `derived.tex`, Tag 015F, `lemma-right-derived-exact-functor`, including its explanation that exact functors preserve acyclic complexes and quasi-isomorphisms. I also read Tag 015J, `lemma-two-ss-complex-functor`, whose proof computes the derived object by the mapped injective finite total. This is background for the existing totalization input; I do not claim that 015F or 015J literally states the whole item. The proof is correctly marked agent-written. No SGA source is used.

Step 1 is naturality for each structural map; taking alternating sums is additive algebra. Step 2 uses the statements of `def-sp-left-exact-additive` (finite biproduct preservation) and `def-sp-double-complex-total` (finite diagonals and the signed differential). Agreement on every summand proves the chain identity, including its sign, without an uncited comparison theorem.

Step 3 uses `lem-weil-pbc-exact-functor-derived-factorization`, whose statement explicitly gives the descended exact functor represented termwise and preservation of quasi-isomorphisms. `lem-weil-pbc-localization-universal-property` explicitly includes lifting natural transformations and uniqueness, not merely existence of a lifted functor. I read both statements and Stacks `categories.tex`, Tag 04VG, `lemma-properties-left-localization`; the natural-transformation enhancement is the existing node's explicit assertion. Its hypotheses apply to Q and QH because H is exact. Naturality at the given derived isomorphism a then gives the displayed identity with correct source M and target QT(HK).

Step 4 uses the full statement of `lem-sfb-cosimplicial-injective-total-replacement`: the same I and eta give strict lifts of maps and also resolve augmentation objects. The other cited statement, `lem-sfb-nonnegative-derived-totalization`, explicitly gives chi, its naturality in strict maps, independence of choices, and the n,q,s >= 0 finite-diagonal convention. A and B are Grothendieck, G is additive left exact, and both K and HK are nonnegative strict diagrams (H is applied termwise), so these are precisely its hypotheses. I read those two statements, not their proof sketches, before using them.

Step 5 applies P_D to this naturality equality; exact factorization permits the termwise model P on resolutions even when P does not preserve injectives. The finite-biproduct identification is the summand argument of step 2 applied to P, so it commutes with model maps and choice identifications by the same explicit calculation. The calculation using h theta = f a verifies the entire square, rather than merely identifying its objects. Both a and h are isomorphisms, hence u and w are isomorphisms.

Step 6 uses the augmentation and compatible-map clauses actually written in `lem-sfb-nonnegative-derived-totalization`. I checked these clauses in full, and included the augmentation clause in its verbatim citation quote. The map is the degree-zero component of a strict const(A) augmentation; the biproduct identification preserves that inclusion. For arbitrary maps into M the stated compatibility is precomposition of the same equality. Naturality in M,a follows by substituting QT(k)a = a' b into the explicit formulas, so there is no unproved assertion about arbitrary incoherent diagrams in an ordinary derived category.

Step 7 uses exact factorization and the uniqueness clause of localization to identify the descents of SP and S followed by P. Both biproduct maps agree on each summand SP(iota), which proves composition compatibility including the augmentation inclusion. For the final site example I read `def-pur-localized-ringed-site` and `lem-pur-site-restriction-module-adjunction-exact`: the former specifies the pulled-back coefficient ring and actual restriction on sections, and the latter explicitly states restriction is exact. I read the localization section and extension-by-zero lemmas around Stacks 03DJ in `sites-modules.tex`, where restriction exactness is also used. The only off-route nonfinished tool is declared in split_report.tool_uses: the generic exactness of module restriction, not a substitute route for the unit.

I tested zero complexes, G = 0, H = identity with theta = identity, and theta = 0: the formulas reduce respectively to zero maps or the identity naturality square. For degree zero and one of the double total, the differential on a summand is delta + (-1)^n d on both sides, and additivity preserves its sign. For constant cosimplicial diagrams the augmentation condition is the alternating sum d0-d1 = 0 in the first horizontal degree, as required. Even for unbounded cosimplicial length, degree r contains finitely many nonnegative triples, so no product preservation or convergence assumption is smuggled into P or S. All seven proof steps are under 2000 characters; none hides a new standalone lemma. Definitions, objects, and coefficient categories remain those in the original statement.

B1-B10: no new nodes, no hollow definitions, no invented matches, retained exact queries and honest unavailable verdict. C1-C8: every non-elementary input is a cited statement, every quotation is a literal substring, and the one off-unit tool is declared. D1-D5: the proof performs summand and morphism calculations and cites existing smaller facts; it does not relabel the conclusion. E1-E7: hypotheses and types checked above, no statement dispute or source error found.

The first delivery dry run rejected two citation quotations as shorter than its 40-character minimum. I expanded them to the complete totalization formula and the restriction-exactness assertion, retaining verbatim text; this required no mathematical change.

## Unfinished work

None in the mathematical split. Required server dry run and direct delivery follow this report.
