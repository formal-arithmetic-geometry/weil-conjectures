# Stage-1 delivery: lem-pod-stratified-dualizable-bounded

## Files written

- dag/nodes/sec-poincare-duality/lem-pod-stratified-dualizable-bounded.json: statement, split into seven steps; Mathlib has generic support/truncation results but not the stratified-dualizability theorem. Statement and stmt_deps unchanged.
- citations.json: 19 verbatim statement excerpts, one per step/cited node pair.
- searches.jsonl: the five actual current searches, including a second natural-language phrasing. Earlier Q82 searches already in the item are retained unchanged.
- report.md: this report. No new nodes and no Mathlib leaves were created.

## Attachments

None. Searched the entire live lean/WeilConjectures tree for the exact blueprint tag, stratified dualizability, and both orders of dualizable/bounded. The hits concern bounded-complex-implies-dualizable, finite coefficients, or statements already assuming boundedness; none proves all of this item. No compiler was run.

## WANTED

None. The needed Hemo–Richarz–Scholbach paper and Stacks sources are present.

## Problems and corrections

The unsplit item had no proof. Its statement agrees with HRS Corollary 4.11 and its hypotheses: qcqs, arbitrary commutative condensed coefficients, finite constructible locally closed stratification, dualizable derived restrictions. No statement dispute or statement change was needed. HRS uses “constructible” for this derived stratified-dualizability notion; the project's sk-def-sfb-constructible instead defines a condition on individual module sheaves. I did not cite that definition or identify these notions.

The source's local boundedness argument must not be read as saying that scalar realization is t-exact on arbitrary complexes: HRS Example 4.2 explicitly warns against this. Steps 3–4 instead use finite projective retracts, exactness as a triangulated functor, brutal-tail triangles and their long exact cohomology sequences. No regularity, Noetherianity, component finiteness, or coefficient-flatness assumption is introduced. The source's finite-stratum induction is made precise using an existing scheme-theoretic binary refinement, so there is no inference that set-theoretic containment alone factors a scheme map.

## Unfinished work

None for this one-level split. Its cited nodes remain independent DAG obligations according to their existing status. No unit realization edit is required: this item is a descendant of sk-def-perfect, not its key node. No Lean source was written or compiled.

## Not duplicates

No new node was created. Searches of the whole DAG and blueprint for dualizable, bounded, stratification, local evaluation and truncation found the tools used below. In particular, lem-zl-condensed-dualizable-local-perfect-models needs locally finitely many irreducible components for its local scalar description and was not used. Existing w-contractible evaluation, locality, cover conservativity, finite binary refinement, open/closed zero detection, complex triangles and good truncation avoid any new helper. The item itself has no blueprint same_as match: the perfect-complex blueprint definitions and finite-coefficient tensor-Hom statements are different claims.

## Review by NU

I read AGENTS.md, the worker brief and role, GOAL.md, the three blueprint levels in SETUP.md, stages/1-dag.md, delivery-errors B–E in both historical copies, the chapter and unit records, the current main-20261015 sk-def-perfect/_section.md, and this item's parent lem-pod-condensed-localization-hom. This is the parent's boundedness input for its scalar telescope, within the local-perfect-model equivalence of sk-def-perfect. I read HRS Definition 3.3, equations (3.1)–(3.4), Remark 3.2, Lemma 4.1 with its proof, Example 4.2, Definition 4.9, Lemma 4.10 with its proof, and Corollary 4.11 with its proof. The final bounded-below consequence uses the explicit good truncation construction, not a claim that global derived sections are bounded.

Step 1: I opened lem-fix-constructible-open-closed-refinement and lem-zl-condensed-lisse-proetale-locality. The first statement supplies actual maps from leaves to original strata, a finite binary tree, qcqs vertices and quasi-compact open children. The second explicitly preserves dualizable objects under every scheme morphism for every condensed ring. Thus pulling the dual pair to a leaf is legitimate even with arbitrary scheme structures on the original strata. I also read the Stacks topology proof at Tag 09Y4 (lemma-constructible-partition-refined-by-stratification); the cited existing refinement node supplies its scheme-theoretic strengthening, rather than taking this extra assertion directly from the topology tag.

Step 2: I read det-pe-hypercover-single-cover: its quantified object may be the final object T of T_proet because each leaf is quasi-compact. It gives a SINGLE covering by a w-contractible affine, so bounds need not be uniformized across an uncontrolled family. I reread the statement of lem-zl-condensed-wcontractible-lisse-evaluation: its ring is A=Gamma(W,B_W), its scalar realization is exact symmetric monoidal, and its equivalence supplies a bounded finite-projective representative. No assumption on the number of irreducible components occurs. Its HRS source is Lemma 4.1, which I read directly. Locality supplies dualizability of the restricted complex.

Step 3: I opened the finite-generation and projective-module nodes. Finite generation supplies a finite-free surjection; the projective lifting clause supplies a section. Applying the additive scalar realization to that retraction makes the image a retract of a finite sum of the coefficient unit. Cohomology, whose functoriality is stated in def-weil-abstract-derived-category, sends a retract diagram to a retract diagram. In any degree other than zero the identity factors through zero, proving the required concentration. This is elementary and written out, so no finite-projective-realization helper was created.

Step 4: I read lem-weil-pbc-complex-ses-triangle and lem-sf-derived-homology-long-exact, and their Stacks source arguments: Tag 0152, lemma-derived-canonical-delta-functor in derived.tex, and the homological-cohomology argument near Tag 05RS. The brutal-tail sequence has the correct orientation: the higher tail is the subcomplex, and the quotient is the single term in degree r. The cited scalar realization is exact in the triangulated sense, hence takes this triangle to a triangle and commutes with its shifts. Starting with the zero tail above b_T and descending to a_T, exactness of the displayed three-term portion makes the middle cohomology zero outside [r,b_T]. This proves the needed bound without asserting t-exactness of the realization. No step exceeds 2000 characters or hides an unlabelled comparison lemma.

Step 5: I opened sk-def-sfb-coefficient-morphisms, lem-trf-geometric-inverse-image-exact, lem-weil-pbc-exact-functor-complex-cohomology and lem-zl-condensed-cover-restriction-conservative. The first gives the coefficient isomorphism for an arbitrary condensed ring. The exactness node applies to transported inverse-image coefficients; it does not claim flatness of an unrelated ring map. I read Stacks Tag 04JC, lemma-flat-pullback-exact in sites-modules.tex, and Tag 010N, lemma-exact-functor in homology.tex. The cohomology node explicitly states the natural cohomology comparison. The covering-conservativity node is used on a module sheaf placed in degree zero, where its hypothesis is precisely zero restriction; it is not being asked to detect zero from global derived sections alone.

Step 6: I opened lem-exc-open-closed-detection and checked its complete statement: arbitrary commutative ring sheaf, closed immersion, complementary quasi-compact open, and zero module inverse images. The refinement supplies all geometric hypotheses; Step 5 supplies the cohomology comparisons for both children. A finite upward induction gives zero at the root degree by degree outside the minimum/maximum leaf interval. This is a finite induction, not Noetherian induction. The refinement lemma's proof is not mined for any construction absent from its statement.

Step 7: I read the whole statement of def-kun-truncations and checked the lower-truncation formula: coker d^(a-1) in degree a and zero below, with the induced differential. Its cohomology agrees with the original complex in degree a and above; below a both vanish. The map E to C is consequently a quasi-isomorphism by the definition in def-weil-abstract-derived-category. This elementary construction needs no new Mathlib leaf for the generic bounded-representative theorem returned by the searches.

Small cases checked: Y empty (zero module category and [0,0]); zero coefficient ring; zero complex; one stratum; one nonzero projective term in any positive or negative degree; a two-term finite-projective complex with a noninvertible differential; and arbitrary coefficient rings with nonflat section-ring realization (the retract/triangle proof remains valid, as opposed to t-exactness on all complexes). Finiteness is used exactly for the leaf min/max and finite-tail induction. In particular no cohomological dimension bound on Y is used.

For delivery-errors B, no new node or unverifiable Mathlib match is asserted; retained search records and the five new command records are distinguished above. For C, every cited statement was opened and supplies the fact taken from it, and citations.json has a verbatim excerpt for every pair. I checked the dependency closure of each cited input: none returns to the item. For D, all boundedness arguments remain in the item's steps; nothing is moved into a renamed clause. For E, the coefficient ring, inverse-image functors, tail shifts, finite-cover issue, actual leaf factorization and empty cases were checked as described. The seven generic off-unit tools are declared in split_report.tool_uses with their exact purpose; none invokes smooth purity, Poincare duality or the trace formula as a theorem. No SGA source is cited.

Dry-run repair: the citation gate required a longer locality excerpt. I replaced the short phrase in both occurrences with the full statement sentences specifying exact symmetric monoidal pullback for every scheme morphism and preservation of dualizable objects. The proof did not change.
