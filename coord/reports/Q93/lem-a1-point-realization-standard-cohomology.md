# Stage-1 report: lem-a1-point-realization-standard-cohomology

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-point-realization-standard-cohomology.json`: split the item into eight proof steps, retaining its statement, provenance, earlier searches and blueprint references. The item is not a Mathlib leaf.
- `citations.json`: 27 step/node citations with verbatim statement excerpts.
- No new nodes; no Mathlib leaves. `searches.jsonl` records the five searches run for this item. `write_split.py` and `bhatt-scholze.txt` are sandbox working material only.

## Attachments

None. Searched `lean/WeilConjectures` for the exact blueprint id and point-realization concepts, and read PointFiberRational.lean and the point-fibre references in PointFiberAlgClosed.lean. The point equivalences there do not state the complete standard-cohomology and normalized scalar-coherence assertion of this item. No attachment is claimed from those declarations.

## Literature

No WANTED documents. Read Bhatt–Scholze Example 4.1.10 (printed p.28), Definition 6.8.10 and Proposition 6.8.11(3) (pp.60–61), Proposition 6.8.14 and Remark 6.8.15 (pp.61–62), from the local PDF. Example 4.1.10 explicitly distinguishes evaluation on a profinite object from a topos-theoretic point; the proof uses precisely sections at the final singleton, as specified in the item. Read Stacks proetale.tex, Tags 0982 and 098H, labels lemma-w-local-strictly-henselian-extremally-disconnected and lemma-w-contractible-is-weakly-contractible; and homology.tex, Tag 010N, lemma-exact-functor. The argument assembling the requested natural square is an agent argument, and proof_origin says so: it is not attributed to a nonexistent assertion in Bhatt–Scholze.

Read the current main-20261015 blueprint's lem-a1-finite-map-purity and prop-constructible-truncations, and the DAG chapter and unit records. This supports the point-fibre/cohomology interface in finite-map purity below sk-thm-dl-a1-upper, without changing the unit's weight-estimate route. The item is not the unit key node, so no unit file is changed.

## Corrections and limitations

There is no statement dispute and no statement change. The imported item supplied no proof. A potential category-convention error was avoided explicitly: prop-weil-pbc-integral-tstructure and prop-weil-localized-tstructure use the category with compatible etale-origin witnesses, whereas this item is written with def-weil-derived-complete-integral-detailed. The last two sentences of lem-weil-pbc-integral-stratified-perfect-characterization identify these full subcategories over the present Noetherian finite-dimensional base, with the same coefficient sheaf and reductions. Step 1 cites that identification before using either proposition. No assertion equating standard truncation with levelwise truncation of reductions is used; such an assertion would require the separate Tor-compatibility hypothesis.

The general descent lemma lem-a1-texact-coefficient-stage-descent was inspected but is not needed: the proof directly checks this particular realization's exactness, two halves, scalar square, and common-stage arrows. Nothing is left unfinished in the natural-language split; cited unsplit infrastructure remains work of its own nodes.

## Searches and reuse

Searched the entire DAG by point-sections, rational truncation, exact-functor cohomology and scalar-comparison concepts, and read the statements of all cited nodes. The blueprint search `point realization` returned no blueprint match; searches `truncation` and `sections` exposed the existing infrastructure. The ancestor command gives lem-a1-finite-map-purity, matching the item's retained from.node/via. No new node is needed.

Ran the required msearch command with LeanFinder, Loogle, grep and LeanSearch, plus a second LeanFinder phrasing. Read all results. The first semantic query found cotangent/localization theory; LeanSearch found unrelated complexes and scalar identities; Loogle found general TStructure truncation declarations; the second semantic query found general homological-functor statements; grep found no matching point-fibre cohomology declaration. These do not state this project-specific realization with its integral/rational comparison and specified scalar square. Search records preserve the exact tool and query text and report actual hit names. Earlier creator searches remain intact.

## Not duplicates

No new nodes. Reused exact sections, exact scalar tensor, homology preservation, integral-category characterization, integral/localized t-structures, canonical truncation comparison, scalar-section comparisons and both shift lemmas already in the DAG.

## Review by Q93

I checked the split against delivery-errors B–E with the cited statements and source passages open. There are no new statement-only nodes, novel notation definitions or new Mathlib-leaf claims to audit. Each step is below 2000 characters. The only step marked elementary is Step 3, which applies the stated description of the halves to the cohomology formula already proved in Step 2. Every substantive input in the other steps is cited, and citations.json copies statement text without paraphrasing. I checked that the chosen dependencies have no return path to this item; in particular I do not cite its parent pullback lemma.

Step 1 uses the integral stratified-perfect characterization for the explicit identification of the two completed-category conventions, integral-tstructure for ambient truncation maps, localized-tstructure for t-exact Q and localized truncations, and standard-tstructure for the definition of the halves. The base is Spec k: its dimension is zero and its sole local ring a field, and ell is invertible because ell differs from p. These are all the scheme hypotheses. I specifically checked that the auxiliary levelwise Tor hypothesis is absent from the general assertions actually used.

Step 2 uses point-proetale-sections-exact for both derived exactness and H^j Gamma = Gamma H^j; coefficient-complex-rationalization for exactness of ordinary tensor, including the case L=E; and exact-functor-preserves-homology for the kernel/image/quotient comparison and naturality. Rationalization-karoubi states that distinguished triangles are images of integral ones up to isomorphism, and finite-coefficient-point supplies exactly this functor and its target. The cone calculation is written explicitly; no unexplained derived-tensor exactness is assumed. Step 3 then verifies the two halves using the definition's isomorphism closures, for arbitrary shifted cuts.

Step 4 applies the full statement of pod-texact-truncation-comparison after exactness and all-cut preservation are established. Constructible-truncations supplies boundedness on the rational categories; Spec k is finite type over k. The uniqueness and composition clauses identify the integral cycle quotient formula with the canonical rational cohomology map. Thus the integral comparison is an assertion about the specified maps, rather than just an abstract isomorphism between objects. The degree-zero heart consequence follows from both halves.

Step 5 uses point-sections-scalar-extension for the exact normalization inverse(Gamma chi composed with theta), rationalization beta for its fraction-compatible target identification, completed-scalar-shift for chi and sections-tensor-shift for theta. I checked each cited statement actually states the displayed map and its shift compatibility. The beta formula is degreewise and commutes with shifts. This checks the essential shift hypothesis before invoking naturality for cohomology.

Step 6 uses constructible-truncations for source scalar compatibility with truncations and canonical maps, and exact tensor plus exact-functor-preserves-homology for the target scalar/cohomology identification. Both composites are therefore exact and t-exact. The natural-transformation clause of pod-texact-truncation-comparison is applied with eta equal to this particular phi, first to upper and then to lower truncation; Step 5 permits the shift. The resulting equation is written in the same direction as the item's square. This addresses the C4 and E5 risks of claiming unspecified transport or unspecified coherence.

Step 7 uses the unit and tower equations in the statement of point-sections-scalar-extension, and their rational beta compatibility, not something only found in their proofs. Pasting the two squares gives the direct square after applying H^j to the tower equation; composition of truncation comparisons accounts for the associators. Equality of fields is allowed throughout. Step 8 uses both common-stage definitions, the definition of Fib on arrows and constructible-truncations to represent triangles, halves, canonical maps and arrows over a finite stage. The scalar square proves representative independence; inverses satisfy the same equation. Exactness of the common-stage functor is checked on an actual triangle, including its shifted last arrow.

For small cases I checked C=0, a degree-zero integral complex, a shifted heart complex, negative cohomology indices and repeated coefficient fields. A uniformizer-torsion integral heart object becomes zero after tensoring with E on both sides, so the proof does not assume torsion-free integral cohomology. L=E gives the identity square, and E=L=M reduces the pasted square to it. For a genuine tower, the rational beta multiplies all scalar factors in M and therefore respects the associators. No finite-stage field is replaced by Omega as an ordinary infinite-extension tensor category: the last step uses the stated pair categories.

The off-unit statements are declared as generic tool uses in split_report. They provide coefficient and t-structure infrastructure for this point realization, not alternate proofs of an affine-line weight-estimate unit step. No Lean file, compiler, Lake invocation, repository write or manual git operation was used.

## Validation

The required `deliver.py Q93 lem-a1-point-realization-standard-cohomology --no-push` completed with exit 0 and `OK (not pushed)` at 1182a0db711; server preflight passed, including the required DAG and split checks. The final packaging is checked again after recording this result; delivery then uses the same sandbox content.
