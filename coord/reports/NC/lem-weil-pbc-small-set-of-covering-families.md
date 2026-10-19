## Worker report

Files written:
- dag/nodes/sec-proper-base-change/lem-weil-pbc-small-set-of-covering-families.json: statement, split into six steps; not a Mathlib leaf.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-cofinality-small-family-bound.json: statement, Mathlib leaf Ordinal.iSup_lt_of_lt_cof, Mathlib/SetTheory/Cardinal/Cofinality/Ordinal.lean:296-299.
- citations.json: verbatim statements for every step citation.

Attachments: none. Searches by the item's blueprint tag, covering-family selection terminology, cofinality, and the prospective leaf declaration in WeilConjectures found no exact project declaration. The exact upstream master is reference material only. No Lean file was written and no compiler, Lake or build was run.

WANTED: none.

The item statement is unchanged. Its hypotheses agree with Sets Tag 000X (sets-lemma-coverings-site) and Section 000W (sets-section-coverings-site): small category, arbitrary class of set-coded indexed families, three covering axioms, and a prescribed set of actual families. Unlike Mathlib's Precoverage, this conclusion retains prescribed indexed families, not merely their presieves. I read Precoverage.lean:46-48 and the returned pretopology conversion signatures; these are not attachments or one-line matches for the item.

Nothing remains unfinished in this one-level split. The new leaf has no proof sketch or proof dependencies. Auxiliary write_split.py is a sandbox-only construction script and is not part of the delivery.

## Source error

I read sets.tex:913-1105 (000W, 000X) and sets.tex:180-243 (000E, 05N2, 05N3). The last paragraph of 000X says beta < beta_1 after using cof(beta_2)>kappa, which only gives a bound below beta_2. It also fails to include the outer family's stage in the common bound, and writes Cov_{kappa,f(alpha)} instead of the final Cov_{kappa,alpha}. Earlier it asks that Cov_0 be contained in V_{beta_0}, although beta_0 was chosen from support representatives; that line must use the subsequently enlarged beta_1. The successor recursion's base-change input uses alpha where its output stages use f(alpha); to guarantee closure one must apply the operation to the current stage. These are proof slips, not false conclusions. Steps 4-6 avoid them by defining actual increasing sets B_gamma, explicitly including every operation on the current stage, and bounding both the outer and the inner stages below theta.

There is also an empty-family caveat: the source's bare support equality needs equal targets. Two empty covers of different objects have identical empty support but different targets. The item already specifies equal targets, and step 1 indexes representatives by the pair (target, support), so this edge case needs no statement repair. No STATEMENT-DISPUTED correction to the item is necessary.

## Not duplicates

The new leaf's tags 000E and 05N2 have no existing node matches in dag/nodes or in the full blueprint search. Searches for cofinality, ordinal supremum, and Ordinal.iSup_lt_of_lt_cof likewise found no node stating this bound. The Grothendieck-category small-object lemma prop-pur-kinjective-objects-small concerns factorization of maps through colimits of monomorphisms, not a bound on an arbitrary ordinal family; it is not a specialization usable here.

No new cardinal-arithmetic or recursion node was created. lem-weil-pbc-finite-list-cardinality already supplies the bound on two-element lists, and lem-weil-pbc-transfinite-recursion already states existence of the recursive family with its defining equations. Neither depends on this item. The leaf's generic ordinal statement does not restate any covering-selection clause.

## Review by NC

I checked the item against the full proof of Tag 000X (sets-lemma-coverings-site), and the single new statement against the definition of cofinality in Tag 000E (sets-section-cofinality), the ordinal bound in the proof of Tag 05N2 (sets-lemma-map-from-set-lifts), and the exact current Mathlib declaration at Cofinality/Ordinal.lean:296-299. The local theorem assumes only |I|<cof(delta) and that each a_i<delta; it imposes no countability, nonemptiness or regularity hypothesis. The new node introduces the index set, ordinal, family, cofinality, and empty supremum inline. The grep search with a file as its last argument prints malformed path fields; the recorded final grep was rerun with SetTheory/Cardinal as a directory and gives the correct file and line. LeanSearch returned HTTP 500 and is recorded unavailable, never no match. Loogle and LeanFinder ran and their current/local or old alias signatures were read.

Step 1 uses only foundational set formation: Separation on a powerset of the arrow set, Collection of witnesses indexed by a set, then Choice on that collected set. Collection is a ZFC axiom, not a claim of global choice on a proper class. This replaces the source's least-rank argument without making the class of all families into a set. The target is explicitly part of the code. Equal target and support give mutual occurrence maps by Choice, and no assertion of closure under arbitrary reindexing is used.

For step 2 I opened lem-weil-pbc-finite-list-cardinality and read its statement: it bounds the cardinality of all finite lists in any set X by max(aleph_0,|X|). Taking X=K of infinite cardinality kappa gives exactly the list bound used. The explicit two-field encoding proves the disjoint-union bound, including when I or some J_i is empty. The initial prescribed families can have huge repetitions: their actual index sizes, rather than just their supports, are included in kappa.

Step 3 uses that same quoted statement through the two-field encoding of step 2. I read the argument in Tag 05N3: the least ordinal of cardinality exceeding kappa cannot be a successor, and a hypothetical cofinal subset of size at most kappa expresses it as a union of at most kappa sets of size at most kappa. The displayed injection gives the contradiction, so no separate invocation of an uncited existence theorem or a new clause-node is hidden here.

For step 4 I opened lem-weil-pbc-transfinite-recursion: it allows a set of well-ordered stages and a class of values, and supplies values satisfying the prescribed rule at each stage. The stages gamma<=theta form a set, and the values here are sets of families. Successor additions are set-indexed by all maps from the actual outer index set to the current set of families and by all arrow/pullback choices in the small category. The original axioms put every output back in Cov; the finite-list citation gives the bound on composite index sets. The proof never assumes the category has unrelated pullbacks. Nonunique available pullback choices are all included if the original axiom quantifies over them.

Step 5 is membership in the union and in the next stage. It checks existence of required fibre products from the original class axiom. The singleton covers use the standard singleton index convention of 00VH and 000X; closure under reindexing along arbitrary singleton sets would be a different, impossible set-sized requirement and is not one of the three axioms asked for here.

For step 6 the new leaf says precisely that sup_i gamma_i<theta from |I|<cof(theta); this follows from |I|<=kappa and step 3. The outer stage is included by taking a maximum with gamma_0. Since theta is a limit, gamma+1<theta. Thus the current-stage composition is actually in the final union. This explicitly repairs the source's beta_1/beta_2 slip and missing outer bound. Representatives remain present from B_0 onward.

I tested the new leaf with I empty (its hypothesis forces delta>0 and sup=0), with delta=0 (no index set satisfies the hypothesis), and with delta a successor (cofinality 1 forces I empty). For the item I checked the empty category, empty prescribed set, empty covering families on distinct targets, and arbitrary repeated arrows with large index sets. The construction includes their original codes and uses their actual index cardinalities. These cases require neither a new hypothesis nor a weakened conclusion.

The chapter/unit records were read. This item is an auxiliary covering-selection tool below the completed-pullback definition, not the unit's key theorem; no unit realized fields change. The existing off-unit recursion citation is a Mathlib leaf, so it is already an admissible tool; no unit route is replaced. The blueprint searches across all chapters found no equivalent blueprint statement for the new ordinal bound. The item's from.place already precisely names the small-covering selection needed for Sites 03A1(1), and remains intact with same_as=[]; the new leaf's ancestry includes this item followed by its existing via chain.

The checks B1-B10 found a self-contained statement-only new node, correct tag/label and file/line, no duplicate or project attachment, and actual logged searches. Checks C1-C8 found only the three cited statements used as stated, quoted verbatim in citations.json, no dependency back to the item, and no unjustified route replacement. Checks D1-D5 found the selection and closure argument stays in the item's steps rather than moving its clauses into new nodes. Checks E1-E7 exposed and repaired the source's stage slips and empty-support issue as described above. All writes are confined to the sandbox. The dry run is the only authorized packaging operation and no push is requested.

The first dry run rejected the new leaf because its fully inline statement had no node citation. I repaired this by citing the existing lem-weil-pbc-transfinite-recursion for the definition of a well-ordered set, which its statement explicitly gives as a total order whose every nonempty subset has a least element. The ordinal is viewed as this well-ordered set; the cofinality definition remains inline. This is a statement dependency only, not use of the recursion theorem to prove the ordinal bound, and does not alter the exact Mathlib match. citations.json now quotes the updated leaf statement. No artificial set-theory definition node was introduced.

## Second reading by NC

- Item statement: checked hypothesis by hypothesis against Sets Tag 000X (`lemma-coverings-site`) and Section 000W; category and arrow sets, proper-class coverings, all three axioms, prescribed set, and target-plus-support equivalence agree. Verdict: sound and unchanged.
- Step 1: checked against Tag 000X first paragraph and the set/choice construction; the target is retained for empty supports and the argument does not assume reindexing closure. Verdict: elementary and adequate.
- Step 2: checked against Tag 000X cardinal bound and `lem-weil-pbc-finite-list-cardinality`; actual index cardinalities and empty coproduct cases are included. Verdict: cited dependency says the required list and disjoint-union bound.
- Step 3: checked against Tag 05N3 and the finite-list bound; the least ordinal argument gives a limit ordinal and cofinality strictly above the chosen cardinal. Verdict: elementary and adequate.
- Step 4: checked against `lem-weil-pbc-transfinite-recursion` and Tags 000X (successor closure) and 00VH (pullbacks); all operations are set-indexed and remain in the class by the stated axioms. Verdict: cited statements support the construction.
- Step 5: checked against Tag 000X verification of identity and pullback axioms; the successor stage and limit union give the required final-stage membership. Verdict: elementary and adequate.
- Step 6: checked against Tag 000X final composition paragraph and the new cofinality leaf; both outer and inner stages are bounded below the limit, including an empty outer index set. Verdict: cited leaf gives the required bound and repairs the source's stage-index slip.
- New node `lem-weil-pbc-cofinality-small-family-bound`: checked against Sets Tags 000E and 05N2 and Mathlib `Ordinal.iSup_lt_of_lt_cof` (Cofinality/Ordinal.lean:296-299). Verdict: statement-only, self-contained, exact one-line Mathlib match, with the well-order notion cited to the existing recursion node; empty, zero, and successor ordinal cases checked.

Changes made in this second reading: none to the mathematical statements or proof steps. I verified the source's two stage-bound slips are already repaired in steps 4 and 6, confirmed the empty-support target issue is handled in step 1, and confirmed `citations.json` quotes each cited statement verbatim. The only packaging issue encountered was that `deliver.py` accepts no trailing `.` argument; the mandated dry-run was therefore rerun with its documented argument form.
