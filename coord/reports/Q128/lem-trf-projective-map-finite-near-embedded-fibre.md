## Worker report

Item: lem-trf-projective-map-finite-near-embedded-fibre. Group Q128. Stage 1, 2026-10-23.

### Files written

- dag/nodes/sec-trace-formula/lem-trf-projective-map-finite-near-embedded-fibre.json: split into four steps using existing nodes; original statement and statement dependencies retained.
- citations.json: verbatim statement evidence for every node used by each numbered step.
- report.md: this report. searches.jsonl is the search command's own log.

New nodes: 0. New Mathlib leaves: 0. No Lean files written or compiler/build tools run.

### Attachments

None. Searching lean/WeilConjectures for the exact item id and for finite/projective/neighbourhood/fibre concepts found no declaration covering this item. The existing properness declaration for projective space is already attached to lemma-nagata-projective-space-base-change-proper, and is used through that node. The Mathlib declaration AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleton at AlgebraicGeometry/ZariskisMainTheorem.lean:406 is already attached to lem-trf-proper-finite-fibre-finite-near; it is not an attachment for this whole item.

### Literature wanted

None.

### Audit and changes

The item was unsplit with an empty proof. The sandbox contained no prior item or report. I copied the current item and preserved its statement, prior searches, provenance and blueprint ancestry. There is no released repair note for this item. I supplied the proof and current searches, set status split, and recorded the blueprint correspondence. No statement dispute was found.

I read GOAL.md, the three blueprint levels in SETUP.md, the chapter and sk-i-curve-zero unit records, and the latest blueprint ancestor lem-trf-local-term-locality.proof.md. The ancestor's contracting-correspondence route stays fixed. This item is an existing auxiliary ampleness/projectivity input below that ancestor. Its concrete source is the final paragraph of Stacks coherent.tex, Tag 0D2N, lemma-ample-in-neighbourhood. The first sentence there uses the locally Noetherian precursor in coherent.tex. For this item's explicitly arbitrary base, I read and used the more general Tag 02UP, more-morphisms.tex, lemma-proper-finite-fibre-finite-in-neighbourhood. This does not impose Noetherianity or finite presentation on S.

The proof does not apply the finite-fibre theorem to Z over S: that fibre can be positive dimensional. It applies it to the proper map Z to P at each point p of the entire projective fibre q^{-1}(s). The distinction is essential. Closedness of q then replaces the open target neighbourhood W by q^{-1}(V), which is the required base shrinking.

### Searches

Whole-DAG searches inspected statements and titles for finite neighbourhoods, proper finite fibres, finiteness local on the target, projective-space properness and affine neighbourhoods. They found lem-trf-proper-finite-fibre-finite-near, lem-weil-pbc-finite-local-on-target, lemma-nagata-projective-space-base-change-proper and lem-weil-pbc-affine-opens-basis. I opened these nodes' statements, together with the fibre, closed immersion and properness definitions. No new node is needed. Blueprint ancestor search gives lem-trf-local-term-locality. Whole-blueprint searches for finite neighbourhood, quasi-finite, embedded fibre and finite near found no blueprint node stating this whole item. The quasi-finite results include the global proper/quasi-finite criterion, not this shrinking assertion.

The five searches in this sandbox's searches.jsonl were run with msearch.py and their actual results read: two LeanFinder phrasings, Loogle, grep and LeanSearch. The item records the same tool/query strings, results and verdicts, retaining all original historical searches. Loogle returned the proper-and-affine and proper-and-locally-quasi-finite criteria. LeanSearch returned finite/proper restriction and finite-fibre facts. LeanFinder returned projective Proj properness and global finite/proper facts. The grep returned the exact pointwise-neighbourhood theorem at ZariskisMainTheorem.lean:406; I read lines 373–420, including its hypotheses and conclusion. None proves the whole item in one specialization: the union, target-locality and closed-image shrinking arguments remain. The existing DAG already carries each required tool.

## Not duplicates

No new nodes. All potential auxiliary facts were reused as the existing nodes above. The item itself was compared against the whole blueprint searches and has same_as = [].

## Review by Q128

I checked delivery-errors B–E against the node files and source texts. Since no nodes are created, there is no statement-only-node, naming, duplicate-tag or Mathlib-leaf certification obligation left over. Every proof step is short (524, 526, 446 and 380 characters); none hides a long extracted lemma. There is no relabelling of the item into a new node, no circular dependency and no substitution for a unit-level argument.

For step 1 I read def-pc-scheme-fibre: its statement gives the underlying-space homeomorphism onto the set-theoretic fibre, for both f and q. I read def-weil-closed-immersion: its statement gives injectivity as a homeomorphism onto a closed subset. These are precisely the two facts taken. The universal-property equations for the induced fibre map show it commutes with projection. Two points over the same p have unique lifts into Z_s, their images in P_s coincide by the other projection homeomorphism, and injectivity forces equality. This is elementary from the cited definitions, not a theorem asserting unproved fibrewise quasi-finiteness or descent of closed immersions. It uses only the topological part of the closed-immersion assumption.

For step 2 I read the full statement of lem-trf-proper-finite-fibre-finite-near, then Tag 02UP in more-morphisms.tex. It assumes just properness and a finite underlying fibre at a point. Properness is an item hypothesis and finiteness was proved in step 1; P need not be locally Noetherian. It returns exactly an open W_p containing p on which the whole inverse-image restriction is finite. I read lem-weil-pbc-finite-local-on-target: condition (3) permits an arbitrary open covering and the restriction clause preserves finiteness. Thus the W_p cover their union W and give finiteness there. No finite subcover, compactness or smallness assumption is silently required: the indexing set is the underlying set of q^{-1}(s).

For step 3 I read lemma-nagata-projective-space-base-change-proper, its current latest blueprint proof, and WeilConjectures/AlgebraicGeometry/ProjectiveSpace.lean:162–176. The statement covers every scheme S and every finite coordinate index set; choosing {0,...,r} gives the q in the item. It is a Lean-closed generic tool, so its off-unit use does not change the unit route. The definition of properness says universally closed, and using the identity base change says q maps the closed complement of W to a closed subset C. The set-theoretic inclusion q^{-1}(s) contained in W excludes s from C. Writing V_0=S minus C and checking q^{-1}(V_0) contained in W is an explicit elementary complement argument. It uses closedness of q rather than requiring W to descend as a chosen open under q.

For step 4 I read the full statement of lem-weil-pbc-affine-opens-basis and the source Tag 01IT, schemes.tex, lemma-basis-affine-opens. It supplies an affine open V about s inside the already-open V_0, with no separation or Noetherian hypothesis. I also read Tag 01WI, morphisms.tex, lemma-finite-local, matching the restriction clause of lem-weil-pbc-finite-local-on-target. Applying that clause to the finite map over W and its open q^{-1}(V) yields exactly the finite restriction in the conclusion, since its source is the inverse image under f=q composed with varphi. This final equality is written in the step and needs no unproved base-change property of finiteness.

I tested the empty Z_s case: every inverse image over a point of P_s is empty and hence finite; 02UP includes the empty fibre and the argument remains valid. For r=0 the projective fibre is one point and the same proof specializes directly. For a proper closed embedding of a positive-dimensional projective fibre the proof never declares that whole fibre finite over kappa(s); it counts points over each p. Nilpotents do not affect the argument, since the actual fibre homeomorphisms and closed-immersion injectivity suffice. Non-surjectivity of varphi_s is harmless: it simply produces empty fibres over the omitted points. No local Noetherian, nonempty, algebraically closed field or surjectivity hypothesis was added.

The repair made in this self-review was to spell out the point-set argument through both fibre homeomorphisms instead of hiding it behind an uncited claim about base-changing closed immersions. Each dependency's verbatim statement is copied into citations.json for its precise step. All non-elementary uses are represented by existing statements, not by their proofs or by source tags alone.

### Unfinished work

No unresolved mathematical issue in the split. New subnodes: none. Verification and delivery are through the required server dry run and deliver.py.
