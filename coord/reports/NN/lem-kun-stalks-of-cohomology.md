# Stage-1 report: lem-kun-stalks-of-cohomology

## Files written

- dag/nodes/sec-smooth-purity/lem-kun-stalks-of-cohomology.json: statement, split into three steps; no new nodes or new Mathlib leaves.
- citations.json: verbatim statement excerpts for every proof citation.
- searches.jsonl: searches executed by the prescribed search command.

## Attachments

None. Searched WeilConjectures in the read-only slopmaster2 checkout for the blueprint id, stalk/cohomology and stalk/homology terminology, and the upstream Lean-name index. Read the project EtalePoint extension: its results concern conservativity and equality of sheaf morphisms, not the cohomology formula. Fourier-transform and Weil-sheaf stalk results do not give the general unbounded abelian-sheaf formula. No upstream master sorry is treated as a finished proof.

## WANTED

None. The blueprint proof, Stacks homology.tex and derived.tex are available locally.

## What was wrong or missing

The imported argument suppressed the image and quotient calculation. It now displays the exact sequences identifying cycles, boundaries and their quotient after taking stalks. An arbitrary representative suffices: the suggestion of K-injectives was unnecessary and would add an existence assertion. Added statement dependencies for inverse image and cohomology sheaves. The equality in the statement is the customary notation for the canonical isomorphism, not literal equality of independently chosen objects; the final step makes this interpretation explicit. No mathematical change to the statement is made.

The item uses abelian sheaves, as the existing derived-category definition explicitly specifies for D(T_et) without a coefficient ring. No pro-etale, condensed, or completed coefficient categories are substituted. No hypotheses such as boundedness, properness or torsion are introduced.

## Unfinished work

None at this level. The existing stalk-as-pullback split remains an existing dependency, not a new assertion to split here.

## Mathlib and duplicate searches

Searched the whole blueprint for 'stalks of cohomology' and 'stalk cohomology', and the whole DAG for exact-functor/cohomology commutation. The pro-etale conservativity result has a different coefficient category and conclusion. No second node states this item; same_as is empty. Existing exactness, stalk-as-pullback and derived-category nodes already suffice, so no lemma is created merely to restate this calculation. No unit record is changed: this node is not the key proposition realizing the Kunneth unit.

Both semantic phrasings, Loogle patterns, grep patterns and the unavailable LeanSearch request are recorded exactly from searches.jsonl. Read Mathlib/Algebra/Homology/ShortComplex/PreservesHomology.lean:455-458 (mapHomologyIso) and the finite-limit/colimit instance at :60; it is the abstract comparison for a short complex and an already homology-preserving functor. The complete item additionally identifies geometric-point inverse image with the termwise stalk and its action on derived objects, supplied by the existing lem-kun-stalk-as-pullback. Consequently no exact whole-item leaf is claimed. The elementary exact-sequence calculation is written directly rather than made into an artificial new generic node.

## Review by NN

I read the item's master-blueprint statement and its single proof paragraph, its chapter and Kunneth unit records, and Stacks Tag 010N (homology.tex, lemma-exact-functor, especially the factorization through the image in its proof). I also read Tag 015F (derived.tex, lemma-right-derived-exact-functor), whose proof explains why an exact functor is computed termwise; the omitted details needed here are the explicitly written cycle/boundary calculation. This is an agent expansion of the blueprint, not a claim that Stacks contains the full geometric-point statement.

Step 1 takes from def-weil-pbc-derived-categories exactly its localization by quasi-isomorphisms and its cohomology formula Ker d / Im d for any representing complex. The quoted statement includes both the abelian-sheaf convention and that formula. The inclusion of boundaries in cycles is just d squared equals zero. This step is elementary and uses no resolution theorem.

Step 2 takes only exactness of the abelian-group-valued geometric stalk from prop-weil-pbc-geometric-stalks-exact, whose statement I read in full. I checked that the point is geometric and that the input category is Ab(T_et), precisely its hypotheses. The three short exact sequences are in this same abelian category; images, inclusions and quotients are categorical sheaf images and quotients. Surjectivity onto the stalk of the image, followed by injectivity into the stalk of the next term, proves the image assertion; the kernel assertion and quotient then follow from the written sequences. Thus 'commutes with kernels and images' is no longer an unproved extra assertion. This is elementary once the cited exactness theorem is granted; Stacks 010N is a source for the displayed argument, not an uncited additional black box.

Step 3 takes from the statement of lem-kun-stalk-as-pullback the identification of the stalk of a derived object with its inverse image along the geometric point. I opened that node and read its statement and existing proof to check the convention: sheaves on Spec Omega are identified with abelian groups and the exact inverse-image functor acts termwise. I do not take any further conclusion from its proof or use its proof's cohomology-compatibility sentence as a substitute for step 2. The naturality argument is explicit: a chain map sends each kernel and image to its corresponding kernel and image and therefore induces the quotient map. The formula in every degree then shows that quasi-isomorphisms remain quasi-isomorphisms, establishing independence of the representative. All cited statements have verbatim quotations in citations.json. I read the newly cited inverse-image and cohomology definition statements as well; they define the notions actually used.

For delivery-errors B, there are no new unsplit nodes, hollow definitions, missing new-node sources or unrun searches; JSON retains the imported metadata and uses single TeX escaping. For C, each non-elementary input is the statement of an existing cited node; no definition is used as a theorem, no proof-only assertion is borrowed, and no new index-category colimit is constructed. Exactness is a Mathlib leaf and the pullback identification is in the same unit, so no off-route tool declaration is needed. For D, the argument stays in the item and creates no restatement or circular child. For E, I checked zero complexes, complexes in one degree, an acyclic complex, and arbitrary unbounded complexes degree by degree: all use only three neighbouring terms, so no boundedness or convergence hypothesis is hidden. The empty scheme has no geometric point, so its assertion is vacuous. The case of a geometric point of a separably closed field uses precisely the point-site equivalence already packaged by the pullback node. No source dispute arose. No statement was weakened and no source or project Lean file was written or compiled.

## Second reading by NN

- Item statement: checked against the master-blueprint lemma, order 1702, its complete proof paragraph, and the Kunneth unit; the same arbitrary derived abelian-sheaf object and geometric point occur, with no finiteness, boundedness or coefficient restriction added. The formula holds for every integer q; equality denotes the canonical isomorphism, as already explained. Verdict: faithful.
- Step 1: opened def-weil-pbc-derived-categories and checked its abelian-sheaf convention, localization definition and kernel/image quotient formula. The inclusion of boundaries in cycles follows from the complex identity. Verdict: elementary and correct.
- Step 2: opened prop-weil-pbc-geometric-stalks-exact and Stacks homology.tex, Tag 010N, lemma-exact-functor, especially the two short exact sequences in the kernel/image factorization. The cited statement gives exactness for precisely the abelian-sheaf stalk used here. Surjectivity onto the image and injectivity into the next term identify both kernel and image, and the third sequence identifies the quotient. Verdict: correct elementary calculation, including for unbounded complexes.
- Step 3: opened lem-kun-stalk-as-pullback and def-weil-pbc-derived-categories; checked Stacks derived.tex, Tag 015F, lemma-right-derived-exact-functor. The pullback node's statement identifies derived stalk and inverse image, but does not itself state the termwise model. Repaired the order: the natural quotient comparison from step 2 proves preservation of quasi-isomorphisms, and localization then gives the termwise model before invoking that identification. Naturality also commutes with inverted quasi-isomorphisms. Verdict: repaired; no assertion borrowed from a cited proof.
- New nodes: none; no child merely restates the item or its clauses, and B1-B7 impose no new-node repair. Independently searched DAG tags 010N/015F and stalk/cohomology terminology; existing generic exact-functor nodes are unnecessary because the calculation is written here. Ran fresh LeanFinder and Mathlib grep queries via msearch.py with different phrasing; read ShortComplex/PreservesHomology.lean:455-458. These provide abstract homology preservation, not an exact whole-item geometric-point comparison. Verdict: retain zero new nodes and zero new Mathlib leaves.
- Edge cases: zero complex gives zero on both sides; a sheaf in degree zero gives its stalk in degree zero and zero in degree one; the two-term identity complex is acyclic before and after taking stalks; over a separably closed field the comparison reduces to the same kernel/image quotient calculation on groups. The empty scheme has no geometric point. Only three adjacent terms are used in each degree, so negative degrees and unbounded complexes require no additional hypothesis. Verdict: no statement dispute.

Changes: rewrote only step 3 to derive termwise descent from step 2 and localization, rather than taking it from the proof of the stalk-as-pullback node (C3/C4); made descent of naturality through inverted quasi-isomorphisms explicit (E5); added its localization-definition citation and a verbatim statement quote in citations.json. Steps 1 and 2, the item statement, and the first worker's review are retained. Fresh search results are recorded unaltered in searches.jsonl. The prescribed delivery invocation with a trailing dot is not accepted by this tool's argument parser; its documented two-positional-argument syntax is used instead.
