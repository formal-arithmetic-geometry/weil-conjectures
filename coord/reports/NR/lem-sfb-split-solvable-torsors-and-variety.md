# Stage-1 delivery: lem-sfb-split-solvable-torsors-and-variety

Group NR, 2026-10-24. Direct delivery; no second worker and no Lean writing or compilation.

## Files written

All node files are under dag/nodes/sec-six-functors-basics/ in this sandbox.

- lem-sfb-split-solvable-torsors-and-variety.json: existing statement unchanged; six-step split, complete proof-dependency union, agent-origin explanation, actual new item searches appended while retaining all inherited searches and provenance.
- lem-sfb-additive-affine-torsor-section.json: new statement-only unsplit lemma; no Mathlib match. Arbitrary affine base, not just a finite-type base.
- lem-sfb-normal-extension-torsor-reduction.json: new statement-only unsplit lemma; no Mathlib match. Representability of the quotient torsor and reduction along a section, for an arbitrary normal affine group extension and arbitrary base scheme.
- lem-sfb-perfect-unipotent-additive-series.json: new statement-only unsplit lemma; no Mathlib match. Perfect-field central series of smooth subgroup schemes with additive quotients.

citations.json records a literal quotation from every statement cited by each proof step. searches.jsonl and the individual saved search outputs record the commands actually run. No new Mathlib leaves.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint id and for split-solvable groups, Lie--Kolchin/trigonalizability, additive/affine torsors, normal-extension torsor reduction and unipotent series. No project declaration states the whole item or any new lemma. Pointwise torsors, etale torsors and finite Galois covers do not constitute an attachment to the fppf group-scheme assertions here.

## WANTED

None. The actual mathematical inputs used are in the available Milne book and the available Stacks sources. The quotient-torsor construction is an agent-extracted arbitrary-base prerequisite, with its source and planned descent construction explained below; it is not attributed to a nonexistent verbatim theorem of Milne.

## Problems found and repairs

No STATEMENT-DISPUTED: all four clauses are correct. The affine-base generality is important: Milne 16.55 phrases (a) using affine algebraic schemes, while his Example 2.72 already treats an arbitrary k-algebra R_0. I explicitly retain that generality in the additive base case and in the torsor-reduction lemma. I avoid applying a finite-type-base theorem to arbitrary S.

The old statement had no proof. The new proof strengthens the induction to global sections over affine schemes with trivial Picard group; that stronger induction, proved in the item itself, is then used on the rank-one quotient to construct the variety isomorphism. Neither torsor triviality nor the variety clause has simply been moved to a new node. In particular, I do not create a node saying that the underlying split solvable variety is affine space times a torus, or that all split-solvable torsors split: these are proved here.

I reused the existing multiplicative-torsor frame geometry, affine-space Picard triviality, polynomial UFD, prime-localization UFD, extension across a factorial complement, normal group quotient, and perfect-solvable unipotent-torus nodes. No new localization/UFD/Picard lemma was needed: extending a line bundle from an open of affine space and restricting its global trivialization is a few-line argument in step 3. This proves the geometric Picard clause without a new Laurent-UFD node.

The blueprint ancestor tool returns None. The inherited created.item chain reaches lem-sfb-admissible-direct-image, whose created.item is the module name Sheaf.SixFunctors.CtfStabilityDirectImages rather than a DAG id. That node still records det-thm-sf-ctf-stability-direct-images in its own blueprint.from. The inherited item itself consequently has blueprint.from.node null. I retained the computed null ancestor, the full existing via list, and an exact textual place; each new node prepends this item to that via list. I did not edit another node to repair its provenance. This is a pre-existing provenance issue, not a change of route. I read the current latest blueprint unit and direct-images proof, including paragraph (3); the item is a supporting Borel/Picard input deep below that paragraph's existing alteration route and is not the unit's key statement.

## Sources and arguments for the new nodes

For lem-sfb-additive-affine-torsor-section I read Milne Example 2.72, printed p.61, with arbitrary R_0, and Definition 2.66/Example 2.67, printed p.60. A trivializing faithfully flat affine cover gives an additive transition cocycle in B tensor_A B. Exactness of the faithfully flat additive Cech complex makes that cocycle a coboundary; translating the local section by its primitive makes it descend. This uses no reducedness or Noetherian property. The same assertion is consistent with Stacks Tag 03P2, etale-cohomology.tex theorem-zariski-fpqc-quasi-coherent, which I read; the node's source stays the explicit arbitrary-ring assertion in Milne rather than copying an etale-only DAG statement and pretending it is fppf.

For lem-sfb-normal-extension-torsor-reduction I read Milne Example 2.68, Proposition 2.69, printed p.60, the induction in Proposition 16.55, printed p.344, and Appendix A.80--A.81, printed pp.584--585; I also read Stacks Tag 0245, descent.tex lemma-affine, and Tags 0499/049A, groupoids.tex lemma-characterize-trivial-pseudo-torsors/definition-principal-homogeneous-space. On a cover trivializing P, the proposed P/N is Q times the base. The transition functions act by left translations on Q, commute with the right Q-action, and satisfy the cocycle condition. Effective affine descent represents it by R. On the same cover the map P to R is G to Q, an N-torsor by the kernel identity. This identity and flatness/finite presentation descend. Pulling P to a section of R gives an N-torsor, and its section is a section of P. This construction commutes with base change. Affineness of Q makes scheme representability valid even for a non-Noetherian or non-quasi-separated S. The lemma does not assume local triviality in the Zariski topology or the solvable-group structure that the item is proving.

For lem-sfb-perfect-unipotent-additive-series I read Milne Corollaries 16.22--16.24, printed p.331. Corollary 16.24 gives a central normal series with additive quotients, not merely the matrix-coordinate filtration with quotients embedded in Ga. Perfectness is retained, and each subgroup is smooth and connected; the trivial group has m=0. The planned proof is Milne's induction from its central additive subgroup result 16.23. This statement is stronger than the existing existence of one central Ga, but does not assert torsor triviality, the product variety or Picard triviality.

## Mathlib and duplicate searches

For each proposed node I ran two differently phrased leanfinder searches, a loogle pattern, grep through msearch.py, and leansearch. All services returned successfully. Every record in each new node is the actual query and full output, followed by my verdict. The hits were abstract group central series, module filtrations, pointwise AddTorsor structures, affine-space constructors, abstract extension sections, closed-immersion factorization, or topological covering torsors. They give no one-line specialization to the scheme statements. The item was separately searched with both inherited semantic phrasings, its Loogle pattern, grep, and LeanSearch; actual new outputs were appended while keeping the old records.

I searched the whole DAG by concepts and Milne places 2.72, 16.24, 16.52--16.56; by the new ids; and by additive torsor, quotient torsor, unipotent series, and Picard/UFD concepts. I ran tools/blueprint_refs.py searches for solvable, torsor, unipotent, normal subgroup, additive torsor, torsor quotient, and central normal series. No blueprint node states a new lemma or the whole item. The existing Lie-algebra solvability nodes concern a different object. The existing etale H1/torsor results are not general fppf affine group-scheme torsors. No new source has an unqualified Stacks tag shared with an old node, but the closest conceptual pairs are distinguished below.

## Not duplicates

lem-sfb-additive-affine-torsor-section vs lem-sc-torsor-h1: the existing node classifies torsors for an abelian sheaf on the small etale site; it does not give a section for a represented additive fppf torsor over an arbitrary affine base.
lem-sfb-additive-affine-torsor-section vs lem-sfb-split-torus-torsor-frame-geometry: the existing result concerns multiplicative tori and invertible-module frames; the new result concerns the additive group over affine schemes.
lem-sfb-normal-extension-torsor-reduction vs lem-sfb-affine-normal-quotient-geometry: the existing node gives G/N and the torsor G to G/N for groups over a field; the new node represents P/N for an arbitrary G-torsor over arbitrary S and gives the fiber torsor along a chosen quotient section.
lem-sfb-normal-extension-torsor-reduction vs lem-sfb-affine-group-torsor-stackification: the existing equivalence with an action quotient stack does not state reduction along a normal subgroup, P/N or the section fiber N-torsor.
lem-sfb-perfect-unipotent-additive-series vs lem-sfb-unipotent-central-additive-subgroup: a single central Ga subgroup is not the full finite central series of smooth subgroup schemes with represented Ga quotients.
lem-sfb-perfect-unipotent-additive-series vs lem-sfb-unitriangular-coordinate-filtration: the existing node filters the entire upper unitriangular matrix group; its intersections with an arbitrary unipotent subgroup need not be smooth connected, and are not automatically additive quotient series. The new perfect-field result is what justifies that stronger conclusion.
lem-sfb-perfect-unipotent-additive-series vs lem-sfb-smooth-unipotent-solvable: solvability means commutative successive quotients, not Ga quotients or a central smooth connected series. The new statement imposes perfectness and supplies that stronger series.

## Review by NR

I read the full item statement and the cited Milne source, in particular 16.55 and 16.56 rather than treating the imported source field as a proof. I checked all cited node statements directly, not their proofs. citations.json contains the exact parts used, and for the normal quotient correspondence it quotes the full statement so that both the torsor property and the inverse-image clause are visible. I also checked the definition statements for schemes, groups, subgroups, fppf covers, sheafification, smoothness/finite presentation, Ga/Gm, local Noetherianness and invertible modules used in the newly stated lemmas.

Step 1 uses the new additive affine section theorem exactly with a restriction to an affine open of S. Its multiplicative input is the existing rank-one frame geometry, valid for arbitrary k and S; local rank-one bases from def-sc-invertible-module are precisely sections of its frame scheme. Restricting the torsor identity along a section constructs the inverse equivariant isomorphism; no unproved claim that a section exists is hidden in that sentence.

Step 2 states both inductive assertions and the length-zero base, takes the first normal term N, and uses exactly the new quotient/reduction statement for the represented quotient Q. After choosing a Q-section the fiber is an N-torsor, not a Q-torsor and not an asserted group extension. The shorter split series is available for N. The affine Picard-zero induction stays over S, whereas the arbitrary-base induction refines the Zariski cover. Thus it never assumes that an arbitrary torsor is globally trivial, and there is no appeal to this item's conclusion as a black box.

Step 3 uses the finite-type-over-Noetherian node only with a field spectrum and affine space, not with arbitrary S. The field is Noetherian from its two ideals and pqf-def-locnoeth supplies the affine criterion. Polynomial UFD, the affine-open stalk-localization node, and prime-localization UFD give the required factorial local rings. The extension node gives an actual extended invertible module on affine space; the affine-space triviality node makes it trivial; restriction then gives the conclusion for every open. This is the Noetherian proof in Stacks 0BDA, written as steps rather than a duplicated node. The empty open is vacuous. No statement about Cl=Pic from Milne Appendix A.78 is used.

Step 4 uses the existing affine-normal-quotient node to obtain H to H/H_1 as an H_1-torsor. The quotient is Ga or Gm by the given series, so step 3 proves affineness and Picard triviality of its base; step 2 supplies a global section for the shorter group. Translation produces a scheme product, sufficient here. I explicitly avoid claiming that it is a group product or that the section is a homomorphism. Incrementing r or s proves the full variety clause without an identical supporting node.

Step 5 is an elementary application of steps 3 and 4. Base change of the coordinate rings puts the product over K inside affine (r+s)-space as D(the product of the last s coordinates), including s=0. Restriction of an extended trivial line bundle proves Picard triviality for every extension K, with no algebraic-closedness requirement on K.

Step 6 uses the perfect-solvable unipotent-torus node precisely under its hypotheses: k algebraically closed is perfect, and H has smoothness, connectedness, affineness, finite type and solvability. Its torus quotient is split by the node's own definition over the algebraically closed field. The normal-quotient correspondence statement supplies smooth connected inverse images of the coordinate subtori and their successive quotients. The new perfect-unipotent series applies to its smooth connected U and is appended to that tower. No characteristic-zero Lie-algebra statement is substituted for positive-characteristic algebraic groups.

Against delivery-errors B--E: all new nodes are self-contained statements only with empty proofs/dependencies, actual searches, unique ids, precise Milne places, explicit notions and blueprint provenance. They are not elementary facts, duplicates, or restatements of any conclusion of the item. Proof uses equals the exact dependency union; every non-elementary input is cited, all citation quotes are literal, no proof-local construction is borrowed from another node, no false normality or base-field assumption is inserted, and all constructions identify the intended scheme or torsor. Every proof step is below 1000 characters, so none meets the 2000-character long-step threshold. I tested trivial H, Ga, Gm, mixed products, rank-zero tori, arbitrary nonreduced affine bases, and the empty scheme. The perfect-field hypothesis of the unipotent node is essential and retained; wound unipotent groups over imperfect fields are not claimed to split.

I corrected the prospective Picard proof before writing it: prime localizations of a UFD alone do not make arbitrary line bundles globally trivial; the actual proof now extends from the open to affine space and applies the existing global affine-space triviality. I also chose the generic torsor quotient input rather than falsely taking its representability from the statement of the group-only quotient node. These are the two main C4 checks for this split.

## Remaining work and verification

Only the three new supporting nodes remain unsplit, as required for a one-level split. No Lean files were changed or built. The optional server check_dag and review_split checks passed; the required delivery dry run below will check the full new-node payload against current live state. No off-unit tool declaration is needed beyond Mathlib leaves: the non-Mathlib results used all belong to this item's unit.
