# Worker report: lem-weil-pbc-kernel-ideal-directed-pairs

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-kernel-ideal-directed-pairs.json`: existing statement, now split into four proof steps. Statement and statement dependencies unchanged; no new nodes and no new Mathlib leaves.
- `citations.json`: verbatim supporting statement passages for every step/node citation.
- `searches.jsonl`: five actual searches logged by msearch.py; the item's inherited Q27 searches are preserved separately in its JSON.
- `report.md`: this report.

## Attachments

None. The blueprint-tag search and searches for kernel ideals, directed pairs and generated ideals in `lean/WeilConjectures/` found no declaration that states the item. The existing Hom-colimit result is in `lean/Sheaf/AlgebraicGeometry/FinitePresentationHomDirectedColimit.lean`, but its proof is `sorry`; it is an existing dependency, not a finished attachment of this item. The quasi-coherent-algebra definitions do not assert the directed-pair theorem.

## WANTED

None. All sources used were read in the repository.

## Audit and changes

The original node had no proof. I retained its full statement, including nonempty directed preorders (not necessarily posets), arbitrary compatible module approximation maps (not necessarily inclusions), the row-extension clause, the smallness clause and the quotient-map identity. I added the proof, its exact dependency union, document provenance and split report. I retained the ancestor/via metadata and searched for equivalent blueprint statements; none states this pair construction. The source relation is in Stacks 05JS; the crucial finite-presentation lift is the square in 0817(2), which cites 01BS. No integral or symmetric-algebra hypothesis from 0817 is needed for this isolated subargument, and no such hypothesis was added.

The DAG search by tags 01BS, 05JS, 0817 and by finite presentation, generated ideals, kernels and quotient algebras found all needed dependencies already present. Whole-blueprint searches included `colimit`, `finite presentation`, `kernel ideal`, `generated ideals` and `ideal-containment`. I reused the existing three lemmas instead of creating duplicates, elementary nodes or nodes restating clauses. Each belongs to the item's existing unit `sk-thm-p1`, so no off-route tool declaration is needed. I read the chapter and unit records and the current main-20261015 H1-constructible-representation proof; this item is below its finite-pushforward step and does not change the unit route.

Mathlib searches used only the prescribed msearch.py command. Loogle returned zero combined predicate matches. LeanSearch returned ring quotient finite presentation and module-sheaf finite-presentation definitions/instances. The two distinct LeanFinder phrasings returned ordinary module direct limits, local cohomology diagrams and Ind-object filteredness. Grep returned local cohomology and order ideals. These do not construct the sheaf-ideal containment preorder and its quotient diagram; no item-level Mathlib match was found. The useful finite-presentation-implies-quasi-coherence clause is already in the existing DAG lemma, which the proof cites.

## Unfinished work

None in this stage-1 split. Existing dependencies retain their own proof obligations. No Lean was written and no compiler, Lake or build command was run.

## Not duplicates

No new nodes were created. Existing generated-ideal, Hom-colimit and finite-presentation quasi-coherence nodes are cited directly.

## Repair of returned delivery e78df3fa3c7

The return dated 2026-10-22 07:34 UTC approved the mathematics but reported a side-project completion that had not been promoted to the live DAG. I compared the retained delivered item with the current read-only live item: the live node is unsplit, with empty proof and proof dependencies, and its statement, statement dependencies, source, chapter, unit, created record and blueprint metadata agree with the retained version. There is no released stage-1 repair note. The initial required dry run rebuilt the delivery against the current DAG and passed as eda5900333b (not pushed); this is the baseline check, not the repaired delivery.

I reconstructed the sandbox item from the current live JSON and overlaid the retained proof, actual logged searches and split report. I reread every current proof dependency, rather than assuming the previous review survives a rebase: `lem-weil-pbc-quasi-coherent-finite-type-affine` still explicitly supplies clause (0); `lem-weil-pbc-quasi-coherent-algebra-kernel-image-ideal` still supplies quasi-coherence and the quotient universal property in (b); and `lem-weil-pbc-finite-presentation-hom-directed-colimit` still supplies factorization through a term for a finitely presented domain on a qcqs scheme. All four citation passages remain literal substrings of these current statements. No dependency statement requires a stronger hypothesis or a replacement citation.

The proof now writes transitivity as the successive image containments under the diagram composition law, and row monotonicity explicitly invokes minimality of the generated ideal. The final source annotation distinguishes the quotient construction in 0817 from the quasi-coherence assertions of 01IC/01LA; the quotient universal property itself is taken from the cited node's statement. The target statement and route remain unchanged. No new nodes or Mathlib leaves are introduced, and the five recorded Q141 searches are retained without rerunning an unchanged search question.

## Review by Q141

I read Properties Tag 05JS (`lemma-algebra-directed-colimit-finite-presentation`, especially its last paragraph defining the order on pairs) and Tag 0817 (`lemma-integral-algebra-directed-colimit-finite`, proof (2), the displayed lift between the E terms and induced quotient map). I also read Modules Tag 01BS (`lemma-finite-presentation-quasi-compact-colimit`) and Tag 01BO (`lemma-finite-presentation-quasi-coherent`), and Schemes Tag 01IC (`lemma-kernel-cokernel-quasi-coherent`) with Section 01LA items (5) and (8). These supply exactly the lifting and quasi-coherence assertions that the source uses. There are no new node statements to validate against a separate source.

Step 1 uses clause (0) of `lem-weil-pbc-quasi-coherent-finite-type-affine`, whose statement explicitly says every finite-presentation module is quasi-coherent. It then uses clause (b) of `lem-weil-pbc-quasi-coherent-algebra-kernel-image-ideal`, whose statement explicitly gives quasi-coherence of the generated ideal and its quotient, and the quotient universal property. The inputs are the given quasi-coherent algebra S_i and the composite E_ik to J_i to S_i. This avoids the C4 mistake of treating a finite-presentation definition as a quasi-coherence theorem.

Step 2 uses the explicit factorization clause of `lem-weil-pbc-finite-presentation-hom-directed-colimit`. Its domain is E_ik, finite presentation by hypothesis; its diagram is the given nonempty directed K_j system, with the supplied module colimit J_j. The scheme is qcqs as that lemma requires. Compatibility of J with sigma gives the linear map into J_j. The factorization ensures the inverse image of I_jl contains the image of E_ik, and the defining minimality of the generated ideal then proves the full ideal containment. The map E_ik to E_jl is not assumed injective, nor is any compatibility of such choices across different pairs required.

Step 3 is elementary after Step 2. I checked transitivity using the diagram composition law for sigma and successive image containments. Row monotonicity uses precisely epsilon_ik = epsilon_il eta_lk. Two arbitrary pairs first move to a common base row, then to a common index in that row. Nonemptiness follows by choosing an element of I and one of its nonempty K_i. Smallness follows because these are sets and P is their dependent disjoint union, with no class-sized indexing construction. No antisymmetry is claimed.

Step 4 uses the universal-property clause of `lem-weil-pbc-quasi-coherent-algebra-kernel-image-ideal`, read directly from its statement: every algebra map killing the module generators has a unique factorization through the quotient. Ideal containment ensures this hypothesis for q_jl sigma_ji. Comparing the two composites with q_ik proves the composition law by uniqueness; the same comparison proves the identity law. Thus the proof establishes an actual algebra-sheaf diagram and its displayed compatibility, without selecting inconsistent lifts. I corrected the final composition's notation to write the third pair as (h,m) and its composite as q_hm sigma_hi.

For the E checks I tested X empty, all J_i and E_ik zero, singleton base and row index sets, repeated indices in preorders, zero algebra quotients and noninjective sigma/eta maps. In the zero case the relation reduces to the base order with indiscrete row comparisons, which is still a preorder and directed. In the singleton case it is just the generated-ideal quotient construction. Empty X imposes no extra geometric nonemptiness requirement. The argument never identifies a sheaf quotient with a presheaf quotient on arbitrary opens; it uses the existing sheaf quotient universal property. Every non-elementary step has its cited theorem; every citation quote was checked as a literal substring of that theorem's statement. All steps are below 2000 characters, and there are no long inline comparison lemmas hidden in them. Sections B through E produced no remaining mathematical or schema fault after these checks.

Repair review by Q141: I reread Stacks 05JS and 0817 (the relation, lifting square and quotient map), 01BS (including its preordered index and finite-cover hypotheses), 01BO and 01IC/01LA, and the main-20261015 finite-pushforward paragraph. Step 2 applies the supplied factorization theorem to the given colimit of modules, not a presumed union of submodules; all noninjective transition and repeated-preorder cases still work. The explicit step 3 uses only ideal minimality, diagram laws and directedness. The quotient maps in step 4 are uniquely characterized independently of the chosen lift, so their identity and composition laws follow by the same universal property. Rechecked the empty scheme, zero ideals/modules, singleton and equivalent distinct preorder indices, and the B--E checklist; no new non-elementary assertion or long step was introduced.
