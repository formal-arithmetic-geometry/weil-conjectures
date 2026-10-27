# Stage-1 worker report: lem-sfb-stack-qcoh-direct-sums

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-stack-qcoh-direct-sums.json`: existing statement, now split into six proof steps; no exact Mathlib match.
- `citations.json`: verbatim statement extracts for every step/node citation.
- `searches.jsonl`: actual Q71 Mathlib search log maintained by msearch.py.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. There were no prior sandbox node files or report to reuse. The live item's original Q32 search records, statement, statement dependencies, source, creation record and blueprint ancestry were retained.

## Attachments

None. Searched the project WeilConjectures source for the blueprint id, quasi-coherent notions, and coproduct/direct-sum combinations. The project has scheme and derived-scheme results but no declaration proving this full stack statement. In particular sorry declarations and partial scheme results were not treated as attachments.

## WANTED

None. The proof uses local Stacks sources already available in literature.

## Findings and changes

The statement is correct, including the absence of quasi-separatedness. The live node had no proof. Its global-section clause does not follow by commuting a sum past an overlap equalizer: the overlap need not be quasi-compact. Instead global coordinate projections give global candidate summands immediately; only a uniform finite support must be established on the quasi-compact atlas. Faithfulness of atlas restriction then proves the finite-sum identity globally. The assertion was not weakened or changed.

The ambient sum is not assumed to be sectionwise on arbitrary tests. It is sheafified first. Only evaluation on an affine test of the resulting quasi-coherent sum is identified with a module direct sum. The big-fppf comparison functor is used for colimit preservation only, never for exactness or kernels.

Read the latest blueprint unit and its direct-images proof (3), and the imported chapter/unit records. This is a module-theoretic prerequisite of the inherited polynomial/Rees input below that unit; it does not replace a unit step. Whole-blueprint searches for quasi-coherent, direct sums, coproduct and 06WN found no exact blueprint duplicate. The original ancestor command returns None, as already recorded by the inherited null from.node; that ancestry and its precise supporting-input place were preserved.

Generic tools from other units are declared in split_report.tool_uses: ambient ringed-site module colimits, scheme quasi-coherent coproduct closure, and affine evaluation of quasi-coherent colimits. The affine basis and quasi-compact-space definitions are existing Mathlib leaves. No new statement-only lemma is necessary: the coordinate calculation, finite union of supports, and section/map identification are written as steps, rather than introduced as elementary nodes.

## Mathlib search evidence

Ran msearch.py with LeanFinder in two genuinely different phrasings (stack sums and finite support; compactness of the structure module), Loogle for quasicoherent, LeanSearch for the global-section comparison, and grep both for stack/coprod results and in AlgebraicGeometry/Modules. Every query and its actual returned result summary is appended to the existing mathlib_searches; searches.jsonl contains the executed Q71 queries. All services answered. The candidates define local presentations or give colimits of all module sheaves on schemes; none states the stack theorem. Read Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean, AlgebraicGeometry/Modules/Sheaf.lean (HasColimits at line 53), AlgebraicGeometry/Modules/Tilde.lean (quasi-coherence instances at lines 465 and 468), and CategoryTheory/Sites/GlobalSections.lean: global sections there are a right adjoint, without this preservation theorem. The affine-transition limit hits concern a different limit theorem and impose different geometric hypotheses.

## Not duplicates

No new nodes were created. Reused the existing scheme coproduct and affine-evaluation nodes, the big-fppf equivalence and inverse-image nodes, and the atlas descent node, rather than creating stack-colimit or scheme-section variants.

## Review by Q71

I read Stacks stacks-sheaves.tex Tag 06WN (lemma-qc-colimits), including its proof, 06WI (lemma-characterize-quasi-coherent), and 06WT (proposition-quasi-coherent) with its explicit restriction functor. I also read 06WV (lemma-quasi-coherent-algebraic-stack) to check that the ambient inclusion is not being assumed left exact. For the scheme comparison I read descent.tex 03DX (proposition-equivalence-quasi-coherent), 06VE (lemma-equivalence-quasi-coherent-limits), and lemma-qc-colimits. For affine calculations I read schemes.tex 01ID (lemma-colimit-quasi-coherent), 01IT (lemma-basis-affine-opens), and Section 01LA's closure assertions. For the atlas convention I read stacks-properties.tex 04YC (lemma-quasi-compact-stack). Ambient sheafification is sites-modules.tex 03DB (lemma-limits-colimits), whose proof constructs the sheafified sectionwise colimit. There are no new-node sources to certify.

For step 1, I opened lem-weil-pbc-module-sheaves-colimits-forgetful and checked that its statement supplies existence and the sheafification formula for a small diagram on an arbitrary ringed site, not merely on an etale scheme site. The given universe convention makes A small. Its statement supplies all of the step's non-elementary content.

For step 2, I opened all five cited statements. Scheme restriction gives the actual associated-sheaf formula for each summand. Scheme coproduct closure applies without compactness or separatedness. The big-fppf equivalence explicitly preserves ambient small colimits; fibred inverse image explicitly preserves ambient sums, with no flatness hypothesis on the scheme test. These prove the local comparison before quasi-coherence of F is asserted. The definition's local free presentations then prove quasi-coherence object by object. Full faithfulness, not an unnamed comparison theorem, identifies the canonical scheme coproduct with F_x. The universal property is the restriction of the already established ambient one to the full subcategory.

For step 3, I checked the global-section compatible-family definition. The maps from the structure sheaf are literally r mapped to r times s at each site object, so no general Yoneda theorem is being inferred from a weaker fully-faithful node. The coordinate projections come directly from the coproduct universal property. Applying them proves injectivity on the algebraic finite-support direct sum; this is elementary and uses no compactness.

For step 4, the quasi-compact atlas is precisely what the cited definition permits. The affine-basis statement and the definition of quasi-compactness give a finite affine open cover without saying anything about intersections. I opened the affine-colimit-evaluation node: its diagram may be any small category, so the discrete diagram on A is allowed, and its hypotheses include quasi-coherence of the apex, already proved in step 2. Evaluation on each affine scheme itself gives finite support there. Taking the finite union of these supports and the Zariski sheaf separatedness condition proves the displayed identity on U. No global-section preservation on U has been assumed.

For step 5, I opened the current smooth-atlas-module-descent statement. It explicitly states an equivalence with algebraic-space relations and gives its action on morphisms by restriction to U_et; therefore restriction is faithful. Its hypotheses allow arbitrary diagonals and require no quasi-separatedness. The scheme-test comparison says the restricted map on every etale W over U multiplies by the pullback of the same section on U. Thus zero on U is zero as an entire restricted morphism. Both its source (the rank-one structure module) and target are quasi-coherent. Faithfulness then proves the required zero map globally. I used no effectiveness or equalizer assertion beyond that statement.

For step 6, I checked linearity and naturality on the summand maps explicitly. All sections and module actions are the compatible families defined in the statement. Bijectivity and these identities give the asserted module isomorphism, including naturality in the family.

I checked the delivery-errors B--E requirements against the files: no new nodes, no moved clause, no hidden exactness or compact-overlap assumption, no statement change, and no unproved comparison disguised as transport. Every cited node was read and every quote is literally in its statement. The first dry run requested a longer scheme-restriction quote for step 5; I replaced the evaluation-only excerpt with its complete statement, including the natural pullback formula actually used. The cited dependency closures were checked for a path back to this item and none occurs. Every proof step is below 2000 characters. The statement's edge cases are valid: A empty, an empty stack/atlas, all zero summands, and a zero coefficient ring; in the empty-atlas case faithful restriction forces every global section to vanish. As a boundary check, an infinite disjoint union of points is not quasi-compact and admits the section with a different nonzero coordinate on each component, explaining why compactness is needed for surjectivity. No restriction was silently added to A or to the overlap space.

## Unfinished work

No mathematical part of this item's stage-1 split remains. The dependencies are existing nodes; their further splitting or formalization is outside this delivery. No Lean files were written and no compiler, Lake, or build tool was run.
