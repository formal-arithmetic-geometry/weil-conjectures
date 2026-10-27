# Q147 stage-1 delivery

## Files written

- dag/nodes/sec-trace-formula/lem-trf-terminal-bar-evaluation-compatibility.json: item, split into five explicit generator calculations; not a Mathlib leaf.
- citations.json: verbatim statement excerpts for all six step/node citation pairs.
- report.md: this report.
- searches.jsonl: authentic search-command log, retained unchanged.

No new nodes and no Mathlib leaves were created. The original statement, statement dependencies, source, created record and blueprint provenance are retained. No Lean file was written or compiler invoked. The shared repository and launcher were read only.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag and for terminal/bar/evaluation and extra-degeneracy terminology found no declaration giving the item. The presheaf Cech exactness helpers concern another augmentation and do not give its statements.

## WANTED

None. The required Stacks source is present locally.

## Problems found and changes

The item was unsplit, with no proof. Its statement is correct with the stated reverse-face convention. I retained every clause and supplied the sign comparison, chain-map/uniqueness check, a terminal-arrow contraction, the direct cycle/boundary calculation, and the exact reindexing formulas. In particular, no unspecified comparison in the derived category substitutes for equality of the specified chain maps.

The live item remained unsplit with unchanged statement on resumption on 2026-10-24; no released repair note exists. No delivery had been started before the pause: the report and dry run were the unfinished steps. The previous searches and proof were reused. The latest chapter and unit texts were read, as well as the recorded DAG chapter/unit. The latest blueprint has expanded the surrounding trace-formula discussion; this auxiliary bar calculation preserves the item's inherited unit and ancestral route.

## Unfinished work

None in the mathematical split. Server validation and direct delivery are the final operations. There are no statement-only new nodes requiring later searches or proof work.

## Sources and search results

I read sites-cohomology.tex, example-left-derived-colimits (08PG, lines 10044 onward), example-morphism-categories (08PH, lines 10117 onward), and lemma-compute-by-cosimplicial-resolution (08Q9, lines 10229 onward). I also read cotangent.tex, lemma-polynomial-on-top (08QV, lines 1222 onward), whose constant polynomial target motivates the canonical augmentation. The displayed K differential and functorial map are in 08PG/08PH. The sign conversion and contraction here are agent-written explicit calculations, so proof_origin.by is agent. No SGA route is used.

Five actual msearch invocations were made and recorded on 2026-10-23, including two semantic phrasings, Loogle, grep and LeanSearch. Their responses were read before the pause, and searches.jsonl is retained. The item's inherited search records from 2026-10-22 remain intact. Loogle and grep gave no hits. LeanSearch returned evaluation, homology and terminal simplicial-set APIs. The first LeanFinder response returned monoid/group standard resolutions, projective resolutions and their quasi-isomorphisms. The second returned ExtraDegeneracy.homotopyEquiv, the universal-cover extra degeneracy, and Dold--Kan homotopies. I read Mathlib/RepresentationTheory/Homological/Resolution.lean, including standardComplex, its augmentation and quasiIso_forget₂_εToSingle₀ at line 306, barComplex.isoStandardComplex, and Mathlib/AlgebraicTopology/ExtraDegeneracy.lean, including the structure at line 72 and homotopyEquiv at line 415. These do not supply the stated arbitrary-category coefficient calculation with reversed faces and strict reindexing. Applying the extra-degeneracy API would require constructing precisely the terminal-append maps and verifying their identities; that short calculation is instead written in step 3. Hence no Mathlib match is claimed and no generic contraction theorem is silently used.

DAG and whole-blueprint searches included bar, terminal, bar complex, and terminal object, together with terminal/augmentation/sign keywords in the DAG. The whole-blueprint searches for bar complex and terminal bar returned no matching nodes. The broad searches produced surrounding geometric statements, not this module bar assertion. I read the related existing statements listed below. No new node is required, and blueprint.same_as remains empty.

## Not duplicates

No new-node pairs arise. The following nearby existing nodes were checked for reuse:

- lem-sc-preorder-bar-terminal-augmentation concerns preorders and total complexes of complex-valued diagrams, not arbitrary ordinary categories or the present two bar conventions. Its restriction to preorders cannot prove this item.
- lem-trf-section-comma-bar-contraction concerns a section/comma construction and a contravariant coefficient system; it does not state arbitrary covariant terminal evaluation and the sign identification.
- lem-coef-extra-degeneracy-contraction gives simplicial-set homotopies after extra-degeneracy identities are supplied. It does not state this coefficient complex assertion.
- lem-coef-ordinary-bar-evaluation-naturality concerns bisimplicial sets and comma-chain evaluation, not these module chain maps.
- lem-trf-two-sided-bar-horizontal-augmentation contracts horizontal rows indexed by chains ending in a specified Q_q. It is useful in the general two-sided resolution argument but is unnecessary for this direct terminal contraction.
- lem-trf-augmented-presheaf-bar-resolution gives contractions on presheaf evaluation with an additional representable arrow, rather than terminal evaluation of an arbitrary covariant coefficient functor.

## Review by Q147

I reviewed delivery-errors B through E, including both copies in that file. There is no new-node form or concealed statement-only proof to check: every new mathematical construction is a step of this item. No step restates a clause as an assumed lemma. Every step is under 900 characters and the only calculation longer than a few displayed lines is fully expanded into its face cases and alternating sum. There is no long step over 2000 characters or hidden comparison lemma.

For step 1 I reopened the statements of lem-trf-derived-colimit-bar and lem-trf-simplicial-derived-colimit-computation. The former specifies deleting U_(n-j) and restricting the coefficient only in the last face; after passage from J^op this is numbering from j_n on a covariant chain. The latter gives the first-vertex faces and their coefficient action. Thus these statements give exactly the two formulas used, without needing their proofs or contractibility hypotheses for a simplicial resolution. Reversing the index gives d_K=(-1)^n d_B, and lambda_n=(-1)^n lambda_(n-1) proves the chain-map equation. Its inverse is the same scalar, and its degree-zero component is one. Naturality follows on each summand because coefficient and indexing maps preserve degree and are R-linear; no general naturality theorem is assumed.

For step 2 the cited bar statement gives the two degree-one faces, with the K sign yielding (j_0,x)-(j_1,H(f)x). I checked the terminal identity !_j1 f = !_j0, including !_t=1. This proves the augmentation is a chain map and its degree-zero inclusion is a section. Uniqueness is only the direct-sum universal property and zero target components.

For step 3 the same cited face statement gives every face of the appended-terminal generator. I checked deletion of the new terminal vertex, deletion of the previous final vertex (using uniqueness of its arrow to t), deletion of an internal vertex, and deletion of the initial vertex (where H acts on the coefficient). Consequently the shifted alternating sums cancel pair by pair. The degree-zero case was checked separately: d s_0 = 1-e epsilon. This supplies the entire contraction; no cited node is being asked to assert terminal contraction. This is an elementary computation from the stated face formulas, not an appeal to a standard lemma.

For step 4 I reopened def-weil-abstract-derived-category: it defines cohomology by kernel modulo image, quasi-isomorphisms by cohomology isomorphisms, and D as localization at these maps. The proof directly writes every negative cycle as a boundary using step 3, and explicitly gives inverse degree-zero cohomology maps using step 2. Thus the definition supplies exactly the conclusion drawn from the computation. No unlisted homotopy-invariance theorem is needed.

For step 5 the reindexing generator formula is copied verbatim into citations.json from lem-trf-derived-colimit-bar. For our covariant indexing u it is applied to u^op between the identity-cover sites, with identity coefficient map; these are small by hypothesis. I checked the composite degree by degree, including I empty. Selecting t gives the identity coefficient because !_t=1_t. On the singleton category all faces are identities, giving the asserted alternating complex, not the single-degree complex; its augmentation is identity only in degree zero. Multiplication by lambda_0=1 and strict scalar/reindexing commutation leave precisely the same augmentation equations under sigma. The proof makes no claim that arbitrary u gives a quasi-isomorphism.

Hypotheses and edge cases: direct sums are legitimate in the fixed universe; each generator maps to one summand, so no finiteness of the category or module is needed. A terminal object forces J nonempty, whereas I is allowed empty. Identity arrows and repeated terminal vertices are allowed in the unnormalized bar construction. I checked n=0,1,2: lambda is 1,-1,-1 and the contraction signs agree; on the one-object identity category d_n is zero for odd n and one for even positive n. A nontrivial arrow j to t has boundary x-H(f)x, which verifies the nonconstant coefficient case. The zero module, zero ring and characteristic two cause no difficulty, since all sign arguments use only additive inverses. I did not assume H is flat or projective, and did not assume u preserves terminal objects.

Finally I verified that proof_deps is the union of uses and each citations.json excerpt is an exact substring of the current cited statement. There is no new dependency cycle: the used bar statements are already statement dependencies of this item, and the remaining used derived-category definition is also a statement dependency. No correction of the imported statement or its intended application was necessary.
