# Stage-1 worker report: lem-kun-lower-truncation-flat-model

## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-lower-truncation-flat-model.json`: statement, split in five steps; no whole-item Mathlib match.
- `citations.json`: eight verbatim statement excerpts, one for each dependency cited by each proof step.
- `report.md`: this report. The search command maintains `searches.jsonl`.

No new nodes or Mathlib leaves. No unit record changed: this item is an auxiliary node, not the unit's statement.

## Attachments

None. Searched `lean/WeilConjectures/` by the blueprint tag, lower-truncation/flatness terminology and truncGE/flat patterns. No project declaration states the whole item. The affine connective truncation theorem concerns quasi-coherent scheme modules and a different hypothesis package; it does not supply the general constant-coefficient etale sheaf kernel and K-flat clauses. Existing declarations for generic subsidiary tools are reused through their nodes.

## WANTED

None. All mathematical sources used are present in `literature/`.

## Corrections and source comparison

The item's statement is true as supplied and was retained verbatim. Its dependencies already name the site, size convention, constant coefficients, complex, flatness, cohomology, truncation, quasi-isomorphism and K-flatness notions used by it. Previously empty proof and proof-dependency fields are now filled.

Read the chapter and the Kunneth unit, Stacks sites-cohomology Tag 0F1M (`lemma-bounded-below-tor-amplitude`, especially the displayed lower truncation and kernel), and the current main-20261015 blueprint proof of lem-kun-0f1m. The blueprint writes the lower-truncation arrow in the wrong direction in one sentence, although its following kernel formula is for the quotient map. Stacks and the present item correctly use K -> P; no correction to this item's statement is needed. This split proves that quotient's quasi-isomorphism directly and does not use the blueprint's later homotopy-cone claim, which is outside this item. The item does not assume K is K-flat, and the proof never needs it.

For the kernel-flatness step read sites-modules Tag 03EY (`lemma-flat-ses`), part (2), including its explicit extension to sheaves, and the neighboring Tag 03EX (`lemma-flat-tor-zero`). For the final step read sites-cohomology Tag 06YQ (`lemma-bounded-flat-K-flat`); verified these tags in `tags/tags`. The existing same-unit lem-kun-kflat-criteria clause (1) states precisely the needed result. The source tag in the more general lem-pc-bounded-above-flat-kflat-site record is not used here.

## Mathlib and duplicate searches

Retained every inherited search record. Ran LeanFinder with two phrasings, Loogle, LeanSearch and two grep queries using the required msearch.py command; the exact tool/query/result records were appended from searches.jsonl. All services answered. Read Mathlib/Algebra/Homology/Embedding/CochainComplex.lean lines 277-285: quasiIso_piTruncGE_iff and its instance give the ordinary truncation quasi-isomorphism only. The second LeanFinder query returned Module.Flat tensor-exactness criteria for ordinary modules; these do not state the constant-coefficient sheaf-complex result. No whole-item Mathlib leaf is warranted.

Searched all DAG statement/title records for bounded-above flatness and flat kernels, the existing parent's proof dependencies, and the whole imported blueprint through blueprint_refs.py searches for 'truncation flat', 'bounded above flat', 'lower truncation' and 'flat kernel'. Reused lem-weil-pbc-site-flat-quotient-tensor-ses and lem-kun-kflat-criteria. The elementary quotient, chain-map, degreewise kernel and cohomology calculations stay as proof steps.

## Not duplicates

No new nodes: no duplicate pairs to justify. This split uses strictly smaller existing statements. In particular, the generic kernel-flatness theorem concerns one short exact sequence of sheaves, and K-flat criteria (1) concerns bounded-above flat complexes without this truncation construction.

## Review by Q45

I checked the proof against the sources with each cited node's statement open. The chosen small skeleton satisfies the small-site hypothesis of the flat-quotient lemma, and the constant sheaf Lambda_T is a sheaf of commutative rings. No module-sheaf flatness is replaced by sectionwise flatness, and no sheaf epimorphism is treated as a surjection on sections.

Step 1 uses the explicit good-truncation formulas of def-kun-truncations and the chain-map equations of def-pc-cochain-complex-modules. The cokernel factors d^a because d^a d^{a-1}=0, its next square vanishes by cancellation of the cokernel epimorphism, and the two boundary chain-map equations are written out. These are universal-property calculations, not an unrecorded resolution theorem.

Step 2 uses exactly the cohomology quotient of def-pc-acyclic-complex-modules and the all-degrees criterion of def-pc-quasi-iso-modules. At a the kernel in K^a/I is ker(d^a)/I; at a+1 the image of the induced differential equals the original image since the projection onto N is epic. Below a the assumed cohomology vanishing is essential. Thus this step checks the induced map, rather than just asserting two cohomology objects have the same names.

Step 3 uses the complex equations and abelian category of def-pc-cochain-complex-modules. Kernels and the boundary image factorization give the displayed L, and the three degree ranges give the short exact sequences explicitly. Image equals kernel of the cokernel in this abelian category; this does not require H^{a-1}(K)=0. The differential into I squares to zero because its composite into K^a does and that inclusion is monic.

Step 4 cites the statement of lem-weil-pbc-site-flat-quotient-tensor-ses: 'If G is also flat, then F is flat.' Its required exact sequence was proved in step 3; G=K^a and H=N are flat by the two separate assumptions. The zero-sheaf flatness observation is a direct application of the exact tensor-functor definition in def-pc-flat-sheaf-modules. This yields flatness of every term of P and L from their actual term lists. I declare the off-unit sheaf lemma as a generic tool in split_report.tool_uses; the Kunneth unit has no independent replacement for this input.

Step 5 uses exactly clause (1) of lem-kun-kflat-criteria, whose coefficient category, chosen universe and direct-sum total tensor convention agree with this item. The bound is a, because all L^i with i>a are zero. There is no lower-bound assumption on L, and no appeal to the cone or filtered-colimit clauses of that node.

I checked every cited excerpt in citations.json against its statement; none quotes a proof or a definition for a missing non-elementary theorem. The three elementary steps are the written quotient and kernel calculations, not renamed clauses handed to fresh nodes. The two non-elementary facts are existing cited theorems. Every step is shorter than 2000 characters. No new statements, definition data, unexplained existence choices, SGA references, compiler actions or repository changes are introduced.

Small-case checks: the zero complex and the empty site give zero P and L and satisfy all assertions. For a complex concentrated in degree a with flat term, q is the identity and L=0; for a complex concentrated above a the retained complex again gives q the identity. For the contractible complex [F --1--> F] in degrees a-1,a with F flat, N=0, P=0 and L=K, so the kernel is correctly bounded above, not necessarily zero. Conversely a nonzero flat sheaf concentrated in degree a-1 violates the cohomology hypothesis and its map to P=0 is not a quasi-isomorphism, confirming that assumption is used. Multiplication by 2 from Z to Z in degrees a-1,a over a point gives N=Z/2, which is not flat; it fails the flat-cokernel hypothesis and therefore does not contradict the conclusion that P has flat terms. Arbitrarily high positive terms of K are allowed: L still vanishes above a.

## Unfinished work

None in this stage-1 split. The already-existing auxiliary theorem nodes retain their own status; this delivery does not edit them.

## Dry-run repairs

The first dry run required the flat-kernel citation excerpt to be at least 40 characters. Replaced that short final sentence by the entire statement, including the small-site, exactness and flat-quotient hypotheses. No mathematical change.
