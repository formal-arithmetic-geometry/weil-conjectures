# Q63: lem-sp-completed-coefficient-regular-quotients

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-completed-coefficient-regular-quotients.json: statement, now split into seven steps; no exact Mathlib match.
- citations.json: one verbatim statement quotation for each node used in each step.
- report.md and searches.jsonl: review and actual Mathlib search log.

No new DAG nodes and no Mathlib leaves. The sandbox also contains the reproducible write_split.py helper. No repository, launcher or Lean file was changed; no compiler or Lake command was run.

## Attachments

None. Searches of lean/WeilConjectures by the item tag, completed coefficients, regularity and projection/kernel/quotient terminology did not find a complete declaration of the item. CompletedIntegral.lean constructs the coefficient sheaf and its actual projections, but does not state this whole package. The existing Sheaf declarations attached to the scalar-regularity and projection-divisibility nodes are used through those DAG statements; they do not supply an attachment for this item.

## WANTED

None newly needed. The standard local-field facts are existing cited nodes, rather than facts asserted here from an unavailable reference.

## Findings and changes

The statement is retained verbatim. The item had no proof. Its ancestor is sk-lem-sp-tower, via lem-sp-ell-coefficient-fiber, and its existing blueprint.from.place identifies the coefficient setup in the first paragraph. The split supplies that setup without changing the unit reconstruction route. The chapter and unit records were read and left alone.

Whole-DAG and whole-blueprint searches found existing lem-sp-completed-integral-projection-divisibility and lem-pod-completed-integral-scalar-regular. They are sufficient; creating new kernel or torsion-free nodes would duplicate them. The point-only principal-reduction nodes do not cover arbitrary T and were not used. Likewise def-weil-completed-integral-coefficients has a global finite-field convention; step 2 deliberately uses clause (3) of det-prop-sfb-qlbar-colimit-x-integral-limit, whose statement covers any scheme and finite E, together with the unrestricted tower definition. I checked the full dependency closures of the cited comparison, regularity, divisibility and sheafification tools; none reaches this item.

The arithmetic and sheafification lemmas are generic tools. They are declared in split_report.tool_uses, with their purpose and why the reconstruction unit does not replace them. The quotient inverse and epimorphism arguments are written directly; no new node merely renames a clause of the item.

## Mathlib searches

I retained the item's inherited search records and ran five fresh searches through the prescribed msearch.py command: LeanFinder with two different formulations, Loogle on AdicCompletion and quotient, grep for completedIntegral/uniformizer sheaf kernels/adicCompletion quotients, and LeanSearch on the completed coefficient sheaf and constant quotient. I read every returned hit. Ordinary adic-completion injectivity, ramification quotient inclusions, constant-sheaf criteria, free module sheaves and perfectoid BDeRham objects do not state this ring-sheaf projection package. In particular AdicCompletion.map_injective has finite-module and ordinary-completion hypotheses and gives no identification of the actual pro-etale projections. All services answered; none was recorded as unavailable. The exact queries and result summaries are appended to the item and preserved in searches.jsonl.

## Not duplicates

No new node is proposed. The existing generic regularity and divisibility nodes are cited rather than recreated. Blueprint searches for regular scalar powers and uniformizer-power inverse limits supplied no second blueprint statement of the whole item; same_as remains empty.

## Review by Q63

I read the item's statement, the coefficient-tower definition, its chapter and reconstruction unit, and the current main-20261015 sk-lem-sp-tower proof. The latter uses the coefficient quotient in its first paragraph and calls reduction a scalar cone; it does not itself prove the scalar calculation. I therefore mark this assembly proof as agent-written. I also read the integral-limit blueprint statement and Stacks sites.tex Tag 00WK (lemma-sections-sheafification) and Tag 00YR (section-sheaves-algebraic-structures, especially the underlying-set comparison). I read sites-modules.tex Tags 093J and 093M to check the source's constant-sheaf/completion background. Every cited DAG statement was opened in full. There are no new statement-only nodes needing a separate source review.

Step 1 uses def-weil-l-adic-numbers for the explicit norm of ell, lem-weil-l-adic-extension-integers-dvr for the extending norm, units and integer-exponent factorization, and lem-weil-valued-dvr-finite-quotients for finite positive quotients. All three statements say these facts. The positivity of e follows from norms, rather than assuming that an arbitrary nonzero coefficient element lies in the maximal ideal. The valued-DVR theorem's hypotheses hold for this O, with its specified absolute value, uniformizer and finite residue field. Equality of the two principal ideals, the cofinal inequalities and finiteness of the ell-quotients are then explicit consequences.

Step 2 uses integral-limit comparison clause (3), not its restricted finite-subextension sibling. That clause covers arbitrary T. def-pur-sheaf-inverse-limit explicitly includes ring sheaves and sectionwise coordinate projections. sk-def-sp-coefficient-towers identifies this actual coefficient ring with its ell-power tower and actual reduction maps. The cofinal comparison is written on compatible coordinates in both directions, so it neither interchanges sheafification with an infinite limit nor substitutes an arbitrary isomorphism for the actual projections. Constants are normalized by their quotient coordinates.

Step 3 invokes lem-pod-completed-integral-scalar-regular, whose statement explicitly quantifies over any scheme T, every pro-etale object U and every m>=0. This is exactly sectionwise injectivity of the constant uniformizer power. The named coefficient comparison in step 2 identifies its inverse-limit model and scalar with R; no characteristic restriction is imported from a convention.

Step 4 invokes lem-sp-completed-integral-projection-divisibility at n=j-1. Its statement gives a section y on the same U whenever the actual positive uniformizer projection vanishes. The index is legal because j>=1. The converse is reduction of pi^j to zero. Injectivity from step 3 shows that sectionwise images glue with unique preimages; thus they are already the ideal sheaf, rather than an unjustified equality between presheaf image sections and sheaf image sections.

Step 5 uses def-weil-pbc-constant-sheaf for the sheafification construction, lem-pe-ring-sheafification-underlying-sets for its natural underlying-set and unit comparison, and lem-weil-pbc-site-sheafification-sections-local for local constant representatives. These statements say precisely what is used. The small pro-etale site has the fiber products appearing in the local-section theorem; all site and value universes can be enlarged as that theorem requires. The sectionwise limit description gives a compatible constant lift of each representative in O. Right cancellation for ring-sheaf maps is then proved using these local lifts and the sheaf axiom, without a claim that arbitrary epimorphisms of rings are surjective.

Step 6 is a direct consequence of earlier steps: u^n is an invertible constant scalar, the ideals agree, and B_n=C_en under the identity on coefficient representatives. It proves ell injectivity, the exact kernel and epimorphism for the actual q_n. It uses no unrecorded flatness or inverse-limit exactness theorem.

Step 7 uses def-weil-pbc-algebra-hom-quotient for ordinary sectionwise quotients and their kernel, and the same underlying-set comparison and local-section theorem for ring sheafification and quotient representatives. The inverse is constructed by gluing local lift classes. Differences belong to the sectionwise ideal by steps 4 and 6, so the local classes agree; different choices give the same section. Ring operations and both inverse identities are checked on a common lifting cover. The transition square is checked on the same local classes and actual projections, not asserted by an unexplained transport. This is a routine sheaf-gluing argument, not an extracted hidden comparison lemma.

I checked B--E of delivery-errors.md: there are no new nodes, sources use the actual Stacks labels and tags where needed, each proof uses a cited statement rather than its proof, all citations have verbatim quotes, and all non-elementary inputs are cited. No step exceeds 2000 characters. There is no new lemma that is elementary, a duplicate or an item clause. No SGA source is used. The original statement is mathematically correct and needs no STATEMENT-DISPUTED repair.

Small cases: E=Q_ell gives e=1; a ramified extension gives ell^nR=pi^(en)R rather than pi^nR; j=n=1 keeps the divisibility index zero; j<e presents no indexing problem; T empty and empty site objects give singleton section rings and still satisfy injectivity and all identifications. Disconnected objects require only locally constant representatives, not a single global element of O. Arbitrary characteristic, non-Noetherian and non-quasicompact T do not enter any argument or cited hypothesis. In particular ell is never interpreted as a scalar in the scheme structure sheaf.

## Unfinished work

None in this one-level split. No new node needs later splitting. Existing dependencies retain their own independent status.
