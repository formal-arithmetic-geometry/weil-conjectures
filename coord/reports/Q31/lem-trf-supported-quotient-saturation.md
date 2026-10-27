## Worker report

Files written:
- dag/nodes/sec-trace-formula/lem-trf-supported-quotient-saturation.json: existing statement, now split in four steps; not a Mathlib leaf.
- citations.json: verbatim statement quotation for the one dependency cited in step 1.
- report.md: report and direct-delivery review.

New nodes: 0. New Mathlib leaves: 0.

Attachments: none. Searched the live WeilConjectures source for the item id, supported-section and quotient terminology. SupportDimension constructs a supported-section subsheaf, but does not prove this quotient theorem. QuasiCoherentCokernelImage supplies the existing generic dependency, not an attachment of all clauses of the item. No compiler was run.

WANTED: none.

The item statement is unchanged and is true with precisely its existing hypotheses. The Stacks source gives the restriction kernel, while the no-residual-support clause is a consequence we must prove, not a clause to attribute to 07ZP. I supplied the missing argument explicitly. No existing proof was in the sandbox; the live item had empty proof and proof_deps. I preserved the live statement, source, creation record, blueprint ancestry, and previous Mathlib searches, and appended only the four searches actually run in this session.

Nothing remains unfinished in this one-level split.

## Sources and searches

Read properties.tex, Tag 07ZP, lemma-sections-supported-on-closed-subset, including the exact restriction-kernel sequence in the proof of (3); divisors.tex, Tag 080D, definition-strict-transform (1); and schemes.tex, Tags 01IB and 01IC, lemma-equivalence-quasi-coherent and lemma-kernel-cokernel-quasi-coherent. Verified these tag/label identifications against tags/tags. Read the current main-20261015 blueprint locality statement and proof, and the chapter/unit records sec-trace-formula and sk-i-curve-zero. The auxiliary node's inherited strict-transform/Orgogozo ancestry is retained; no chapter or unit route is changed.

Searched the whole DAG for 07ZP, 080D, quasi-coherent cokernel/image/quotient and affine exactness. Opened the actual statements of lem-weil-pbc-quasi-coherent-module-cokernel-image, lem-weil-pbc-quasi-coherent-module-cokernel-closure, lem-weil-pbc-quasicoherent-epi-affine-cover, lem-sc-picard-scalar-affine-sections-exact and lem-trf-affine-pushforward-quasi-coherent-quotient. The cokernel/image node already states exactly the general calculus needed; no duplicate or new clause-node was made. Blueprint searches for supported, cokernel, quasi-coherent cokernel and supported-section quotient found no blueprint statement of the full item. The ancestor command confirms lem-trf-local-term-locality.

Four logged msearch calls were read: LeanFinder for the kernel-of-open-restriction quotient; LeanSearch with a second wording about the supported-section quotient and its open restriction; Loogle for SheafOfModules/cokernel; grep for supported|saturat|cokernel in AlgebraicGeometry/Modules. The first hits are general local injectivity facts; the second are quasi-coherence constructors and open restriction; Loogle supplies presentations by free cokernels; grep finds Tilde.lean:452,460,462,477,478. I read Tilde.lean:440--485: these are tilde presentations and an isomorphism used to identify presentations, not this saturation theorem. No exact match or one-line specialization giving every clause was found. All recorded new query texts are verbatim from searches.jsonl; older records remain attributed to the previous live item.

## Tool use

lem-weil-pbc-quasi-coherent-module-cokernel-image is a generic algebraic-geometry tool from the proper-base-change unit, used without changing the trace-formula route. Its statement gives cokernel quasi-coherence, local-image kernel, the epimorphic projection, and affine section surjectivity for arbitrary quasi-coherent module morphisms. The local trace-formula unit has no competing general cokernel calculus statement. This use is declared in split_report.tool_uses for maintainer judgment; no maintainer-owned tool_uses field was written.

## Not duplicates

No new nodes were created. In particular the existing cokernel/image node is reused rather than duplicating its affine or quasi-coherence clauses.

## Review by Q31

I reviewed the written node against the local sources and delivery-errors B--E with its dependency open. Properties 07ZP assumes retrocompact complement to prove quasi-coherence of the supported subsheaf. Here quasi-coherence of K is already a hypothesis, so none of that extra assumption is needed or introduced. Divisors 080D supplies the intended quotient construction. Schemes 01IB/01IC support the general quasi-coherent cokernel calculus in the cited existing node. The saturation argument is explicitly agent-written, not misrepresented as a separate sentence in Stacks.

Step 1 uses only lem-weil-pbc-quasi-coherent-module-cokernel-image. I checked its statement clauses (1), (2), (3): they give ker(q) as the local-image subsheaf, q epi with q composed with the original map zero, quasi-coherence, and affine surjectivity. Both its inputs K and H are quasi-coherent by the item's hypotheses; Y is a scheme, and the map is their actual inclusion. Its statement has no compactness or finiteness requirement. I also read the corresponding live declaration and docstring in QuasiCoherentCokernelImage.lean to exclude confusing a different cokernel model with the stated one. This is a citation of the node's statement, not extraction of a claim hidden in its proof.

Step 2 uses step 1 and the definition K(W) = ker(H(W) -> H(W intersect V)). Local membership in K forces zero restriction on a cover of W intersect V; uniqueness for the sheaf H gives zero restriction globally. Conversely a member of K is already in the inclusion's image. This proves the claimed sectionwise kernel on every open, without assuming a sheaf epimorphism is sectionwise surjective. It is an elementary sheaf-uniqueness argument, so it creates no new lemma or citation.

Step 3 uses the kernel equality from step 2 and affine surjectivity from step 1. For every open T inside V, K(T) = 0, so the map is injective on every overlap, including overlaps that are not affine. Affine local lifts therefore glue uniquely. I wrote out both the gluing and naturality by uniqueness, obtaining the isomorphism on the whole restriction, rather than using an uncited restriction-preserves-cokernels theorem. All opens used for surjectivity are affine; no false assumption that intersections of affine opens are affine occurs.

Step 4 uses the preceding isomorphism only on U intersect V, and the preceding affine surjectivity only on affine U in W. The lift's restriction is zero because its quotient image is zero and the restricted projection is injective. Thus the lift is in K(U), hence its quotient section vanishes. Uniqueness glues zero sections on the affine cover. Finally injectivity on sections of Q -> j_*(Q|V) follows by applying this result to differences; the categorical monomorphism assertion is checked by cancellation of components. These are elementary applications of earlier steps and the sheaf axioms, not an unrecorded support or descent theorem.

For small cases: if V is empty, K = H and Q = 0; if V = Y, K = 0 and Q = H; if H = 0 or Y is empty every assertion holds. With Y = Spec Z, H = O_Y and V = D(2), K = 0 and sections restrict injectively, consistent with the saturation conclusion. On a non-quasi-compact W the same cover argument remains valid: no finite subcover or common annihilator is taken. I also checked that the generic step 1 tool has no dependency path back to this item, leaving no circular appeal to saturation. No new statement required an edge-case test, no new unsplit node contains a proof, and no step exceeds 2000 characters. The report and citations match the actual uses lists. The substantive correction to the initial empty proof is to distinguish affine local lifting from false global surjectivity on arbitrary opens.
