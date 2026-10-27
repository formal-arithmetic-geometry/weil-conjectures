# Stage-1 delivery: lem-sfb-relative-pseudocoherent-pullback

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-pseudocoherent-pullback.json`: item, statement unchanged, six proof steps, status split; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-closed-immersion-unbounded-projection-formula.json`: new statement-only lemma, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-closed-pushforward-nonpositive-free-tensor.json`: new statement-only lemma, unsplit; no Mathlib match.
- `citations.json`: one entry per step citation, with the verbatim statement of the cited node, including all hypotheses.

Two new nodes, zero Mathlib leaves. All writes are in the assigned sandbox. No Lean, compiler, Lake, local DAG preflight, or repository git operation was used.

## Attachments

None. I searched the live `lean/WeilConjectures/` by the exact blueprint tag and the relative-pseudo-coherence notion. There is no declaration of this theorem. Existing module pullback functors, ring-level pseudo-coherence lemmas and coefficient projection formulas do not state the item.

## WANTED

None. The Stacks sources and the current latest blueprint were available locally.

## Findings and corrections

The item has no proof in the live repository, and the sandbox had no prior item or report. Its statement agrees with Stacks more-morphisms.tex, Tag 09US, `lemma-pull-relative-pseudo-coherent`. In particular it does not assume quasi-coherent cohomology or global boundedness. No statement correction was needed.

I read the current latest blueprint's unit and its direct-images statement and proof under `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`. The inherited support chain starts at direct-image clause (3); the current blueprint does not itself state this auxiliary relative-pseudo-coherence theorem. The ancestor search returns None. I retained the inherited null ancestor and detailed place, and extended its via chain for the new nodes. This changes no chapter or unit route.

The source's omitted nonpositive finite-free-resolution argument is supplied by existing nodes, not renamed as a new lemma. Only the unbounded closed projection formula and the closed-pushforward tensor-filtration assertion need new nodes. These are smaller independent tools: neither restates relative preservation by a morphism.

## Source error

Tag 09US, lines 17217–17220 of the available more-morphisms.tex, says the pieces with q very negative have zero cohomology in degrees less than or equal to m. This is the wrong direction. With Q=O[0] and q=-10 the piece Q[-q] is concentrated in degree -10, so for m=0 its cohomology certainly need not vanish in degrees at most m. The useful assertion is vanishing in degrees at least m once the tail is far enough to the left. The occurrences of A_Y^n instead of A_Y^d and A_S^{n+m} instead of A_S^{n+d} in that proof are also dimension-letter slips; the delivery consistently uses P=A_Y^d and W=A_S^{n+d}.

The phrase reducing to all pieces being pseudo-coherent must be read at the fixed degree m: the hypothesis supplies m-pseudo-coherence, and nonpositive resolution degrees shift that cutoff to m+q, which is at most m. Full pseudo-coherence of K is not available. These are proof-text errors, not a false item statement, so there is no STATEMENT-DISPUTED change to the statement.

## Argument retained for the new tensor lemma

Read Tag 09US's total tensor/filtration argument together with the definition of m-pseudo-coherence (cohomology.tex Tag 08CB) and its triangle closure (lemma-cone-pseudo-coherent). Here is the corrected argument for the statement-only node. On the affine target W, finitely many strictly perfect local approximations to Rj_*Q give one upper cohomological bound a. Closed pushforward is exact and detects zero sheaves, so Q has the same upper bound. Choose a representative E of Q with E^i=0 for i>a. The nonpositive finite free complex F is K-flat, so Tot(E tensor F) computes Q tensor^L F.

Choose N<=0 with a+N-1<m. The subcomplex F^{>=N} is the brutal upper truncation; its inclusion in F has quotient supported in degrees <=N-1. Thus Tot(E tensor (F/F^{>=N})) has no terms in degrees >=m. After exact j_*, the inclusion of the finite truncated tensor into the full tensor induces isomorphisms above m and a surjection at m (indeed an isomorphism there with this strict bound). The finite truncated tensor has a finite filtration with quotients Q^{r_q}[-q], N<=q<=0. Finite sums of the given local approximations show Rj_*Q^{r_q} is m-pseudo-coherent. Shifting these approximations by [-q] makes the cutoff m+q<=m; hence each shifted quotient is m-pseudo-coherent. Triangle closure gives m-pseudo-coherence of the finite truncated tensor. Composing its local strictly perfect approximations with the inclusion proves the claim for the full tensor. There is no infinite-extension or unproved convergence assertion in this argument, and no quasi-coherence of E is used.

## Not duplicates

lem-sfb-closed-pushforward-nonpositive-free-tensor vs lem-sfb-relative-pseudocoherent-pullback: both refer to Tag 09US, but the new lemma concerns an explicit nonpositive finite-free complex and absolute m-pseudo-coherence after a fixed closed pushforward; it neither mentions a base S nor asserts pullback along a relative pseudo-coherent morphism.

lem-sfb-closed-pushforward-nonpositive-free-tensor vs lem-sfb-space-inverse-module-polynomial-model: the latter's source mentions Tag 09US in a much larger inverse-limit argument, but its statement constructs polynomial-ring models of a specific derived inverse limit of base-flat modules; it says nothing about tensoring arbitrary non-quasi-coherent Q after a closed pushforward.

lem-sfb-closed-pushforward-nonpositive-free-tensor vs lem-trf-pseudocoherent-tensor-closure: the latter is a ring-level assertion in D(R); the new lemma is about arbitrary structure-module sheaves, whose cohomology need not be quasi-coherent and therefore cannot be moved to D(R) by the affine quasi-coherent equivalence.

lem-sfb-closed-immersion-unbounded-projection-formula vs lem-pc-projection-formula: the existing theorem assumes both objects have quasi-coherent cohomology. The new theorem permits arbitrary objects and uses the closed-immersion hypothesis to remove this restriction. No node with source Tag 0B55 or label lemma-projection-formula-closed-immersion was found.

Whole-DAG keyword and tag searches, and blueprint_refs searches for pseudo-coherence, closed-immersion projection formula, finite-free resolutions and tensor filtrations found no equivalent blueprint statement. The polynomial model, ring tensor closure, affine model and finite-free bound nodes were read before this decision. Search results in searches.jsonl were read, including the projective-resolution and finite-presentation hits; they do not assert the sheaf-level conclusions. Each new node records exactly queries actually run through msearch.py. The existing item's earlier Q57 searches remain intact and four new recorded searches have been appended.

## Review by Q70

I read Stacks 09US in full for the item, 0B55 and its exactness/K-flat proof for the projection-formula node, and 09US's final filtration paragraph for the tensor node. For the resolution I also read perfect.tex 08E7 and more-algebra.tex 064T/064U. I read the statements of every node cited by a proof step and copied their exact statements into citations.json; the following are the actual applications, rather than appeals to their proofs.

Step 1 uses the every-affine-chart criterion to restrict the two hypotheses, source locality to assemble the result, and derived pullback composition to identify the restriction. Affine base opens are allowed to vary and no intersection of affine opens is presumed affine. The affine triples cover the inverse image of each chosen affine base open, so their good embeddings give the defining covers over S.

Step 2 uses the affine-pairs criterion precisely for finite generation of A over R and B over A. The two surjections are written down, so the closed-immersion definition and affine-space definition give exactly i, j, p with h=pi. In particular j is a closed immersion, not an unspecified map into W. This is an elementary generator calculation, not a hidden factorization theorem.

Step 3 uses the every-chart criterion for all m on O_X, and the absolute all-degree characterization recorded in def-pur-pseudo-coherent-complex. Exactness comes from the new projection-formula node's explicit first clause. The quasi-coherence needed for the affine criterion is verified before applying it: the module is the associated sheaf of B, with sections B localized on each principal open. The existing bounded-free-model statement permits b=0 because B[0] has zero cohomology above zero. The affine equivalence then sends the free terms to free sheaves and preserves the derived isomorphism. No such claim is made for arbitrary K.

Step 4 uses polynomial-projection flatness on S'=A_S^d and then the flat-base-change statement with source Y, base S, base change S'->S and new source P. Its conclusion is relative to S', which is exactly the base for the polynomial chart j:P->A^n_{S'}. This is why the all-chart criterion applies. In particular I did not confuse relative-to-S' with relative-to-S, or use a quasi-coherent-only base-change theorem.

Step 5 applies the new projection formula with E=O_X[0] and Q=Lp^*K, followed by the tensor unit/symmetry and derived pullback composition. Its isomorphism is in the derived category, not merely per cohomological degree. The tensor lemma's affine, closed, fixed-degree and nonpositive-free hypotheses were all established in steps 2–4. Direct-image composition identifies the result with the pushforward along ji. No assertion of an arbitrary derived projection formula for a nonclosed morphism is used.

Step 6 uses only the defining relative criterion with the explicit composite polynomial surjection and the local assembly already justified. I checked that all non-elementary facts in these steps have cited statements, proof_deps is exactly their union, and no step exceeds 2000 characters. Generic off-unit tools are declared only in split_report.tool_uses; no tool_uses approval record was written.

Small cases checked: empty schemes, zero rings, n=0, d=0, K=0, F=0, F=O[0], and a single free term in degree q<0. The negative-degree test checks the sign m+q and exposes the source error. A complex with arbitrary non-quasi-coherent cohomology below m is permitted throughout; no affine-derived equivalence is applied to it. Infinite negative resolutions are permitted, and the finite-tail argument explains why no lower bound is required. New unsplit nodes have statements only, empty proof/proof_deps and null proof_origin. Definitions cited in them define precisely the displayed objects.

## Unfinished work

None for this one-level split. The two new statement-only nodes are the intentional downstream stage-1 items. No required source is missing and no mathematical obstruction remains.
