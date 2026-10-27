# Worker report: lem-trf-finite-ideal-twist-cohomology-comparison

## Files written

- dag/nodes/sec-trace-formula/lem-trf-finite-ideal-twist-cohomology-comparison.json: existing statement, now split into seven steps; full statement retained; Mathlib searches find no match for the whole assertion.
- citations.json: nineteen exact statement quotations supporting the seven proof steps.
- searches.jsonl: five searches actually run with the prescribed command; their results were read and appended to the item's earlier search history.
- report.md: this report. write_split.py is sandbox-only preparation material.

No new nodes and no Mathlib leaves were created.

## Attachments

None for the whole item. Searching the blueprint tag and the notions in lean/WeilConjectures found existing partial ingredients, not a declaration stating all clauses. In particular, FiniteAffinePushforwardIdealDevissage.lean assumes the source affine and proves an ideal-devissage/degree-one vanishing assertion; it does not give the arbitrary finite-morphism, all-degree, all-twist statement. Modules/ProjectionFormula.lean:314 proves the ordinary projection formula for every morphism and its section formula occurs at line 278, but the DAG node to which it is attached, lem-pc-closed-immersion-coherent-cohomology, states that clause only for closed immersions. I therefore did not cite that node for a finite morphism. The item proves the elementary rank-one local argument itself.

## WANTED

None. All mathematical sources used are already present in literature/stacks-project/. coord/dag-sync.md, mentioned by the historical standing brief, is absent in this read clone; the current direct-delivery brief supplies the applicable shared-repository rules.

## Corrections and scope

The imported statement is true with its given hypotheses and is unchanged. Its proof was empty. A false possible shortcut would treat f^*J as a subsheaf of O_Y, or treat an arbitrary finite morphism as a closed immersion. Neither is used: H remains the image of the multiplication map throughout. Local Noetherianity is used separately on Y for coherence of its quasi-coherent submodule H and on X for finite-pushforward coherence. Surjectivity, ampleness, properness, and global quasi-compactness play no role.

The current blueprint is literature/blueprint/latest/ (COMMITS.txt ends at snapshot main-20261023-1620, 7284bb09daf97437d544c51882b325f9c52cd345). I read the chapter and unit records and the current sk-i-curve-zero/lem-trf-local-term-locality.proof.md. The latter retains the contracting-correspondence route; the finite ampleness calculation is a supporting subargument recorded in the created-item ancestry, not a replacement of the local-term route. The ancestor command confirms lem-trf-local-term-locality. Searches of all imported blueprint nodes for ideal/cohomology, affine/cohomology, projection, and finite/coherent found no node stating this whole result. DAG searches by 01YP, 089W, 01E8 and by the notions found the reusable ingredients cited below. No source forbidden by the route lock was used.

## Review by Q76

I read coherent.tex Tag 0B5V (lemma-surjective-finite-morphism-ample), especially the ideal-product paragraph and the displayed three-line cohomology calculation. That calculation uses only the finite/affine nature of the map for this subargument; its ambient surjectivity and ampleness assumptions are not needed for any isomorphism here. I also read coherent.tex Tag 01YP, including its explanation of the image and the affine equality I(M_A)=((IB)M)_A; Tag 01Y1, the quasi-coherent-submodule coherence statement; Tag 01Y6 via the existing finite-pushforward node and its source proof; and Tag 089W, whose proof uses affine vanishing and Leray. I read cohomology.tex Tag 01E8 and expanded its omitted degree-zero rank-one local argument. I read modules.tex Tags 01CD, 0B8L, 01CT and the tensor-power definition, schemes.tex Tag 01I8 and Section 01LA on tensor products, and cohomology.tex Tag 01F8 on coefficient functoriality.

For Step 1 I opened all four cited statements. The definition of finite explicitly includes affine. The finite-pushforward node gives coherence of G under local Noetherianity of X. The coherent-finite-type criterion gives quasi-coherence of F under local Noetherianity of Y. The affine ideal-product node explicitly includes both quasi-coherence of H and equality as submodules, so it supplies exactly the assertions used, not merely an unrelated projection formula. In Step 2 I opened the coherent-kernel-cokernel-locnoeth statement: its clause (2) allows a quasi-coherent submodule of a coherent sheaf, so it applies to H inside F. The finite-pushforward statement then applies to H and yields coherence of JG via the equality already established.

For Step 3 the invertible pullback/tensor statement explicitly gives preservation of invertibility, the natural tensor comparison, and the section formula. The definition of an invertible module makes the tensor unit the base case; the separately cited structure-sheaf pullback node gives the actual isomorphism at n=0. The induction specifies c_0 and c_(n+1), so it does not assume the desired power comparison. Step 4 uses only local rank-one trivializations and the sheaf tensor definition: tensoring is the identity locally, and equality of kernels and local images on a cover proves exactness. This is an elementary step, rather than a new exactness lemma.

Step 5 uses precisely the definitions of invertibility, tensor sheafification, and module pullback. The bilinear section map h tensor s maps to h tensor f^*s and respects restrictions; sheafification gives the sheaf morphism. On a trivializing open it becomes the identity in the two generator coordinates. On overlaps e'=ae changes both coordinates by the same unit, so the inverses glue. Thus the step supplies the omitted argument and the precise map, with no general projection-formula theorem silently imported. Its length is below 2000 characters and it contains no independent subclaim requiring a new node.

In Step 6 I used the general quasi-coherent tensor-product node, whose statement explicitly supplies quasi-coherence for any two quasi-coherent modules. It applies to H and the invertible tensor power of f^*L; the definition of invertibility supplies quasi-coherence of the latter. I did not introduce a duplicate lemma for a line-bundle twist. For Step 7 I opened the canonical affine edge node: it names exactly e_(f,M), not just an unspecified isomorphism of groups. Its hypotheses hold by Steps 1 and 6. The cohomology-definition node supplies the functor H^p; the fmap-functorial node explicitly gives the coefficient-composition identity. I corrected the draft naturality equation to use the induced map w:JG -> JG' on the image submodules, rather than a map on J tensor G. The equation is now derived from v_0(af)=a v_0(f), then the projection's section formula, then the cited edge naturality. Every proof citation has a verbatim full-statement quotation in citations.json.

I checked n=0 (unit comparisons and no positive-power convention needed), p=0 (the edge map is the same map on global sections), J=0 and J=O_X, F=0, the empty source, and the identity finite morphism. I also checked a nonflat closed immersion A -> A/I: the multiplication-image definition of H remains valid although pullback of the ideal inclusion can fail to be injective. For a finite non-surjective morphism, nothing in the proof uses points outside its image. Non-quasi-compact locally Noetherian schemes are allowed, since all coherence and generator arguments are local and the affine edge theorem imposes no global quasi-compactness assumption.

All existing cited nodes are definitions or are recorded Lean-closed, so no off-unit open tool citation is needed. The statement dependencies were retained, no maintainer field was edited, and no Lean or compiler operation was performed. No new-node statement, duplicate, Mathlib-leaf, or unsplit-proof issue arises; every non-elementary step names its ingredients, and the two elementary steps write their full local arguments. No step exceeds 2000 characters.

## Not duplicates

No new nodes: all matching existing facts were reused.

## Unfinished work

None in the one-level split. Deeper proofs remain owned by their existing nodes. The required server dry run and direct push are performed after preparing this report.

## Validation

The first complete server dry run passed at 35c9d7b65eb. The delivery command recorded a durable successful receipt; this report-only update is revalidated by the final dry run before pushing.
