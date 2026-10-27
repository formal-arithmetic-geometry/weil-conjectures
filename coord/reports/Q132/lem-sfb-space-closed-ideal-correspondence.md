# Q132: lem-sfb-space-closed-ideal-correspondence

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-closed-ideal-correspondence.json: statement item, split using existing nodes; no Mathlib match for algebraic spaces.
- citations.json: verbatim statement excerpts for every step/node citation, including the three distinct correspondence clauses used in step 1.
- searches.jsonl: actual search-command log. write_split.py is a sandbox-only reproducibility aid.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched the project's WeilConjectures source for the exact blueprint tag and for closed-ideal and algebraic-space concepts. The relevant existing project declarations concern schemes, not the full algebraic-space statement. Mathlib's AlgebraicGeometry.IsClosedImmersion.overEquivIdealSheafData, Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean:180, inspected at lines 175–190, also concerns schemes. Loogle, LeanSearch and two LeanFinder phrasings gave scheme-level results, not an exact match. The searches inherited from the live item were retained; the actual searches for this delivery were appended.

## WANTED

None.

## Corrections and route

No statement correction or dispute. The imported proof was empty. The DAG already contains lem-sfb-space-ideal-closed-subspace-correspondence, which supplies the correspondence, surjectivity/kernel, factorization criterion, and arbitrary inverse-image ideal. I cite that node rather than create a duplicate. The additional content here is the specified quotient-pullback isomorphism and its unit/composition compatibility, assembled through the small finite coequalizer. In particular, the argument does not tensor a short exact sequence and assume its injection remains injective.

I read the chapter and unit records, and the latest blueprint's sk-thm-sf-ctf-stability unit and direct-images proof (3). The item lies on the inherited Hilbert/Quot supporting chain for the alteration/moduli input; the latest blueprint has no separate identical lemma. blueprint_refs ancestor reports a null blueprint ancestor, as in the live item's existing provenance, and I retain that chain and its precise place. Whole-blueprint searches for closed immersion ideal, closed subspaces and quotient pullback found no separate identical imported theorem.

## Not duplicates

No new node was created. In particular the existing lem-sfb-space-ideal-closed-subspace-correspondence is cited for all of its overlapping clauses; it does not state the tensor-pullback quotient isomorphism or its coherence. lem-sfb-space-closed-immersion-quasi-coherent-modules concerns the exact fully faithful pushforward on modules annihilated by the ideal, and was read but is unnecessary here.

## Review by Q132

I read Stacks Tag 03MB (spaces-morphisms.tex, lemma-closed-immersion-ideals), its proof and the paragraph following definition-inverse-image-closed-subspace. This confirms arbitrary algebraic-space base changes, not just etale or flat ones. I also read categories.tex Tag 0038 (lemma-adjoint-exact), part (1) and its proof, and sites-modules.tex Tag 03D7 (lemma-adjoint-pullback-pushforward-modules) with the preceding tensor formula. These are the sources for the extra quotient argument. No new node requires another source.

For step 1 I opened the entire statement of lem-sfb-space-ideal-closed-subspace-correspondence. It explicitly gives the inclusion-reversing bijection, a surjective structure map with the prescribed kernel, and the image ideal after every algebraic-space base change. These are exactly the three facts used. The induced quotient isomorphism is justified by local lifts modulo that kernel. There is no appeal to an unrecorded construction from the cited node's proof.

For step 2 I opened def-trf-space-etale-module-functors: it defines the tensor pullback as left adjoint to the specified direct image, not just an unrelated inverse image of sheaves. I opened lem-weil-pbc-left-adjoint-preserves-colimits: its statement applies to a small indexing category and a colimit that exists. Here the diagram is the finite parallel pair consisting of the ideal inclusion and zero, whose coequalizer is the quotient already supplied in step 1. Thus smallness and existence are satisfied, without a hidden infinite-colimit assumption. The cited tensor definition is sheafification of the presheaf tensor, so the displayed multiplication and inverse maps define maps of sheaves. This gives the cokernel by the image ideal and does not require flatness. The colimit lemma is a Mathlib leaf and is used as a generic categorical tool, without changing the unit route.

For step 3 the tensor and functor definitions are the only external citations; the rest is uniqueness of the coequalizer already established in steps 1–2. I checked the tensor formula for the unit and multiplication, and wrote the successive-pullback formula explicitly. Every section of the quotient has local lifts, so equality on these tensors or after the epimorphic quotient proves equality of the sheaf maps. This is an elementary assembly of the preceding steps, not a separate base-change theorem hidden inline. Each step is under 1000 characters, so none conceals a long unexamined argument.

I tested the zero ideal (identity immersion), unit ideal (empty closed subspace), zero ring/empty scheme charts, and the nonflat affine example A=Z, I=(2), B=Z/2. The quotient formula B tensor_A (A/I)=B/IB holds in each case; in the nonflat case it deliberately makes no assertion that the pulled-back ideal inclusion remains monic. Repeated scalar extension sends c tensor (b tensor [a]) to [c r(b) (p r)(a)], so both quotient comparisons preserve the unit and agree, including empty charts. All hypotheses of each cited statement hold without finiteness, Noetherian, separation, or flatness assumptions. I checked for a dependency path back to the item in the cited nodes and found none. Every quote in citations.json was checked as a literal substring of the cited statement.

The B–E review found no extra definitions needed in new nodes (there are none), no clause moved into a new node, no unsupported locality/descent claim, and no source error. Only the item, report and citation/search support files were written in the authorized sandbox; no Lean was written and no compiler or git command was run.

## Unfinished work

None in this one-level split. The existing unsplit correspondence node remains its own future stage-1 item.
