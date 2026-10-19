# Worker report

## Files written

- dag/nodes/sec-smooth-purity/lem-asd-supported-kummer-cartier-pullback.json: statement, split; no Mathlib match. Six proof steps replace the empty proof.
- citations.json: twelve verbatim statement quotations, one for each citation in each proof step.
- searches.jsonl: five actual Mathlib searches, retained as logged.

No new nodes and no Mathlib leaves. No unit record was changed: this auxiliary item is not the statement of sk-prop-sf-cbc. The repository and both Lean checkouts were only read; no Lean was written or compiled.

## Attachments

None for this item. The project source has the related sorry-free theorem `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.nonempty_pullback_dual_toModules_iso` in WeilConjectures/AlgebraicGeometry/EffectiveCartier.lean, lines 365–371. I read its signature and proof, and the preceding ideal-pullback and dual-pullback declarations. It asserts Nonempty of an underlying module isomorphism, with no condition on the canonical section or complement trivialization. It therefore covers only part of the present statement and is not an attachment. The exact blueprint tag search in WeilConjectures had no hit.

## Literature needed

None. Stacks divisors.tex, Tag 0C4U (lemma-pullback-effective-Cartier-divisors), and the definition-invertible-sheaf-effective-Cartier-divisor were read in the local literature. The former says that the line bundle and canonical section pull back, with proof explicitly omitted. I supplied the local-coordinate argument and marked proof_origin.by as agent. I also read schemes.tex, Tag 01JU (lemma-fibre-product-immersion), and sheaves.tex, Tag 04TN (lemma-glue-maps), and the pullback tensor formula at Tag 0095 (definition-pushforward). No SGA source is used.

## Findings and changes

The item statement agrees with Tag 0C4U, including the requirement that the scheme-theoretic inverse image is effective Cartier. It is unchanged. The complement-trivialization clause is the direct consequence of preserving the canonical section, which is a basis off the divisor. The original proof was empty. The new proof does not assume flatness and does not invoke the existing flat-pullback theorem outside its hypotheses.

The current blueprint's lem-amb-cartier-kummer-map.proof.md, final paragraph, requires pullback of the pair and its trivialized line bundle. The ancestor thm-asd-smooth-tensor has a different local-adjunction proof in main-20261015, but the historical ancestry of this created auxiliary node is preserved. This delivery supplies precisely the Cartier-pair input of lem-asd-ordinary-supported-kummer, rather than changing any chapter or unit route.

DAG searches included Tag 0C4U, Cartier/pullback, dual/pullback, and gluing modules, inspecting the actual statements of all candidates used. Whole-blueprint searches with tools/blueprint_refs.py covered `Cartier pullback`, `canonical section`, and `divisor`, and ancestor lookup returned thm-asd-smooth-tensor. No blueprint node states the present full claim. lem-pc-recd-pullback imposes relative Cartier hypotheses; lem-pc-divisor-line-bundle-properties and its flat-pullback children impose flatness; these do not prove the current arbitrary Cartier-preserving pullback assertion. Reused lem-pc-closed-subscheme-base-change-ideal-image for the image ideal and lem-weil-pbc-glue-sheaves-of-modules for gluing maps. Their dependency closures do not reach the item. Both generic tools are declared in split_report.tool_uses for the maintainer's route review.

Five Mathlib searches were run through msearch.py and their hits read: LeanSearch, Loogle, grep in AlgebraicGeometry, and two different LeanFinder phrasings. The first semantic search returns IdealSheafData.comapIso and its projection identities; the second returns fractional-ideal duality over Dedekind domains. LeanSearch returns generic bundle pullback and Scheme.Modules.pullback as well as comapIso. None states this line-bundle comparison with canonical section. Mathlib's IdealSheaf/Functorial.lean and Modules/Sheaf.lean were opened to distinguish the actual ideal-comap and module-pullback interfaces from the full claim. The original inherited search entries are retained, and the actual searches of this worker are appended; the inherited second LeanFinder verdict's phrase about an etale comparison is unrelated wording, not used as evidence. No new node relies on inherited search provenance.

## Not duplicates

No new nodes. Existing relative and flat Cartier-pullback nodes were not cloned; their extra hypotheses exclude their use here. The item itself already exists and is the assigned auxiliary statement.

## Review by NS

I checked B through E of delivery-errors.md against the open node files and the Stacks sources. There are no new nodes whose statement, provenance, or proof needs a separate audit. The item retains all imported fields, its original statement and statement dependencies, and its historical blueprint ancestry. Each non-elementary step is under 2000 characters (the largest step is under 900); no long step hides a new comparison lemma.

Step 1 uses the precise local regular-generator condition in def-nagata-effective-cartier-ideal and the equality O(D)=Hom(I_D,O) in def-pc-divisor-line-bundle. Multiplication by a regular generator has the explicit inverse af -> a, so the dual basis and the expression f e for the canonical section are a basis calculation. I checked the canonical-section convention against the Stacks definition: it corresponds to the ideal inclusion, so its coefficient is f, not 1 in the dual frame.

Step 2 uses the tensor definition in def-pc-module-pullback and the actual structure-sheaf isomorphism in lem-weil-pbc-module-pullback-structure-sheaf. The coefficient maps and their inverses are written down, rather than assuming a general theorem that duality commutes with pullback. Crucially lem-pc-closed-subscheme-base-change-ideal-image states exactly that the ideal of the fibre-product closed immersion is the image of the pulled-back ideal inclusion followed by that structure-sheaf map. Its hypotheses are a closed immersion and an arbitrary scheme map, both available; no flatness is required. This gives the genuine ideal (g), not just a set-theoretic inverse image.

Step 3 uses only the two definition statements of step 1. I checked the subtle hypothesis: an arbitrary image of a regular element need not remain regular. Here the second Cartier hypothesis gives a local regular generator a of the image ideal, and g=ua, a=vg implies vu=1 by cancellation of a. Thus g is regular and really is a basis of the ideal. The local expressions are taken after refinement when necessary; the unique coefficient inverses agree and give the basis on V_i. This small calculation is elementary and should not be a new DAG node.

Step 4 uses the definitions of the dual line and tensor pullback, and writes the change of basis explicitly. If f_i=u_ij f_j, then the dual basis changes by u_ij^{-1}, on both sides. This inverse is necessary. The chosen local maps and inverse maps agree on overlaps, so the argument does not conceal a theorem about a canonical unspecified isomorphism.

Step 5 cites only clause (1) of lem-weil-pbc-glue-sheaves-of-modules: its statement gives existence and uniqueness of a map between existing global O-modules from agreeing local maps. That is exactly what is applied, separately to the local maps and inverses. The identity composites and independence of all local equations follow by the same stated uniqueness. No object gluing, derived gluing, or affine-overlap hypothesis is used. I read the corresponding Tag 04TN proof, whose module version checks linearity locally.

Step 6 uses only the two definitions stated in its uses list and the explicit maps already constructed. It computes theta(g E)=g e', not merely an assertion of naturality. Sheaf separation gives equality of global sections. On the complement the coefficient g is invertible, so the two trivializations by the preserved canonical section agree. This also identifies the complement with the inverse image of T-D by the local principal ideal calculation. There is no extra theorem being imported from the proof rather than the statement of a dependency. Every citation has an exact quote in citations.json.

For edge cases I checked D empty (local equation 1, the unit line and its unit section), T' empty (all maps and gluing conditions are unique), opens disjoint from D (any local equation is a unit), and nonflat maps preserving Cartier divisors. For instance Z[t] -> F_p[t] is nonflat and the divisor (t) remains Cartier; the basis calculation still gives the claimed section-preserving isomorphism. The excluded map k[t] -> k sending t to 0 makes (t) pull back to the whole scheme with zero ideal; the cancellation argument correctly fails because this inverse image is not Cartier on a nonempty scheme. Schemes need not be reduced, Noetherian, or quasi-separated; no step assumes these properties or that intersections of affine opens are affine.

No statement dispute was found. The corrections made during self-review were to avoid applying a flat-pullback result to arbitrary h, to prove the pulled-back equation regular rather than assume it, and to make both the inverse transition factor and the actual canonical-section calculation explicit. The former upstream nonempty-isomorphism result remains only a partial match.

## Unfinished work

None in the mathematical split. Server dry run and direct delivery are performed after this report is written.
