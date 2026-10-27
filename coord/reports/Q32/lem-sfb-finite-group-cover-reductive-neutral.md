# Q32 stage-1 report: lem-sfb-finite-group-cover-reductive-neutral

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-group-cover-reductive-neutral.json`: statement node, now split in seven steps; no Mathlib match. Statement and statement dependencies unchanged.
- `citations.json`: one verbatim statement quotation for each step/node citation (23 entries).
- `searches.jsonl`: five actual msearch results for this item, read before recording the verdicts.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches of the project `lean/WeilConjectures/` for the exact blueprint tag and for reductive/finite-group-cover notions found only unrelated Lie-algebra statements. They do not state the item. The Mathlib hit `AlgebraicGeometry.isIso_of_isClosedImmersion_of_surjective` is an auxiliary closed-immersion fact, not an attachment for the item.

## WANTED

WANTED: `literature/prasad-yu-on-quasi-reductive-group-schemes.pdf`, Proposition 4.3, first paragraph of proof, printed p.8, for this item. I read that paragraph online at https://arxiv.org/pdf/math/0405381. The local literature directory contains citation lists/import tools and the Stacks source, but this PDF is absent. The proof is marked agent-written: it expands the finite-kernel argument using existing DAG statements. It does not use the subsequent reductive-model result in that paragraph.

WANTED: `literature/milne-algebraic-groups_iAG2017.pdf`, Theorem 5.39 and Corollary 14.7, for the sources of the existing homomorphism-factorization and unipotent-image tools. Their complete DAG statements, rather than any unquoted details of their proofs, are used here.

## Existing material and route

I read the item, its parent quasi-reductive-special-connectedness statement and proof, the chapter/unit records, the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`, and its direct-images proof. This is the Prasad-Yu finite special-fibre-cover prerequisite already selected in the parent's proof, within the inherited alteration/moduli supporting chain. No unit or chapter route changes. The item's pre-existing `blueprint.from.node` is null, as the ancestor command confirms; its detailed nonempty place and via chain are preserved. The main det-thm-sf-ctf-stability-direct-images ancestor is described in `split_report.blueprint`, without inventing a different imported id.

Whole-DAG statement/title searches located the existing component, translate, closed-image, reduced-source-factorization, homomorphism-factorization, normal-unipotent-image and Artinian-product tools. Whole-blueprint searches for finite group cover, unipotent image, reductivity and identity component found no equivalent statement: the matrix-group component-coset lemmas have different scope and the Lie-algebra reductivity material does not concern finite algebraic-group covers. `same_as` is empty.

## Mathlib searches

I ran the msearch commands for leanfinder, leansearch, loogle and grep, and a second leanfinder phrasing concerning invariance under inseparable isogenies. All services answered. I read the returned signatures. Abstract finite groups, finite algebra homomorphisms, formal smoothness, and characteristic-zero Lie-algebra radicals do not imply this finite-type group-scheme assertion. Grep for reductive/isogeny/unipotent in AlgebraicGeometry/Group and Loogle for IsReductive gave no hits. The useful closed-immersion isomorphism hit is handled with the existing reduced-source-factorization lemma and an explicit section/monomorphism argument; it does not justify declaring this item a Mathlib leaf. Prior searches on the item are retained unchanged; only the five logged Q32 searches are appended.

## Problems corrected

The original item was statement-only, not a disputed statement. The statement is retained, including possible nonreduced target and inseparable finite kernels. I supplied the missing component-surjectivity argument and did not replace it with an assumed surjection on neutral components. I also checked the difference between geometric faithful flatness in the homomorphism-factorization statement and the extension-of-scalars formulation in the normal-unipotent-image statement. This required adding the existing affine-flatness criterion and flat-plus-surjective-spectrum criterion explicitly to step 4. The Artinian source label was checked against the local Stacks source: it is 00J6, lemma-finite-dimensional-algebra.

## Not duplicates

No new nodes. Every auxiliary non-elementary fact is an existing cited statement; the finite-module quotient, finite closed cover, monomorphism, descending-subspace and connected-product arguments remain proof steps.

## Review by Q32

For the item I read Prasad-Yu Proposition 4.3's first proof paragraph online. Its obstruction is a positive-dimensional normal unipotent subgroup in the kernel. Here finiteness allows a direct coordinate-algebra proof of triviality and requires no separability assumption. I read the local Stacks statements and arguments at groupoids 0B7R and 047R, with 047N/047P for the smooth reduced identity group, morphisms 01WN for finite closed images, and algebra 00J6, 00J7, 00JB for the finite reduced algebra endgame. No new-node source review is needed, since no new node is created.

Step 1 uses the actual statement of locally-algebraic-group-identity-component, which provides openness/closedness, geometric irreducibility, finite type and the reduced identity subgroup, all over an algebraically closed field as here. It applies to both U and V because both are of finite type. I checked the equality of the reduction of V's open identity component and the identity component of V_red on local rings. Closed-immersion's affine-quotient clause supplies affineness. The smooth-open-restriction statement gives smoothness of G from U, and smooth-geometrically-reduced gives reducedness. There is no smoothness assertion about V or its kernel.

Step 2 uses reduced-source-factors-through-closed-subscheme with source G, already reduced, and closed target H in V. This is precisely the extra hypothesis that makes set-theoretic containment suffice; it would be false for an arbitrary nonreduced source. Closed-immersion's quotient-ring clause supplies the coordinate quotients and monomorphism. The finite-module generators pass to B/J and to the acting quotient R/I, so this argument proves actual finiteness of the restriction.

Step 3 uses group-neutral-component-translates exactly for its finite list of translates by F-points. Finite-closed-map-finite-fibres is used only for closedness of q's images of the closed components. Reduced-source-factorization applies to Spec F when a translating point lands in V's neutral component. A connected image meeting a component lies in that component; the finite closed cover of irreducible H has a member equal to H, and inverse translation then makes f surjective. This uses neither smoothness of q nor an unjustified assumption that inverse images of connected sets are connected.

Step 4 checks both affine groups are separated using affine-source-morphism-separated before using the complete homomorphism-factorization statement. Its map j is closed and surjective, while H is reduced from step 1. Reduced-source-factorization applied to id_H provides a section; the closed-immersion quotient criterion proves that j is monic, hence an isomorphism. The affine flatness statement and flat-surjective-spectrum statement explicitly turn geometric faithful flatness into the coordinate-module version needed next, including for u in step 5.

Step 5 starts with an arbitrary smooth connected normal unipotent closed subgroup N of G; no existence or maximality theorem for the unipotent radical is assumed. Its affine finite-type and separated hypotheses follow from closed-immersion quotients and the separatedness tool. The homomorphism-factorization statement supplies exactly the factorization required by unipotent-normal-quotient-image. I checked both faithful-flatness hypotheses, the finite-type affine image, the closed immersion, and normality in the source. That cited lemma concludes smoothness, connectedness, unipotence and target normality, so reductivity of H kills the entire scheme-theoretic image J. This proves constancy on schemes, not just rational points.

Step 6 uses closed-immersion's actual affine quotient description, smooth-geometrically-reduced for N, and reduced-scheme's equivalence with reduced global sections. Once C acts on E through the identity C to F, the finite C-module generators become a finite F-spanning set. The Artinian assertion is proved by stabilization of dimensions of descending subspaces; it needs no additional structural theorem.

Step 7 uses exactly the full product-of-residue-fields assertion of reduced-artinian-residue-product. I verified its two hypotheses in step 6. Nonemptiness follows from the identity-point map, and connectedness excludes multiple field factors by their idempotents. The remaining field maps as an F-algebra to F, forcing it to equal F. Thus every candidate N is trivial and all clauses of reductivity from the unchanged statement hold. The coordinate-algebra endgame is written out instead of assuming finite connected group schemes are trivial.

Small cases checked: U=V=1; an arbitrary finite smooth disconnected group mapping to 1 (G is one identity point); a product of a reductive connected group with a finite constant group; Frobenius on G_m in characteristic p with kernel mu_p; and a smooth reductive source times a finite constant group mapping to a nonreduced target via the reduced subgroup. The last example is allowed because only surjectivity on underlying spaces was assumed, and the proof factors the smooth source through the reduction. Dropping smoothness would allow alpha_p to map to 1 with nontrivial connected source; step 6 correctly uses smoothness of N. No proof step exceeds 2000 characters. The B--E review found no new-node, duplicate, clause-restatement or hidden-lemma problem after the faithful-flatness correction. All citations are verbatim statements in citations.json.

## Unfinished work

None for this one-level stage-1 split. Referenced existing nodes retain their own independent proof obligations. No Lean was written, no compiler or build tool was run, and no repository or launcher file was changed. Server dry-run validation and direct delivery follow this report.
