# Stage-1 delivery: lem-sfb-scheme-etale-tensor-hom-comparison

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-etale-tensor-hom-comparison.json: statement, split in seven steps; not a Mathlib leaf. The statement and its statement dependencies are unchanged.
- citations.json: one verbatim statement quotation for every step/node citation.
- report.md: this report. searches.jsonl contains actual Q08 searches; the item's pre-existing Q20 search records are retained.

No new nodes; no Mathlib leaves. A split does not require new nodes when all its prerequisites already exist. The finite-presentation argument stays in the proof rather than becoming two nodes restating the item's tensor and Hom clauses. Local write/refinement scripts are sandbox scratch material only.

## Attachments

None. I searched the entire project WeilConjectures tree for the exact blueprint tag (no hit), and for tensor/Hom and etale comparisons. The close project declarations in AlgebraicGeometry/Sites/EtaleHom.lean (Modules.etaleHom, Modules.isSheaf_etaleHom), EtaleTensorHomEvaluationNaturality.lean, and ZariskiEtaleCore.lean give respectively a sheaf of morphisms between scheme pullbacks, an evaluation naturality statement, and a site comparison. None states both tensor and module-valued internal-Hom isomorphisms of this item. No sorry declaration was treated as a finished proof. Constant-coefficient etale/pro-etale comparisons have different coefficient sheaves.

## WANTED

None. All mathematical sources used are in literature/stacks-project. No SGA source was used.

## Source, blueprint and searches

I read descent.tex Tag 06VE (lemma-equivalence-quasi-coherent-limits), both the statements and the proof of (7),(8), and its warning/examples (6),(9). I read sites-modules.tex Tag 03EL (lemma-tensor-product-pullback), 0GMX (remark-pullback-internal-hom), 0GMY (lemma-internal-hom-exact) and 0GN2 (lemma-pullback-internal-hom), including the presentation/kernel proof. That proof has a harmless printed repeated n where the relation rank is m; the split consistently uses a relations and b generators. The Hom source is quasi-coherent by the already existing Zariski Hom-quasicoherence node. I also checked the kernel formulas in modules.tex 01CO/01CQ and the flat scheme-pullback source 0C6I.

The item was unsplit, with no repair note and no earlier sandbox node or report. I copied the live item and retained its provenance and prior searches. DAG searches covered the source labels, tags 06VE/0GN2/0GNA/03EL/0C6I, pullback, tensor and Hom keywords across all chapters. blueprint_refs.py searches included tensor Hom, 06VE, flat Hom, pullback internal, ringed tensor, flat pullback and Hom finite presentation; no blueprint node states this comparison. Relevant candidates were opened rather than used by title. In particular, the existing flat-ring Hom-base-change theorem is about rings, the etale restriction theorem concerns constant coefficients, and the isomorphism inverse-image Hom theorem assumes a scheme isomorphism: none was silently substituted for a scheme structure-sheaf comparison.

I read the chapter and unit records and the current latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/{_section.md,sk-thm-sf-ctf-stability.proof.md}. The current unit uses perfect models, compactification and the existence theorem. The item's null blueprint ancestor and long inherited completion prerequisite chain are retained. This is a subordinate scheme-module calculation, not a change of the unit or chapter route. Generic off-unit prerequisites are listed in split_report.tool_uses with their roles.

Q08 ran leanfinder twice with different topology/association phrasings, leansearch on the flat finite-presentation Hom comparison, loogle on SheafOfModules and Hom, and two Mathlib greps. I read the returned hits and the source of SheafOfModules.pullback and its adjunction, QuasicoherentData presentations, the scheme Modules.Hom and pullback declarations, and PresheafOfModules.Hom. They give presentations or abstract pullback, not the topology comparison. The second semantic search's LightCondensed tensor/closed-category instances have constant coefficients on a different site. The genuine searches and their responses were appended verbatim as records; no search was invented and no unavailable service was recorded as a miss.

## What was wrong or corrected

No statement dispute or statement correction. The imported node had no proof. I supplied the argument without creating an equivalent clause as a new node. During self-review I added explicit finite-sum quasi-coherence and slice-exactness citations, corrected the internal-Hom exactness source tag to 0GMY, and separated the scheme-object restriction check from ordinary slice restriction: the cited equivalence alone does not state that scheme pullback preserves Hom. Step 7 derives that identification from flat exact pullback and the already cited finite-presentation kernel formula. It does not assume it for arbitrary scheme morphisms.

## Not duplicates

No new nodes. All supporting facts are existing DAG nodes; no duplicate comparison, generic Hom-kernel theorem or new definition was created.

## Review by Q08

I checked delivery-errors B to E against the node and the opened sources. The item introduces every object and retains all its original definition references. There is no new unsplit node with a proof hidden in its statement, no purported Mathlib leaf, and no change to coefficient category or hypotheses. The tensor theorem is applied to the actual ringed-site pullback epsilon^*, not to a bare equivalence of abstract categories.

Step 1 uses the comparison node's explicit tensor-pullback formula, the tensor-closure node's assertion of quasi-coherence, and the ringed-topos tensor theorem's natural isomorphism. Its direction is inverted to match this item. The scalar-balanced formulas exhibit the local section rule; they are formulas for the known comparison, not a new existence theorem. The definition of sheaf tensor explains passage to sheafification. I checked the module universe against the small-site requirement.

Step 2 uses the actual sheaf-Hom quasicoherence statement with the finite-presentation hypothesis on M and quasicoherence of N. Tensor and Hom definitions give evaluation and the slice-by-slice transformation explicitly. Currying here is written as h mapping to (m mapping to ev(h,m)) on each further object; no unmentioned tensor-Hom adjunction lemma is needed. This also verifies which comparison map is being proved invertible.

Step 3 uses the precise finite-presentation Hom-kernel theorem, which states the matrix, the basis evaluation map, and exactness. The module adjunction and left-adjoint colimit theorem give the finite sums with their canonical injections, while the associated-module definition identifies the structure sheaf and coefficients. The coproduct-closure and image-quasicoherence nodes make every object of the kernel/image short exact sequence quasi-coherent. The existing small-etale exactness theorem applies to that sequence; the exact-functor theorem supplies kernel/mono preservation. This avoids assuming a left exact functor on the big etale site. All these facts are in the cited statements, not merely their proofs.

Step 4 uses slice restriction's explicitly stated preservation of finite colimits, so the restricted presentation is a cokernel. The abelian exact-epi/cokernel theorem supplies its universal property if expressed as an exact sequence. The Hom definition identifies the maps on the localized site, and the sectionwise-limits theorem identifies the resulting kernel as a sheaf kernel. The elementary argument itself constructs both directions: a tuple satisfying the relation equations defines a linear map from the free sheaf, which factors uniquely through the cokernel. It never assumes surjectivity of sections of a sheaf epimorphism. This routine universal-property computation is not a hidden internal-Hom base-change lemma.

Step 5 compares the actual evaluation arrow under the two kernels: both send h to its values on p(e_i). The etale composition/cancellation node states precisely the open immersion, composition and cancellation facts needed to identify slices and covers. The comparison equivalence gives restriction and its section normalization. The site and Hom definitions then make the restrictions the same actual maps. The sheaf gluing argument for local inverses uses uniqueness and no affine-overlap assumption.

Step 6 checks the naturality equations, rather than asserting that compatibility is automatic. Pure tensors give f(m) tensor g(n) along each tensor path; transformation evaluation gives g(h(f(m'))) along each Hom path. The localized tensor restriction node explicitly preserves pure-tensor sections. The Hom definition explicitly restricts transformations on further slice objects, so (h(m))|W = h|W(m|W) proves the restriction equation on all sections.

Step 7 checks the remaining scheme-object formulation. Composition/cancellation identifies the etale slice; the equivalence gives A_T(F)|U = A_U(u^*F). Finite presentation of u^*M and quasicoherence of the pulled-back modules follow from their cited statements without extra hypotheses. Etale flatness is part of the cited etale definition, so the flat pullback exactness theorem applies. Pulling back the finite kernel row and using the same cited Hom-kernel theorem gives u^*H = Hom(u^*M,u^*N), with the same evaluation coordinates. This is a short specialization/calculation from existing results, not a newly created node and not an assertion that all scheme pullbacks preserve internal Hom. Substitution in the previously proved slice square proves the full requested restriction compatibility.

Small cases: empty T has the unique module sheaves and the same formulas; a=0 gives Hom from a free module, b=0 gives the zero module and the empty tuple, and M=0 or N=0 gives the zero Hom/tensor. Identity etale restriction is the identity. A non-Noetherian scheme is allowed: only finite presentations, quasicoherence and etale flatness were used. No separation assumption entered, and no intersection of affine opens was declared affine. The distinction between small and big sites is essential: the source's Spec Z, Z/2, structure-sheaf example has zero Zariski Hom but nonzero big-site Hom at Spec F_2, so no big-site generalization is claimed. Finite presentation is used in the finite matrix/finite sum argument; no arbitrary infinite product is pulled through A.

Every proof dependency was opened and its complete statement copied verbatim into citations.json for the relevant step; the quotations are deliberately complete to retain the hypotheses. proof_deps is exactly the union of uses. Every proof step is below 2000 characters. The longer elementary steps are the explicit cokernel tuple calculation, the evaluation equations, and the short flat-pullback consequence of an already cited kernel theorem; none introduces an unproved subsidiary lemma. There are no new nodes needing separate small-case/source/search audits. Stage 1 only: no Lean file was written, no compiler/Lake/build tool was run, and no repository or launcher file was edited.

## Unfinished work

None in the one-level split. All future proof work belongs to existing prerequisite nodes. Maintainer independent review remains required.
