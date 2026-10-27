## Worker report

Item: lem-sfb-ringed-global-hom-cup-comparison. Group Q22, 2026-10-23. Only stage 1; no Lean files, compilation, repository writes or direct git commands.

### Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-ringed-global-hom-cup-comparison.json: statement node, split; statement and statement dependencies retained. Eight proof steps, no new nodes and no Mathlib leaves.
- citations.json: one verbatim statement quotation for every citation in every proof step.
- report.md: this report. searches.jsonl contains the search command's original records. write_split.py is a sandbox-only reproduction script, not part of the delivery.

### Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and global Hom, cup/evaluation and shifted-unit concepts. MixedGlobalHomAdjunctionIso.lean constructs comparisons for scheme morphisms with quasi-coherent adjoints; GlobalHomShiftedHypercohomology.lean concerns schemes and shifted cohomology only. Neither states this arbitrary ringed-site comparison with all its clauses. The curve trace pairing specializes to H^1 and cannot attach this item.

### WANTED

None. The needed literature is present. The algebra calculation beyond Stacks' explicitly written construction is marked agent-written, using existing nodes with representative normalization.

### Corrections and scope

The live item had no proof, not a false statement. Its statement, source, statement dependencies and inherited blueprint provenance are retained. No STATEMENT-DISPUTED correction was necessary. The latest blueprint direct-image proof, paragraph (3), is contextual: it does not itself prove this general homological lemma. I read that current file, the unit and chapter records, and the inherited parent lem-sfb-space-affine-global-trace-adjunction. The split supplies the exact global Hom normalization requested by that parent; it does not alter the unit route or introduce a new coefficient category.

During review I considered lem-sfb-shifted-cup-adjunction-transpose, but its shifted formula only concerns two endomorphisms of the monoidal unit. It cannot justify the arbitrary internal-Hom evaluation pairing here. I discarded that citation before writing the delivered split. Instead steps 5–7 give the cocycle normalization and explicit adjunction equations. The earlier draft never changed the item file (its script failed before the write); an initial citations file was fully replaced by quotations copied verbatim from the actual cited statements.

### Searches and reuse

Read coord/delivery-errors.md B–E in full and the stage-1 brief. Searched the DAG for Tags 08JA, 0B6C, 0B6D, the global Hom and unit-normalization concepts; opened the relevant nodes, including lem-pur-rhom-global-sections, lem-pc-derived-tensor-hom-sections-unit, lem-pc-derived-pullback-evaluation-sections, lem-sc-global-hom-shifted-hypercohomology, lem-pur-global-hom-evaluation-model, lem-sfb-derived-internal-hom-sections-model and the existing tensor/unit/shift lemmas. The scheme-only nodes cannot be used at an arbitrary ringed site. The general sections model and canonical ringed tensor-Hom adjunction are reused directly. Blueprint searches for global Hom, 08JA, global cohomology, shifted unit, tensor unit, sections adjunction and hypercohomology did not identify a blueprint statement duplicating the complete item. The ancestor command reports blueprint.from.node = None; I preserved the item's inherited null ancestor and nonempty precise contextual place rather than inventing a blueprint ancestor.

All Mathlib searches were made with the required msearch.py and logged as produced; their hits were read. The searches found ordinary SheafOfModules.unitHomEquiv and its evaluation/naturality equations (Mathlib/Algebra/Category/ModuleCat/Sheaf.lean:178–191), ordinary sections adjunction (CategoryTheory/Sites/GlobalSections.lean:101–115), module pullback unit normalization (Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean:60–111), and HomComplex.CohomologyClass.toSmallShiftedHom (Algebra/Homology/DerivedCategory/SmallShiftedHom.lean:39–60). None is the complete unbounded cup/evaluation comparison with its shifted action. The ordinary closed comparison search found CategoryTheory.expComparison and closed-category adjunctions, not the requested derived normalization. Alternative phrasings were tried. There are no new nodes to search or distinguish by a shared source tag.

## Not duplicates

No new nodes. All general facts are existing nodes; no clause of the item was repackaged as a new node. The all-degree Hom identifications are specializations of lem-sfb-derived-internal-hom-sections-model, including its point-site specialization.

## Review by Q22

I read Stacks sites-cohomology.tex Tag 0B6C (remark-cup-product), Tag 0B6D (remark-projection-formula-for-internal-hom), Tag 08JA (lemma-section-RHom-over-U), and the Tag 08J9 (lemma-internal-hom) proof. I also read derived.tex lemma-derived-adjoint-functors and lemma-derived-shift. Tag 0B6C defines exactly the tensor-of-counits cup in this item; 0B6D defines exactly its evaluation transpose. Tag 08JA's proof chooses a K-flat first input and K-injective second input and computes global Hom. All sites are small in the specified module universe; no finiteness, boundedness or flatness of the structural ring map is added.

Step 1 uses lem-weil-pbc-pullback-tensor-canonical-shift-unit for precisely its tensor comparison, unit comparison, both tensor shift equations and action-unit equations. It uses lem-weil-pbc-derived-adjunction-shift for canonical K-flat/K-injective shift compatibility of the derived adjunction. Both statements apply to general ringed topoi presented by small sites, so the coefficient point is allowed. The shifted-unit comparison j_n and its compatibility equation are the specialization of these stated equations with the first tensor input A and then A[-n]. They are not inferred from a tensor isomorphism with no coherence.

Step 2 cites the Mathlib-leaf adjunction-of-natural-bijection statement for the explicit inverse transpose epsilon F(b). Closed-symmetric-monoidal gives evaluation, transposition and naturality in every variable; it applies both to the original site and to the coefficient point. I wrote the evaluation and pairing naturality equations for arbitrary r:L'→L and s:M→M', so naturality is checked with the correct variance.

Step 3 uses the sections model's statement, particularly its canonical global Hom complex and all-integer cohomology formula. Its one-object-site specialization is exactly ordinary A-module derived Hom. The module representability node states all integer degrees and its value-at-one cocycle formula. The A-action is the specified action on each Hom group, and the differential and every comparison are A-linear; taking underlying abelian groups does not change the cohomology groups claimed.

Step 4 checks the hypotheses separately: K-flat resolutions with flat terms exist for arbitrary source complexes, K-injective resolutions exist on a small ringed site, and the internal Hom from that K-flat source into that K-injective target is K-injective. Each is an explicitly cited statement. The sections model then gives the actual section Hom complex. I do not claim its section complex is K-injective over A, which is unnecessary and would be an unwarranted hypothesis for a nonflat structural map.

Step 5 uses resolving-derived-adjunction-normalization for the chain-level transpose on a resolving source and a K-injective target, with the ordinary module adjunction providing r→r phi. The source A[-n] is flat-term K-flat (a one-term free module); its pullback is O[-n]. The canonical ringed tensor-Hom adjunction explicitly asserts the componentwise uncurrying equation, not just existence of an adjunction. Applied to O[-n] and P, it says evaluation is z→phi(z). Since d_I phi=(-1)^n phi d_P, this is a chain map P[-n]→I with exactly the shifted differential; no interchange of the tensor factors introduces an extra sign. This identifies v with u[-n] under the source's canonical Hom-cocycle identification.

Step 6 is a direct substitution in the cup definition and counit naturality. Its only external algebra is the cited inverse-transpose formula; t's naturality and the cup counit equation were already established in steps 1–2. All domains were checked: both expanded arrows start at F(S tensor GL) and end at M.

Step 7 is a second explicit substitution. The shifted unit/coherence equation starts at F(GL[-n]) and ends at O[-n] tensor FGL. Naturality of its unitor carries epsilon_L to epsilon_L[-n]. The adjoint of G(v)(sigma_G)^-1 has precisely the same source and target, and the canonical counit/shift equation makes it v epsilon_L[-n] sigma_F. Injectivity of the stated adjunction bijection proves equality in D(A) before homology. This is routine mate algebra with every equation written, not an uncited comparison hidden behind a word such as “transport”.

Step 8 uses only the equations proved in steps 3–7 and shift zero/addition laws already supplied in step 1. Shifting v=u[-n] recovers u, hence G(u) with the canonical G(M[n])≅GM[n] comparison. No new lemma is hidden here. All eight steps are shorter than 2000 characters.

I checked n=0 (the unshifted counit calculation), n=1 and n=-1 (signed shifted differential), zero L or M, the point site with identity coefficient map (chi is identity), and a nonflat coefficient map such as Z→Z/2 (A[-n] remains free over A and pulls back to O[-n]; nothing requires G to preserve K-injectives). The result is a map, with no isomorphism claim. No SGA source or route is used.

The off-unit citations are generic homological tools, not replacements for a stability-unit step; their purposes are explicitly recorded in split_report.tool_uses. The citations file contains the full verbatim statement for each step's cited node, so its use and hypotheses can be checked without guessing from a title. Every proof dependency is a uses entry and conversely. No unresolved mathematical work remains in this split; server preflight and independent maintainer review are the next checks.
