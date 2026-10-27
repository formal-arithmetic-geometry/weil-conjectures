# Stage 1 delivery: lem-sfb-stable-picard-theta-ampleness

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-stable-picard-theta-ampleness.json: item, split into seven argument steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-stable-moduli-regular-universal-atlas.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-jacobian-canonical-line.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-regular-group-rigidified-line-extension.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-picard-etale-schematic.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-regular-group-generic-ampleness.json: statement, unsplit; no Mathlib match.

citations.json has one verbatim statement quote for each of the 20 step/node citations. searches.jsonl is the unmodified msearch log; search-results.json retains the exact printed answers for all 20 searches on the five new nodes. search-specs.json and research.py record the questions and permitted command invocations. Auxiliary Python scripts remain only in the sandbox and are not delivery node files.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag, stable-curve and Picard/theta terminology, and read the relevant Picard directory search results. Existing smooth-curve Picard and rigidification code does not state the item or the new lemmas. In particular ordinary gluing of rigidified generators is not extension of a line module across the missing base fibres.

## WANTED

WANTED: P. Deligne, Le lemme de Gabber, Asterisque 127 (1985), Sections 4.1--4.8, printed pp.141--144, for the item and the four Deligne-sourced supporting nodes. The repository does not contain the named PDF. I read the primary scan online at https://www.numdam.org/item/AST_1985__127__131_0.pdf, including pp.136,138,141--144,149. No document was downloaded or written to the repository.

WANTED: M. Raynaud, Faisceaux amples sur les schemas en groupes et les espaces homogenes, LNM 119 (1970), XI Theorem 1.13, for lem-sfb-regular-group-generic-ampleness. Deligne 4.3 and 4.8 explicitly explain this use; the general regular-base formulation is stated separately and remains the responsibility of an unsplit item. I do not claim to have read the original Raynaud theorem. Search results for modern accounts were not treated as its proof: one modern draft has an obviously erroneous assertion of projectivity for arbitrary homogeneous spaces (which would include G_m), so I did not cite that text.

## Issues and corrections

The imported assertion is retained, with explicit definition citations added. There is no STATEMENT-DISPUTED assertion: the claim agrees with Deligne 4.3. No hypotheses were added or dropped. The report and proof deliberately distinguish the canonical smooth-Jacobian line, its regular-universal-base extension, and its pullback/descent to an arbitrary, possibly nonregular base.

Deligne 4.8 prints a reference to [8] XI 1.13, whereas 4.3 correctly refers to [10] XI 1.13; bibliography [8] is a four-page Neron-model note and [10] is Raynaud's LNM 119. The new node identifies this bibliographic typo. This is not a mathematical change or a use of an SGA source.

The inherited blueprint creation chain has no surviving blueprint ancestor: tools/blueprint_refs.py ancestor returns None. I retained its null ancestor and exact inherited chain rather than invent a replacement. I read the current blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), and the chapter and recorded unit. The original dependency came through its alteration/curve-level auxiliary route, which this proof preserves. Current latest is main 7284bb09daf97437d544c51882b325f9c52cd345. This is not the unit key node, so no unit record was written.

The first draft of the assembly implicitly needed Picard representability on the universal bases, although the item assumes representability only for its given family. I repaired Step 1 to cite projective-bundle properness, universal structure-sheaf cohomological flatness, full Picard-space existence, and openness of the multidegree-zero subgroup before applying the new nodal theorem. Another draft described an arbitrary-base-change consequence as if it were literally in the fpqc descent theorem. I removed that wording and wrote the affine-base pullback argument using the actual affine-pullback ampleness theorem. Finally def-sc-group-scheme only defines groups over a field: the generic-ampleness node now defines its group-scheme-over-S structure inline instead of misusing that definition.

## Not duplicates

lem-sfb-stable-moduli-regular-universal-atlas vs lem-sfb-unpointed-stable-coarse-projective: both cite 0E9C, but the existing node is over a field and asserts a projective coarse moduli scheme; the new node is the arithmetic etale universal family and its regular overlap nerve over Spec Z. A field-based statement cannot supply mixed-characteristic universal bases.

lem-sfb-stable-moduli-regular-universal-atlas vs lem-sfb-stable-isom-finite-unramified: the existing node states finite unramified Isom over fields; the new node supplies a surjective arithmetic etale presentation with dense smooth locus and regular nerve, not the Isom finiteness assertion.

lem-sfb-stable-moduli-regular-universal-atlas vs lem-sfb-abelian-level-coarse-moduli: the existing node concerns smooth curves with an invertible prime level over a field; the new node is unpointed stable curves, including singular fibres, over all of Spec Z, without a level structure.

lem-sfb-stable-moduli-regular-universal-atlas vs lem-sfb-stable-abelian-level-normalization: that node gives the finite normal level cover over a field; it neither gives a regular universal base nor an arithmetic etale atlas. It also depends transitively on the present item and must not be cited here.

lem-sfb-smooth-jacobian-canonical-line vs lem-sfb-curve-polarized-jacobian-faithfulness: the existing theorem concerns an algebraically closed field, canonical polarization and faithful automorphism action. The new theorem gives the diagonal Poincare line for smooth families over arbitrary locally Noetherian bases, including coherent base-change identifications. It is a construction input, not a renamed stable ampleness conclusion.

lem-sfb-smooth-jacobian-canonical-line vs lem-sfb-theta-poincare-pullback: that comparison concerns a fixed pointed curve over an algebraically closed field and the Abel map to its Jacobian. It does not give the relative canonical line and arithmetic base-change coherence used here.

lem-sfb-regular-group-rigidified-line-extension vs lem-trf-algebraic-space-invertible-descent: extension across missing fibres over a regular base differs from effective etale descent of already defined lines. Both are needed and neither is a clause of the item.

lem-sfb-nodal-picard-etale-schematic vs lem-sfb-nodal-multidegree-zero-locus: the existing node gives openness, quasi-compactness and separatedness only; it does not supply a scheme after etale localization of the base.

lem-sfb-nodal-picard-etale-schematic vs lem-sfb-picard-space-curves-smooth: the existing node gives full Picard algebraic-space existence and smoothness under cohomological-flatness hypotheses. It does not supply schematicness of the multidegree-zero group after base localization.

lem-sfb-nodal-picard-etale-schematic vs lem-sfb-stable-relative-picard-kummer: the parent is only over an algebraically closed field base and its proof depends on the present ampleness item. The new node is the independently proved Deligne 4.4--4.6 scheme-local input; it contains no global ample line or global scheme consequence, and avoids that cycle.

lem-sfb-regular-group-generic-ampleness vs lem-sfb-space-relative-ampleness-fpqc-descent: the former propagates generic ampleness on group schemes over a regular base; the latter descends a line already known ample on base covers, with algebraic-space representability included. These are different hypotheses and conclusions.

All new-node questions were searched across the DAG by id/title/statement keywords, across the blueprint using blueprint_refs search (theta, relatively ample, Picard, Picard space, stable moduli, smooth stable, universal atlas, rigidified, rigidified extension, principal polarization, autoduality, connected group scheme, generic ampleness), and in the project Lean. No same_as blueprint statement was found. The broad theta and Poincare searches mostly returned cohomological comparison maps or duality nodes, not geometric line-module results. No new node merely restates a stable singular-fibre ampleness clause: the nontrivial argument assembles regular universal extension, uniqueness and coherent descent, generic ampleness after independent scheme-localization, arbitrary base pullback, and polarized descent.

## Review by Q120

I read coord/delivery-errors.md sections B--E in full and applied the checks to the actual statements, sources and proof. I read Deligne 4.1 (smooth line), 4.2 (extension/uniqueness), 4.3 and 4.8 (regular-universal reduction and scheme-only ampleness), and 4.4--4.6 (scheme charts and translating enough charts). I also read the local Stacks theorem-stable-smooth-proper, Tag 0E9C, and lemma-smooth-dense-in-stable in moduli-curves.tex for the arithmetic atlas input. The generic Raynaud source limitation is explicitly marked WANTED above; no SGA is cited. Accordingly proof_origin is agent, not a claim of a local literature proof.

Step 1: I opened the seven cited node statements. The atlas supplies regular arithmetic bases and dense opens, projective-bundle properness supplies exactly properness, the stable definition supplies flatness/finiteness/reduced connected fibres, the global-sections theorem supplies every-base-change cohomological flatness, Picard-space-curves-smooth supplies full algebraic-space representability, and nodal-multidegree-zero-locus supplies the represented open subgroup. Only after these does the new nodal statement apply. The stronger parent relative-Picard-Kummer node was specifically excluded to prevent a cycle. Relative curve dimension one is in the stable definition and is within the Picard existence theorem's at-most-one bound.

Step 2: The smooth canonical-line statement is used for its line with identity trivialization; the regular-group extension statement is used for its existence clause. Every regular-base, dense-open, finite-presentation, separatedness and geometric-integrality hypothesis comes from Step 1. The smooth line is only requested on the actual smooth-family open, never on a singular fibre.

Step 3: The same two statements are used for the canonical smooth identifications and for unique extension of a specified isomorphism. The latter explicitly concerns line isomorphisms, not just equality of Picard classes. U_1 and U_2 are regular by the atlas theorem; pullback projections are etale. Therefore both compositions on a triple overlap really are extensions of one identical smooth-open isomorphism. This proves the cocycle, rather than merely claiming compatibility.

Step 4: The atlas statement gives the actual scheme T and universal family isomorphism for the arbitrary S. The nodal statement identifies D_T under that family isomorphism and base change and supplies an etale base refinement with schematic D_Ta. I checked the invertible-descent node requires a scheme atlas of D, not an atlas of its base alone; this refinement makes exactly the required scheme atlas. Its morphism descent clause also glues the identity trivializations. Pullback is the tensor inverse image on ringed etale sites used in the new statements. No regularity of T or S is needed for the pulled-back descent cocycle.

Step 5: The nodal theorem, not an assumption of ampleness, gives schematic D_Wa first. W_a is etale over the regular universal base. Density of the smooth locus persists under etale open maps; its inverse image contains the generic points of these regular bases. The canonical smooth line is already ample on those fibres. The Raynaud node is applied to group SCHEMES, with all its other hypotheses supplied by the nodal theorem. I tested the distinction: the same generic-ampleness assertion for an arbitrary nonproper morphism would be false and is not what the new node says.

Step 6: I opened the existing space-relative-ampleness-fpqc-descent and pullback-ample-invertible statements. The first includes both representability and the ample conclusion; it is used only for covers, not for a fictitious arbitrary-base-change clause. The second requires an AFFINE morphism; the step checks this by choosing affine V and W and by the affine tensor-product formula after base change. Finite affine refinements over each affine base make the etale coverings fpqc, without supposing an arbitrary infinite etale family itself quasi-compact. Local relative ampleness then descends to the original possibly nonregular S. This also prevents assuming scheme representability descends without a compatible ample line.

Step 7: The nodal theorem gives finite presentation and hence finite type and quasi-compactness. I read the ample-very-ample-immersion-affine-base statement: over every affine W it gives exactly a finite-dimensional projective-space immersion and a positive power of M equal to O(1)'s pullback. This suffices for the asserted quasi-projectivity. I explicitly retain finite presentation, since an ample-line theorem cannot give a finite projective-space immersion for a disjoint infinite union from local finite type alone.

Small cases: S empty gives empty D and all claims vacuous. Smooth families have U^sm=U and recover the canonical line. Stable nodal compact-type fibres have torus rank zero, while nonseparating nodes allow positive torus rank: neither the nodal lemma nor the group criterion assumes D proper. A torus over a field has an ample trivial line, so the theorem does not incorrectly force projectivity. Nonregular/nonreduced original bases are allowed because only universal bases are subjected to regular extension; arbitrary original bases are reached by pullback/descent. In the extension node the requirement of geometric integrality prevents componentwise vertical twists invisible at the identity; it is not dropped. The generic-ampleness node makes no characteristic or field-base assumption, and its regular locally Noetherian hypothesis is checked each time.

All five new nodes have self-contained statements, empty proofs, empty proof_deps, null proof_origin and null mathlib_match. Their definitions are cited or given inline; in particular arbitrary-base groups are not defined by the field-only group-scheme node. The primary nonspecial-divisor and generic-ampleness arguments remain future splits of those stated inputs, rather than undocumented invocations inside an item step. The generic-extension lemma is independent of Picard spaces, and the nodal schematicness lemma is independent of global ampleness. None contains this item's full proof in its statement. Every item proof step is shorter than 2000 characters. All citations have a literal statement witness in citations.json. The item proof_deps is exactly the union of its uses. The report declares the genuinely generic off-unit properness, cohomological-flatness, invertible-descent and ample-immersion tools in split_report.tool_uses, with no change to the constructibility unit route.

## Unfinished work

No required stage-1 assembly is left unfinished. The five new mathematical inputs are intentionally unsplit, as the one-level split rule requires. No Lean source was written or compiled, no repository file or launcher file was changed, no agents were started, and no manual git command was run. Required server dry run and final delivery follow this review.
