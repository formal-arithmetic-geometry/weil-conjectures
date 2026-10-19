# Stage-1 split: lem-sfb-perfect-constant-derived-map-local

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-perfect-constant-derived-map-local.json`: item, statement unchanged, four proof steps, status split; Mathlib searches found no match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-perfect-constant-local-chain-representative.json`: one new statement-only unsplit node, Stacks 09BD (constant finite-projective specialization of 08FR(1)); no Mathlib match.
- `citations.json`: one verbatim statement quotation for every node cited by every item step.
- `report.md`: this report.

## Attachments

None. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item's id and blueprint tag, 09BE/09BD, local-actual, and perfect/projective constant-complex language found no declaration proving the item or new input. The master source was also searched as reference, not as evidence of completed proofs. Existing constantSheafOver declarations concern underived module maps, represented by the existing site-constant-morphism-local node, which is reused.

## WANTED

None. The item and the sole new node are sourced from the archived Stacks text.

## Findings and corrections

The item is exactly the commutative-ring case of Stacks 09BE, `sites-cohomology.tex`, lemma-locally-constant-map. Its hypotheses and conclusion need no correction. It had no proof. The proof now follows its two cited inputs: 09BD for actual chain representatives, then 093S(3) for locally algebraic components. The new input has arbitrary sheaf-complex target, whereas the item concludes algebraicity in D(R) for a constant target; these are different tasks. The finite component refinement and algebraic chain equations are proved in the item, not moved into a new lemma.

A potentially invalid shortcut was deliberately avoided: constant sheaf realization is not faithful over an object covered by the empty sieve. Step 3 assigns the zero algebraic chain map on such objects, where every module sheaf restricts to zero; step 4 proves faithfulness of constant sections only on the other objects by local equality after sheafification. No geometric point is assumed. Also, the constant-module-section-properties node requires a Noetherian coefficient ring, so it is not cited here. General exact module sheafification supplies exact constant realization over arbitrary R instead. Coverings are refined only finitely many times, so the unbounded target causes no infinite common-refinement problem.

All searches were run with the prescribed msearch command and copied from its actual log. Both item and new input have LeanFinder, Loogle, grep, and LeanSearch attempts, with second semantic phrasings. K-projective hits were inspected in Mathlib/Algebra/Homology/HomotopyCategory/KProjective.lean and DerivedCategory/KProjective.lean: they require projectivity in the ambient abelian category; finite projective coefficient modules need not yield projective objects of arbitrary sheaf categories. The other hits concern underived constant sheaves or special condensed sites. None is a one-line specialization giving the assertion. There are no Mathlib leaves in this delivery.

The unit is sk-lem-integral-models, and the chapter is sec-six-functors-basics. I read both records and the current blueprint ancestry det-lem-integral-models-stacks. This work supplies the 09BE input to 09C5, then 09C6 in the local-perfect-lifting portion of the integral criterion. It does not change the chapter or unit route, and is not the unit's statement node, so no unit realization record is edited. Generic off-unit tools are declared only under split_report.tool_uses for review: the site constant-map lemma, local sheafification-section equality, and exact-functor derived factorization. No SGA source is used.

## Not duplicates

lem-sfb-perfect-constant-local-chain-representative vs lem-weil-pbc-finite-free-etale-local-actual: the existing node assumes a scheme's small etale site and finite free source terms; the new 09BD node allows an arbitrary small site and finite projective terms. Its target is any sheaf complex. The existing node additionally includes local null-homotopy, which is not asserted or needed here.

lem-sfb-perfect-constant-local-chain-representative vs lem-weil-pbc-finite-ring-derived-local-constancy: that node assumes a finite coefficient ring, a scheme's small etale site, and bounded finite locally constant cohomology; its local-model and sheafified Hom conclusions do not supply actual chain representatives on arbitrary sites with arbitrary ring coefficients and arbitrary sheaf-complex target. It cites 08FR in its proof, not as its own general statement.

lem-sfb-perfect-constant-local-chain-representative vs lem-sfb-perfect-constant-derived-map-local: the item gives derived algebraic maps into a constant target. The new input gives actual sheaf chain representatives into an arbitrary sheaf complex, and makes no assertion that these components or their equations are algebraic. The latter argument remains in item steps 3 and 4.

Whole-DAG tag and keyword searches and blueprint_refs searches for 09BD, 09BE, local actual, map out locally constant, and strictly perfect were performed. The one blueprint strictly-perfect hit is a definition on ringed spaces, not the required statement. Same_as is empty. The existing site-constant-morphism-local node supplies 093S(3), so no new node for that fact is created.

## Review by Q129

I read Stacks sites-cohomology.tex at 09BE and the complete 09BD statement and proof, together with its referenced 08FR statement and proof. 09BE explicitly cites 09BD and Modules on Sites 093S; I read 093S(3) in sites-modules.tex. For the new node, 09BD has exactly a finite complex of finite projective coefficient modules, arbitrary sheaf-complex target, and local actual chain representatives. Restricting its coefficient ring to commutative R agrees with the project convention. No omitted boundedness or points hypothesis has been introduced. 08FR(1) is its more general strictly-perfect ringed-site precursor; the new statement remains statement-only.

For step 1, I opened the statements of def-pc-perfect-ring-complex, def-weil-abstract-derived-category, lem-weil-pbc-site-module-presheaf-sheafification-exact, lem-pc-sites-module-sheafification-interface, and lem-weil-pbc-exact-functor-derived-factorization. They give, respectively, the chosen finite-projective model, representative complexes and localization, exact sheafification, the constant-ring module action with the underlying abelian sheafification, and natural representative identifications for the induced exact derived functor. Exactness of the constant-presheaf functor is sectionwise; composing with the cited exact sheafification proves the exactness needed here. I checked the source 00WJ in sites.tex as well. The source and target isomorphisms are transported by this natural derived realization, rather than equating different objects literally.

For step 2, the new 09BD statement gives the actual sheaf chain maps claimed, with F bounded finite projective and no restriction on G. This step does not use the proof of a cited node. For step 3, I opened lem-weil-pbc-site-constant-morphism-local and checked its exact finitely-generated-source, arbitrary-target, arbitrary-site and non-empty-sieve condition. I also read the underlying project declaration exists_mem_forall_exists_constantSheafOverHom_comp_map_eq and its canonical slice comparisons. The site-definition and localized-site statements supply the covering and restriction notions and relocalization. Only the finitely many nonzero F degrees are involved. Empty-covered objects remain harmless zero restrictions; on other objects the node applies with B=R, M=F^q and N=G^q.

For step 4, I opened both module-sheafification and underlying-set-sheafification statements, and the site-sheafification-sections-local statement. The latter explicitly asserts local equality of two presheaf sections with the same sheafification image. I read sites.tex 00WB and 00WK and verified how this proves injection of constant sections on a nondegenerate object: a covering there cannot be empty, so agreement of constant presheaf values on any covering member is actual equality of module elements. This tests each chain equation on every x; no finite presentation of G, finite target, stalk functor, or enough-points theorem is used. Localization and natural exact-functor representative isomorphisms then give precisely the derived morphism alpha required, with its correct direction. The same V is used to verify every equation and represent the original map.

I tested the item and the new input on the one-point site (ordinary finite-projective chain representatives), the zero complex, a single finite-projective term, a finite projective summand which is not assumed free, an unbounded target, the zero ring, disconnected sites, sites without points, and an object covered by the empty sieve. Boundary equations at the ends of F are included: although the source term may be zero, d_F into its first nonzero term is zero and the equation with last nonzero source still matters. The argument handles both. These tests are compatible with 09BD and show why discarding boundedness of the target and avoiding projectivity in the sheaf category are necessary.

Against delivery-errors B–E, the new node introduces all objects, carries only a statement, uses single TeX escapes, and has tag plus source label and truthful search records. Existing definition nodes cover its notions. The item has a complete argument rather than a clause restatement; every non-elementary input is cited, each citation was read as a statement, and citations.json was checked by literal substring matching. The new node depends only on definitions, so introduces no back-edge to the item. Off-unit generic tools are declared for review. The source and node statements agree; no STATEMENT-DISPUTED is needed. No Lean file, compiler, Lake command, live repository, or launcher file was modified.

## Unfinished work

The new 09BD input is intentionally unsplit, as required for a one-level split. No item proof step is left unfinished. The accepted sandbox is to be handed to a fresh second reader; no delivery push is authorized or performed.

## Second reading by Q129

- Item statement: checked Tag 09BE (`lemma-locally-constant-map`) in `sites-cohomology.tex` hypothesis by hypothesis; the final-object site, ring, perfect source, arbitrary target object, and local derived equality all agree.
- New node `lem-sfb-perfect-constant-local-chain-representative`: checked Tag 09BD (`lemma-map-out-of-locally-constant`) and its Tag 08FR(1) precursor; the bounded finite-projective source, arbitrary sheaf-complex target, local chain representatives, and no target boundedness agree, with all notions self-contained through definition nodes.
- Step 1: checked the perfect-complex and derived-category definitions plus the exact sheafification, module-sheafification interface, and exact-functor derived-factorization statements; these support the chosen representatives and natural termwise constant realization without a Noetherian hypothesis.
- Step 2: checked the cited 09BD node itself; it gives the claimed local chain map on each slice and requires exactly the bounded finite-projective source used here.
- Step 3: checked the cited 093S(3) constant-morphism node, site covering axioms, and localized-site definition; its target is the constant sheaf `\\underline{G^q}` and finite common refinement supplies simultaneous algebraic maps, including the empty-sieve case.
- Step 4: checked the module and underlying-set sheafification interfaces, local equality after sheafification, exact-functor factorization, and derived localization; these prove injectivity on nondegenerate objects, every chain equation, and the final local derived equality, including boundary degrees.
- Edge cases: rechecked the one-object site, zero complex, one-term complex, nonfree finite projective summand, unbounded target, zero ring, disconnected or point-free sites, and empty-covered objects; no statement changes are needed.
- Changes: corrected the new delivery item's stale `created.item` and `created.group` metadata to `lem-sfb-perfect-constant-derived-map-local` and `Q129`; the proof text already explicitly used the constant target `\\underline{G^q}`. No mathematical statement, citation, or source was changed.
