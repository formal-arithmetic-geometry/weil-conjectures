# Worker report

Item: lem-pd-section-tensor-representatives-exists. Group: NA. Stage 1 only, 2026-10-26.

## Files written

- dag/nodes/sec-poincare-duality/lem-pd-section-tensor-representatives-exists.json — existing statement node, now split into seven proof steps; not a Mathlib leaf.
- citations.json — 15 verbatim statement quotations, covering every use in every proof step.
- report.md — this report. searches.jsonl is the original append-only output of the required msearch.py commands. prepare.py is a sandbox-only JSON preparation script, not part of the DAG delivery.

New nodes: 0. New Mathlib leaves: 0. No Lean file was written and no compiler, Lake or build command was run.

## Attachments

None. I searched the live WeilConjectures tree by notion and exact blueprint tag, and also read the actual matching declaration in lean/Sheaf/Paper/SectionDerivedRealization.lean. section_tensor_representative_exists at lines 226–231 has sorry. tensor_representatives immediately above its downstream users proves uniqueness by invoking that sorry theorem. Neither is a finished attachment, and the theorem in question is under Sheaf, rather than a separate finished upstream declaration under WeilConjectures.

## WANTED

None. The Stacks sources and the exact Lean predicate are present. The section-equivalence normalization is an agent argument using existing DAG lemmas, not a theorem attributed verbatim to Stacks.

## Statement repair and other findings

STATEMENT-DISPUTED: the imported statement was only “Existence part of the normalized derived section tensor representative.” It introduced no objects, transformation type or conditions, so could not be checked as a self-contained proposition. I expanded it to the exact existential type of the live section_tensor_representative_exists and TensorRepresentativeCondition (SectionDerivedRealization.lean:197–231): existence of q, the prescribed all-internal-complex normalization, invertibility when either arbitrary section complex is acyclic-test K-flat, and existence of a regular-unit isomorphism. This is the parent statement with “exactly one” replaced by “a”; no mathematical hypothesis or clause was changed. In particular, the unit assertion remains Nonempty, not a specified choice, and no flat-term or boundedness assumption was added. This is not a counterexample to the intended existence theorem; it repairs an incomplete import.

The original one-step proof said only “construct ... and transport all three clauses”, citing definitions and the ordinary comparison. It omitted the actual extension from internal images, the all-pairs localization-counit identification, the independent-universe K-flat bridge, and the unit composite. These arguments are now explicit, supported by existing statement nodes. Tag 07A4 concerns pullback of derived tensor, not the exact section representative predicate; the source field now distinguishes that contextual tag from the tags actually used here. I kept the original maintainer-owned metadata and previous search records; the old COMPILER review is not represented as a mathematical review by me.

## Earlier attempts and live comparison

I ran the exact requested archive listing. No abandoned directory for this item existed under any group. The active sandbox contained only dispatcher brief markers, without an item node, report or search record. I copied the live item before modifying it. There was no item-specific repair note. The parent node and its existing review supplied useful pointers to existing comparison nodes, but I independently opened their current statements and checked their hypotheses; I did not treat the parent's review as proof. Its three-clause statement agrees with the live Lean predicate.

The three original Mathlib searches dated 2026-10-24 were retained as inherited records from the live item. They are not claimed as searches made by NA. All eight new records dated 2026-10-26 were actually run through msearch.py and are preserved unchanged in searches.jsonl, including the broad grep whose truncated hit list was unhelpful. I repeated that grep with the relevant Mathlib subdirectories and read the returned declarations. No archived search was reused or relabelled.

## Source and blueprint route

I read AGENTS.md, the worker brief and role, the three levels in SETUP.md, GOAL.md, the stage-1 contract, delivery-errors B–E (including the repeated historical copy), the chapter record and sk-thm-sf-verdier-exchange unit. The unit's exchange route is unchanged; this is an auxiliary coefficient-model construction, not a replacement of its exchange proof. blueprint_refs ancestor returns None for this created item. I searched all imported blueprint records with blueprint_refs for representative/section/conjugate tensor terms and searched the current literature/blueprint/latest chapter files. The one “section tensor” blueprint match, def-pur-supported-exterior-product, defines an exterior product and does not state this normalization. No same_as match was found.

For the item I read sites-cohomology.tex: 06YS lemma-K-flat-resolution, 06YT lemma-derived-tor-quasi-isomorphism-other-side, 06YU definition-derived-tor and its construction, 07A4 lemma-pullback-tensor-product, 0FPQ lemma-symmetric-monoidal-cat-complexes and 0FPT lemma-symmetric-monoidal-derived. I checked the tag-to-label mapping and read sites-modules.tex 03EK section-tensor-product and 0GMW lemma-sheafification-tensor. The latter source explains the ordinary balanced tensor used by the existing internal/section comparison. Stacks leaves monoidal coherence details omitted; those details are not silently claimed here, but supplied by the existing total-tensor and derived-monoidal statements.

No new node was created, so no new statement needs an independent source or new-node edge-case review.

## Mathlib verdict

LeanFinder, Loogle, LeanSearch and source grep all ran successfully. I tried two semantic phrasings and inspected Mathlib/CategoryTheory/Localization/Monoidal/Basic.lean:50–180, Algebra/Homology/DerivedCategory/Basic.lean:90–165 and 270–305, and CategoryTheory/Monoidal/Tor.lean:1–90. tensorBifunctorIso assumes the morphism class is preserved by tensor with every object; arbitrary quasi-isomorphisms of all complexes do not satisfy that condition. It therefore does not directly specialize to the K-flat resolution construction here. Tor and Tor' are degreewise functors for categories with projective resolutions. Q and singleFunctorIsoCompQ provide localization and degree-zero infrastructure. None states this normalized section-equivalence theorem, nor its one-sided K-flat invertibility. The search results and that verdict are recorded on the item.

## Not duplicates

No new nodes were created. I reused lem-pd-conjugate-tensor-localization-counit and lem-pd-ringed-kflat-native-model-identification instead of making new nodes for their all-complex comparison and K-flat test bridge. I avoided lem-pd-section-kflat-tensor-comparison, which is downstream of the realization this item supports. The parent existence-and-uniqueness node is also downstream and is not cited in the proof.

## Review by NA

I reviewed the node and sources against delivery-errors B–E, rather than accepting the imported sketch. Here is what each step actually takes from the cited statements.

1. def-pd-section-derived-tensor-data specifies the conjugate tensor, exact localized equivalence, normalization maps, signed totals and transferred functorial flat resolutions. sk-def-sfb-derived-tensor-hom supplies the actual internal relative K-flat tensor with its lax localization, not an unrelated absolute tensor. lem-pe-internal-section-tensor-comparison explicitly asserts exactness, natural tensor and regular-unit comparisons, coherence, and preservation/reflection of acyclicity, flatness and K-flatness. Thus the internal category and section-ring module category meet the hypotheses of the generic conjugate-counit theorem. The coefficient universe contains the small site; its object and morphism universes need not equal one another. The quasi-inverse properties follow by reflection and the specified counit, not by assuming another unspecified equivalence.

2. The same fixed tensor data and internal lax comparison make alpha a natural transformation on pairs of internal complexes. lem-trf-exact-tensor-equivalence-kflat-homotopy explicitly supplies the termwise inverse equivalence and its unit/counit. I wrote q_y = G(e_y) alpha_Iy F(e_y^{-1}), checked its source and target, and wrote the naturality substitution. This step is elementary composition of given natural maps, not a new transport theorem.

3. That termwise-equivalence statement has the fixed triangle identities. I checked e_Jx = J(eta_x^{-1}) and naturality of alpha along eta_x^{-1}; the two inverse factors cancel in the required order. This proves the normalization exactly, without assuming E is injective on objects. No separate uniqueness lemma is needed to prove existence.

4. lem-pd-conjugate-tensor-localization-counit explicitly states both the defining equation for epsilon^c and epsilon^R v = epsilon^c for every complex pair without K-flat or flat-term hypotheses. def-pd-section-derived-tensor-data identifies the very same c and ell; I checked ell = Q(t) kappa against its Lean definition. Solving the equation gives the alpha used in Step 2. The counit extension is identical, hence q = epsilon^c. This uses the node's statement, not its proof or a merely resolving-pair comparison.

5. lem-pd-ringed-kflat-native-model-identification explicitly says that each localization transformation is invertible whenever either complex is acyclic-test K-flat, including nonflat terms, and equates the two K-flat tests. The tensor data give its functorial-flat-resolution premise. Composing epsilon^R with the invertible v from Step 4 therefore gives exactly the disjunction in clause (2). This was the crucial missing input in the original proof; citing only the definition of flatness would not suffice.

6. lem-sfb-total-tensor-homotopy states the degree-zero complex unit and lem-sfb-derived-monoidal says the derived constraints are induced from those of complexes. The internal module category is the category with that specified structure in the tensor data. lem-pe supplies E(R_internal) isomorphic to R_sec. I checked each type in the composite D(E)(u_internal), kappa, Q(u0[0]); outside degree zero the chain-map equations are between zero maps. It yields precisely a unit isomorphism in the derived category. This uses no claimed uniqueness of it.

7. Conjoining the three established conditions and taking the displayed q is elementary. The step cites no additional fact.

I reopened every cited node statement, verified the quoted formulas verbatim for citations.json, and checked the statements rather than looking for support hidden in their proofs (C4). The non-elementary counit identification, K-flat comparison and monoidal-unit construction are all named existing nodes (C1). The four off-unit tools declared in split_report are generic equivalence or monoidal tools; the two pd comparison nodes already have the item's unit. A dependency traversal of statement and proof edges from every proposed cited node found no path back to this item; the required server checks remain the authoritative cycle check. The longest proof step is 1011 characters, so none exceeds the 2000-character long-step threshold. No new clause-restatement node, elementary-node inflation, duplicate or Mathlib leaf was created.

I tested the argument at E = identity (the construction reduces to the internal localization map), the zero ring and empty scheme (all relevant zero objects and units still give isomorphisms), unbounded acyclic complexes, and K-flat complexes with nonflat terms (flat terms are never imposed on the inputs). For Z/2 placed in degree zero over Z, clause (2) gives no invertibility when both inputs are that non-K-flat complex, so it makes no false claim about Tor. With one regular degree-zero input the localization map is invertible. These checks also rule out accidentally using total tensor as an underived tensor on arbitrary complexes.

## Completion and validation

The mathematical split, statement repair, exact citations and report are complete. The required deliver.py --no-push finished successfully: OK (not pushed) at 9eb8a410b1a, preflight passed. This includes the server DAG and split-review checks and local citation/search gates. The final delivery runs its preflight again before pushing. No unresolved mathematical or literature issue remains.
