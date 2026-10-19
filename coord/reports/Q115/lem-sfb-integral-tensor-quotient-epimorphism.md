# Q115: lem-sfb-integral-tensor-quotient-epimorphism

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-integral-tensor-quotient-epimorphism.json: statement, split; no Mathlib match. The statement and its three statement dependencies are unchanged. Five complete proof steps replace the empty proof.
- citations.json: eleven entries, one for every step/node citation, copied verbatim from the cited statements.
- searches.jsonl: six new actual searches through the required msearch command. Earlier searches in the repository node are retained.
- report.md: this report. prepare.py is sandbox-only preparation material, not a delivered node.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Read-only searches of WeilConjectures/ for the exact blueprint id, tensor/epi, and locally-surjective tensor terminology found no declaration that proves this statement. The project ring-theory tensor epimorphism result concerns algebra epimorphisms and does not assert this sheaf-module unit is locally surjective. Existing source metadata about tensor constructions is not a proof of this item.

## WANTED

None. All sources used are present locally.

## Findings and changes

The statement is correct with the existing local-surjectivity hypothesis. No statement dispute or source correction is needed. Bhatt–Scholze Proposition 6.8.4(1), p.59, says its proof is left to the reader; the generic sheaf lemma here supplies the quotient transition used by the existing parent split, rather than claiming that the proposition explicitly states this general-site lemma. Accordingly proof_origin.by is agent. Its proof is based on the actual tensor and sheafification constructions in Stacks 03EK/03CY and the local-section theorem 00WK, with 00YR as the bridge between abelian and set sheafification.

The proof now explicitly constructs the unit, proves it is linear for the restricted R'-action, obtains local presheaf representatives, lifts finitely many coefficients on successive covering refinements, writes the balanced tensor identity, and proves the epimorphism assertion by right cancellation and the sheaf uniqueness axiom. It never replaces local surjectivity by surjectivity on sections. It also never assumes enough points, a terminal site object, or global lifts of coefficients.

Whole-DAG keyword and tag searches and tools/blueprint_refs.py searches for tensor product, locally surjective, quotient epimorphism, sheaf tensor, and scalar extension unit were read. The existing tensor definition gives sectionwise tensors and module sheafification. The existing general-site underlying-set comparison and local-section lemma provide exactly the two auxiliary results needed; no new nodes are warranted. In particular the similarly named lem-weil-pbc-module-sheafification-underlying-sets is only about opens of a topological space and was deliberately not applied to an arbitrary site.

Read the ancestor's current blueprint proof at literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-coefficient-heart/sk-lem-coefficient-heart-closure.proof.md, especially paragraph (2), and the chapter/unit records. The parent lem-sfb-integral-lisse-reduction-equivalence uses this item in its step 4 to prove the reduction transitions epic. The split keeps that route. The off-unit generic local-section theorem is declared as a tool use; it supplies no replacement of a coefficient-heart argument.

Mathlib hits were checked against the source: Sheaf/ChangeOfRings.lean:55-74 proves restriction induces a Hom equivalence; Sheaf/Generators.lean:63-69 transports generators along an already epic map; neither proves this unit is epic. Presheaf/Sheafify.lean supplies local surjectivity of sheafification, not of F to the presheaf scalar extension. Ordinary ModuleCat extension/restriction unit formulas construct 1 tensor m without proving the sheaf quotient statement. The second semantic phrasing returned the same nearby sheafification constructions. All actual queries and outcomes are recorded; there was no unavailable service. Existing unrelated Mathlib results are used only through the existing DAG nodes, not as uncited assertions in the proof.

## Unfinished work

None in this one-level stage-1 split. No Lean was written and no compiler, Lake, or build command was run. Only this sandbox was written.

## Review by Q115

I read delivery-errors B through E with the item, the six cited statements, and the sources open. For the item, I read Bhatt–Scholze Proposition 6.8.4(1) and its omitted-proof sentence, the actual sheaf tensor formulas of sites-modules.tex Tag 03EK (section-tensor-product) and the change-of-rings formula preceding lemma-adjointness-tensor-restrict, Tag 03CY (lemma-sheafification-presheaf-modules), sites.tex Tag 00YR (section-sheaves-algebraic-structures), clause (gamma), and Tag 00WK (lemma-sections-sheafification). No SGA source was used. There are no new statements to review separately.

Step 1 uses def-pur-sheaf-tensor-product for the sheafification of the sectionwise tensor, def-weil-presheaf-modules-sheafification for its linear sheafification map, and def-weil-sheaf-of-modules-category for what a module sheaf morphism means. Each statement actually gives that content. Additivity, 1 tensor am = q(a) tensor m, and compatibility with restriction are written out from the tensor relations; there is no asserted adjunction comparison hiding here.

Step 2 uses the module sheafification definition's explicit identification of its underlying abelian sheafification, lem-pc-sites-sheafification-underlying-sets for the same unit to be set sheafification, and lem-weil-pbc-site-sheafification-sections-local for local representatives. I checked all three statements, including the unit compatibility and the last node's universe convention. Smallness in the coefficient universe satisfies that convention after placing objects and morphisms in that common universe. I corrected an initially considered citation: the module-underlying-sets lemma for a topological space would not justify this application on a general site; the cited abelian-presheaf theorem does.

Step 3 uses only the sectionwise tensor described by def-pur-sheaf-tensor-product. Its finite-sum representation follows from the defining generators and relations, with negative coefficients absorbed into the module factor; that elementary argument is explicit. This is a proof step, not an auxiliary node duplicating a tensor definition.

Step 4 uses the transitivity of coverings stated in def-weil-pbc-sites-and-cohomology and the balanced tensor definition stated in def-pur-sheaf-tensor-product. Local surjectivity of q is a hypothesis of the item. I checked that the iterative construction restricts earlier lifts before taking the next covering, so it does not require a single global lift or an unjustified common refinement. The finite induction gives exactly the displayed preimage sum. Empty sums and empty covers are explicitly covered. This is an elementary finite coefficient calculation, not an appeal to an unnamed flatness or exactness theorem.

Step 5 uses the sheaf equalizer axiom in def-weil-pbc-sites-and-cohomology and the componentwise notion of module morphism in def-weil-sheaf-of-modules-category. The direct cancellation argument is given section by section, so no unrecorded theorem about epis, underlying sets, or exact forgetful functors is needed. Equality on a covering implies equality globally even for an empty covering. No basis or finite generation of F is assumed in any step.

For B, there are no new nodes, no statement-only proof leakage, and no duplicated clause hidden in a child node. Existing records and provenance are retained. For C, every uses entry was opened; citations.json contains actual statement text, never a proof quotation. The two sheafification results are cited separately, avoiding a false inference from a definition alone. For D, the steps carry the whole coefficient-lifting argument rather than moving it to a restatement. For E, I tested the one-object point site (ordinary surjective A to B, arbitrary A-module), q the identity, F=0, R the zero ring sheaf, and objects with an empty covering. The construction gives respectively the ordinary sum of lifted coefficients, the unit identification, zero preimages, zero target, and the unique section. Without local surjectivity, Z to Q and F=Z on the point site would fail, so the proof genuinely uses exactly the given quotient hypothesis. No flatness, no finiteness on F, and no rank restriction were added. All steps are under 2000 characters, and none hides a separate comparison lemma.
