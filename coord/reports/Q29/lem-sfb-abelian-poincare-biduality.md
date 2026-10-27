# Q29: lem-sfb-abelian-poincare-biduality

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-abelian-poincare-biduality.json`: statement item, split into seven explicit steps; no Mathlib match. Statement and statement dependencies retained.
- `dag/nodes/sec-six-functors-basics/lem-sfb-dual-isogeny-degree.json`: one new statement-only prerequisite, unsplit, no Mathlib match. It asserts that the dual of an isogeny is an isogeny of the same scheme-theoretic degree over any field.
- `citations.json`: one entry for every step/node citation, copied literally from that node's statement; whole statements are quoted where several clauses are used.
- `searches.jsonl`: the unmodified actual msearch log. Ancillary sandbox files are the extracted Milne text and scripts used to write/check the JSON.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact item tag, Poincare/Poincaré, abelian dual, bidual, dual-isogeny and kernel-degree concepts. Read the abelian-variety Basic and Isogeny sources: they provide geometric integrality, commutativity and isogeny rank, not abelian-variety Poincare biduality or dual isogenies. The ordinary module/sheaf biduality declarations have different objects. No declaration of the project proves the item exactly.

## WANTED

None needed for this split. Read the available `literature/milne-abelian-varieties_AV.pdf` directly (sandbox text extraction), I §8 printed pp.35–40 and I §9 printed p.41. The new unsplit node is the degree consequence of the theorem actually stated as 9.1 there; its further proof is future work. The item's explicit generic-field cancellation and naturality computations are my assembly, so `proof_origin.by` is `agent`.

## Corrections and route

The item was unsplit with no proof, and the sandbox initially had no node, report or previous search log. No repair note exists. No statement correction or weakening was necessary. Preserved its existing searches and appended the searches actually performed in this session. The only new node uses actual log entries for its own statement (two semantic phrasings, LeanSearch, Loogle and source grep); none of the returned signatures is an abelian-variety theorem.

Read chapter `sec-six-functors-basics`, unit `sk-thm-sf-ctf-stability`, SETUP's three levels and the newest `literature/blueprint/latest/` chapter/unit and direct-image proof. This is an auxiliary below the recorded Rosati/polarization chain for direct-image stability, not the unit's key node, so no chapter/unit file changes. `blueprint_refs.py ancestor` returns None for this inherited auxiliary chain; retain that provenance and prepend this item to the new node's `via`. Blueprint searches for Poincare, bidual, dual abelian, dual isogeny, dual isogeny degree, and isogeny were read; none states the new degree theorem or the item. Whole-DAG statement searches also checked the possible overlaps listed below.

Generic tools from other units are declared in `split_report.tool_uses`: rigidity, projectivity, integrality, commutativity, isogeny rank, ordinary module-pullback composition/tensor, global functions, regularity/normality and finite birational recognition. They serve those generic purposes, without replacing a step of the unit's geometric route. No SGA source is used.

## Source error

Milne 8.9 prints an equivalence of four conditions for an arbitrary divisorial correspondence. I do not use that equivalence. For example, take an elliptic curve E over an algebraically closed field, A=E×E, B=E and pull the universal Poincare bundle on E×E back by `(pr_1, id)`. A fibre over b in B is trivial only for b=0, so printed (b) holds. But B is not the dual of the two-dimensional A, and the fibres indexed by (0,x) in A are trivial, so (a) and (c) fail. This caution was already explicit in the item's source record. The true biduality conclusion in the item is retained and proved by a separate cancellation argument using 9.1.

## Not duplicates

- lem-sfb-dual-isogeny-degree vs lem-sfb-finite-torsion-weil-pairing: the latter concerns prime-to-characteristic torsion *points* over an algebraically closed field and perfect finite pairings. It cites Milne 9.1 in its proof but its statement does not assert equality of scheme-theoretic kernel orders for arbitrary isogenies, including inseparable ones over imperfect fields.
- lem-sfb-dual-isogeny-degree vs lem-sfb-abelian-polarization-calculus: the latter gives normalized difference and dual pullback formulae over algebraically closed fields; it does not state the dual-isogeny degree theorem.
- lem-sfb-dual-isogeny-degree vs lem-sfb-abelian-space-poincare-calculus: the latter constructs the relative dual and its pullback identities but says nothing about degrees or the kernel of a dual isogeny.
- lem-sfb-dual-isogeny-degree vs lem-sfb-polarization-calculus-over-field: the latter's rational Rosati involution needs biduality; it gives no equality of degrees of an arbitrary isogeny and its dual. It is an ancestor, so not used as a proof dependency.
- lem-sfb-dual-isogeny-degree vs lem-sc-isogeny-degree: the latter equates a single isogeny's kernel order with its finite flat rank; it does not compare an isogeny and its dual.
- lem-sfb-dual-isogeny-degree vs lem-sfb-ample-line-polarization-isogeny: the latter makes an ample normalized-difference homomorphism an isogeny, but does not dualize it or compare degrees.
- lem-sfb-dual-isogeny-degree vs lem-sfb-abelian-poincare-biduality: the new node is not evaluation, biduality, uniqueness, or naturality. The item's proof constructs evaluation, establishes the key polarization identity, and cancels equal generic ranks to prove it an isomorphism.

The new node carries no Stacks tag: its source is Milne Theorem 9.1, checked against every same-source candidate above. Existing Stacks facts (056S, 0569 and 0AB1) are cited through existing nodes, not recreated.

## Review by Q29

I read delivery-errors B–E in full, including the repeated copy, with the node statements and Milne text open. The following is my own mathematical review, not an independent second reading.

1. The universal property actually stated in `def-sfb-abelian-dual-poincare-datum` quantifies over every k-scheme T, gives uniqueness of the classifying *map*, includes the identity rigidification and classifies tensor product by sum. I use precisely that for T=A. The swapped family is admissible by `def-sfb-line-algebraic-equivalence`: over each algebraically closed Omega the smooth connected parameter A_Omega connects its fibre at a to its fibre at zero. `lem-sfb-abelian-field-extension` supplies the abelian-variety hypothesis after arbitrary field extension; properness supplies separated finite type. I corrected the initially terse treatment of the second axis: `lem-sc-abelian-variety-characterization` and `lem-pc-h0-proper-variety` imply all its discrepancy units are scalars, and matching at the intersection makes them 1. The comparison therefore respects both compatible identity-axis normalizations, not just an unrigidified Picard class.

2. `lem-sc-rigidity` really states factorization through the second projection when one fibre is constant, with the proper/geometrically connected/geometrically reduced, connected and separated finite-type hypotheses displayed. These hold for U and V by their abelian-variety definition and `lem-sc-abelian-variety-characterization`. `lem-sc-av-commutative` justifies writing the subtraction defect. Writing h(x,0)=h(0,y)=0 and then applying rigidity proves the pointed map is a homomorphism; this does not invoke biduality or assume biadditivity of an unidentified Poincare object.

3. `lem-sc-abelian-variety-projective` expressly supplies an ample line over the original field, not only after algebraic closure. The normalized difference is the real construction in the Poincare datum, and the translation family gives its algebraic-trivial fibre condition directly. Step 2 makes its pointed classifying map a homomorphism. `lem-sfb-ample-line-polarization-isogeny` has exactly those hypotheses and works over arbitrary fields. The new node applies to that isogeny and the two chosen data, giving its dual mu and equal kernel orders. I made explicit the existence and homomorphism property of mu from the representing property and pullback of generating equivalences; the new node is not being used to smuggle in the original biduality conclusion.

4. The crucial equation is mu delta=lambda. Every product map in its displayed pullback chain has the correct factors: P_D lives on D×E, Q on D×A, and the comparison lives on A×A. `lem-pc-module-pullback-identity-composition` gives the composition isomorphisms and `lem-weil-pbc-module-pullback-tensor` distributes pullback across the displayed normalized difference. Commutativity gives m∘s=m, and only the two inverse-line factors exchange. The constant-line factor is retained. A comparison can be normalized along the chosen identity axis by multiplying by the inverse parameter unit; `lem-pc-h0-proper-variety` ensures the other-axis discrepancy is the same scalar determined at the intersection. The defining uniqueness of maps therefore applies. This is a short explicit substitution argument, marked elementary, not a new symmetry lemma node.

5. `lem-sc-isogeny-degree` states that *each* isogeny is finite flat and its direct image has rank equal to its kernel order. The newly cited equality makes both ranks the same positive integer, even for nonreduced kernels. `lem-weil-pbc-finite-permanence-over-separated` explicitly permits finiteness cancellation in mu∘delta, and mu is finite, hence separated. Over F=k(D), the two finite domain algebras become fields of that common finite dimension. The induced unital map M→K is injective and hence bijective by equal dimensions. This proves dominance and birationality of delta, rather than assuming it or using a geometric-point count. The finite-domain-to-field assertion is elementary: a nonzero element acts injectively on a finite-dimensional domain and hence surjectively, so it has an inverse. No separate lemma with new hypotheses is hidden here.

6. `lem-weil-pbc-smooth-scheme-over-field-regular` gives regularity for every smooth k-scheme, `rem-pc-regular-normal` explicitly gives normality, and `lem-trf-finite-birational-normal-iso` has exactly the integral/finite/function-field-isomorphism/normal-target hypotheses established in steps 2 and 5. I read Stacks `varieties.tex` lemma-smooth-regular (056S), `algebra.tex` lemma-regular-normal (0567), and `morphisms.tex` lemma-finite-birational-over-normal (0AB1). An inverse to a group homomorphism that is a scheme isomorphism respects multiplication by composing the multiplication identity with the inverse; uniqueness is the already established representing uniqueness.

7. Naturality is a different displayed pullback chain, on B^vee×A, not an assertion that it 'transports'. Its middle comparison is exactly the switched defining identity for f^vee. The endpoints classify f^{veevee} delta_A and delta_B f by the datum for B^vee with parameter A; the maps are equal by that datum's uniqueness. I added the explicit preservation of algebraic equivalence by pulling back generating families, so the existence of both dual maps does not rely on an unstated general theorem. The only extra tool is ordinary pullback composition; normalization uses the already explained global-unit argument. This is marked elementary as an explicit composition/uniqueness calculation from cited statements and earlier steps.

For the new node I read Milne 9.1, including the general-field qualification and the Cartier-dual kernel description. The order of a finite Cartier dual is the dimension of the linear dual of its finite coordinate Hopf algebra, hence the same integer; that explains the degree consequence recorded here, without reducing to closed points. I tested identity isogenies, multiplication-by-n, the zero-dimensional abelian variety, and Frobenius on an elliptic curve in characteristic p: kernel length, not number of geometric points, gives the correct degree. Imperfect fields cause no extra smoothness or separability assumption in any cited tool. For the item, f=0, identity maps, and composites give the stated naturality equation, including dimension zero. No statement is disputed.

No step exceeds 2000 characters (the longest after review is 1224); I found no hidden comparison left in a long step. The new node is a genuine prerequisite with different hypotheses and conclusion, not a restatement of one clause. The seven-step assembly retains the mathematical work. Existing nodes are reused rather than introducing elementary lemmas. Every `proof_deps` entry occurs in a step, and all step citations have literal quotes in `citations.json`.

## Unfinished work

No unfinished part of the assigned split. The new statement-only degree prerequisite is intentionally left unsplit for the next stage-1 worker; it has its full hypotheses, literature place and actual Mathlib searches.
