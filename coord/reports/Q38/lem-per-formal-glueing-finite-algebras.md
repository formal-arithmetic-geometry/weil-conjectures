## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-formal-glueing-finite-algebras.json`: statement, split into six steps; Mathlib searches found no match. Statement unchanged.
- `citations.json`: exact statement text for every proof-step citation.
- No new nodes; no Mathlib leaves.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` by the blueprint id, `formalGlue`, `FormalGlue`, `formal_glu`, `glueing`, `formal gluing`, and `finite algebra`. The relevant hits concern finite algebras in other settings or projective-space transition units, not this theorem. No project declaration proves the item. The upstream master searches likewise produced no attachment. Existing `lean` fields on the reused DAG tools are not being claimed as new attachments.

## WANTED

None.

## Findings and corrections

The item is a correct consequence of Stacks Tags 05ER and 05EU, whose source text was read in `literature/stacks-project/more-algebra.tex`. Tag names were checked against `tags/tags`: 05ER is proposition-equivalence; 05EU is remark-formal-glueing-algebras; 05EK is lemma-recover-module-from-glueing-data; 05EL is remark-glueing-data. I retained the statement and source. I added explicit base-change and localization definition dependencies already implicit in its notation.

The imported item had no proof. Simply citing the last sentence of 05EU as an algebra-category equivalence would hide the algebra-structure argument. Instead the proof constructs the subring of matching tuples and uses only the existing module equivalence, matching-module exactness, and finite-module detection. This avoids creating a node restating the item, or a new abstract monoidal transport theorem. No new definition is needed for this one-off subring construction: its objects and operations are specified directly.

The current blueprint unit and chapter were read, as were the current main-20261015 ancestor proof and the existing DAG ancestor. The inherited provenance mentions a reverse-completion/Ratliff argument that is a lower branch added during splitting, not literally the current ancestor proof's Step 3. I preserved that recorded ancestry and via list and made the split report explicit about the intervening conormal-algebraization Step 4 and Stacks 0ALR. No chapter or unit route is replaced and no unit realization file is changed.

## Searches and existing tools

I searched the whole DAG for 05ER, 05EU, their TeX labels, finite-algebra formal gluing, and matching-subring terms, and ran `tools/blueprint_refs.py ancestor` for the item and `search` for `formal glueing finite algebras`, `formal`, `glueing`, and `gluing`. None is a blueprint statement duplicating this item. The relevant existing nodes are:

- `prop-weil-pbc-formal-glueing-equivalence`: modules, including essential surjectivity, not algebraization as algebras.
- `lem-weil-pbc-formal-glueing-complex-exact`: injectivity and exactness of the canonical matching complex, not algebraization.
- `lem-weil-pbc-formal-glueing-finite-modules`: detection of module finiteness, without constructing an algebra.
- `def-weil-pbc-formal-glueing-data`: actual canonical maps and morphism equations used in the checks.

The three statement nodes are general commutative-algebra tools filed in another unit. Their use is declared in `split_report.tool_uses`, with reasons; I do not set the maintainer-owned `tool_uses` field. They implement exactly the 05ER/05EU input already named by this item's source, rather than replacing its unit route.

I retained all original Mathlib-search records. The sandbox initially contained no node, report, or searches. I ran the required wrapper searches for Q38: LeanFinder in two phrasings, Loogle, grep in RingTheory, and LeanSearch. I read the returned declarations and types. Finite-type skeleton existence, Noetherian descent of smooth algebras, open-cover finite presentation, complete-ring completion equivalences, and ringed-space GlueData do not assert this statement or a one-line generalization. The localization gluing hit assumes an open cover generating the unit ideal and does not supply the S-component formal gluing asserted here. All wrapper calls succeeded, and the appended search records reproduce the actual logged query texts and results. No claims of a Mathlib leaf are made.

## Review by Q38

I read 05EU's finite-module and tensor/algebra sentences together with the full statements and constructions in 05ER, 05EL and 05EK, and opened the statement of every cited node. There are no new-node sources to audit. Here is the mathematical reading of each step.

1. The exact essential-surjectivity clause of `prop-weil-pbc-formal-glueing-equivalence` supplies an R-module M and an isomorphism of canonical module data with the given underlying datum. This is all that the step takes from the proposition; it does not attribute an algebra structure or a specified H^0 counit to that proposition. Its hypotheses are precisely a flat map and R/K = S/KS. The statement of `def-weil-pbc-formal-glueing-data` gives the equations for this isomorphism and its inverse, and its componentwise identities make the component maps bijective. The algebra-map hypothesis in our item guarantees the underlying module datum is the specified object.

2. Both sides of each defining equation for D are ring-homomorphism images. I checked closure under products, unit, sums, negatives and the image of R directly; commutativity is coordinatewise. This is elementary from the given algebra maps and does not assume an abstract tensor structure on Glue. The projection maps preserve all operations by construction. The products are finite (t is a natural number), including t=0.

3. `lem-weil-pbc-formal-glueing-complex-exact` states exactly that the diagonal M-to-product map is injective and its image is the kernel of the displayed difference map. It is applied to M, not to an unknown ring. The canonical matching conditions in that kernel become the specified conditions for D through the component isomorphisms. I checked both directions using the morphism equations in `def-weil-pbc-formal-glueing-data`: the inverse is also a gluing morphism. Thus the asserted module isomorphism lambda follows from the cited exactness, with no assumption that the equivalence node itself states H^0 is a quasi-inverse.

4. `def-weil-module-base-change` supplies the induced linear maps and their composition/identity rules; `def-weil-pbc-module-localization-away` supplies fractions, their equality relation and localization maps. On their generators the proposed maps q' and q_i agree with a' and a_i after lambda. Applying the same operations to lambda inverse proves their bijectivity. Multiplicativity is separately checked by the displayed product formulas, rather than assumed from the linear maps a' and a_i (which need not be algebra maps). The S action and R_fi action agree with the given algebra structures. The image of f_i is invertible in E_i because E_i is an R_fi-algebra, so the localized formula is well-defined even when a localization is the zero ring.

5. I checked the precise prime-chart and chart-chart squares from `def-weil-pbc-formal-glueing-data`. The first displayed equality follows from the defining equation for d and S_fi-linearity. The second follows after multiplying by the inverses of both f_i and f_j on the common overlap. These are actual computations on all localized generators and pure tensors, not an assertion that compatibility transports automatically. The same computations hold for i=j and when one of the localizations is zero. Inverses of bijective algebra maps preserve the operations, so the component isomorphisms are indeed algebra isomorphisms of the requested datum.

6. The statement of `lem-weil-pbc-formal-glueing-finite-modules` is exactly the required iff under the same flatness and quotient-isomorphism hypotheses. Applying its reverse direction to the constructed D uses the finite S-module E' and finite R_fi-modules E_i through q' and q_i. Pulling finite generating families back along these module isomorphisms is elementary. No finite presentation, Noetherian, faithful-flatness of R to S alone, or completion hypothesis is added.

For B1-B10, there are no new nodes at all, no unrun searches, no imported proofs or declarations being claimed as closed, and the item blueprint ancestry and same_as search were retained/checked. For C1-C8, the only substantive inputs are the three cited module statements above, each used only for its stated clause; all definition citations were opened, every proof-step citation has an exact quote, and the off-unit statement uses are declared as tools. For D1-D5, the proof carries the ring construction and overlap checks itself instead of moving its clauses into new nodes; it does not use the proof of a cited node, nor any source's omitted algebra argument as a black box. For E1-E7, the hypotheses are verified at steps 1, 3 and 6, and all identifications are the explicit canonical ones at steps 3-5. There is no statement dispute or source error.

Small cases checked: t=0 makes K=0 and forces R to S to be an isomorphism; D is E' with the restricted R-algebra structure and all chart requirements are empty. If all f_i=0, all chart algebras are zero and the same reduction holds. If a generator is a unit, its chart recovers the whole ring/module, so the matching equations still give the claimed comparisons. If R=0, S and all unital algebras in the data are zero. Zero component algebras are allowed and all constructions remain unital, including the zero algebra. No f_i is assumed to be a nonzerodivisor. All six steps have fewer than 2000 characters, and I checked that none hides a separate comparison lemma: step 3 directly applies an existing exactness statement, and steps 4-5 give the maps and the generator calculations.

## Unfinished work

None in the one-level stage-1 split. The existing cited tools retain their own downstream work; no Lean was written, compiled or built.
