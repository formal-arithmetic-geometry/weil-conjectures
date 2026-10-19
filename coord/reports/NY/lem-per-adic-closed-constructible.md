# Stage-1 delivery: lem-per-adic-closed-constructible

Group NY; direct worker delivery; 2026-10-18. Only stage 1 was performed. The statement is unchanged.

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-adic-closed-constructible.json`: statement, split into nine proof steps; not in Mathlib.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-finite-tor-internal-hom-any-field.json`: statement-only, unsplit; finite-coefficient internal-Hom finiteness with finite Tor amplitude over arbitrary ground fields; not in Mathlib.
- This report. The sandbox also contains citations.json, searches.jsonl, the source-text extraction, and the sandbox-only editing script; these are research/validation material rather than extra DAG nodes.

## Attachments

None. Searched the slopmaster2 project under WeilConjectures for the exact item tag and for adic/constructible internal Hom and tensor terminology. The integral completed category, its internal-Hom preservation, and its scalar-extension coherence are not supplied by a single closed project declaration. Read Etale/Derived/Hom.lean, the finite-coefficient Hom results in Etale/Derived/Stability/DirectImage.lean and Matrix.lean, and the ProEtale/Derived and Adic internal-Hom search results. `AlgebraicGeometry.Etale.constructibleFiniteTor_derivedHom` is an etale finite-coefficient result, whereas the new node states pro-etale finiteness; the pro-etale Matrix comparison theorem assumes the fixed algebraic closure of a finite field. None is an exact attachment for this item or new node. No compiler, Lake, or git command was run in the read-only repositories.

## Literature

WANTED: none for this delivery. Read the local Bhatt–Scholze PDF, particularly Definition 3.4.10, Lemma 3.4.11, Proposition 3.5.1, Definition 6.5.1 and its following comparison paragraph, Lemmas 6.5.3–6.5.5, Proposition 6.6.11, and Lemmas 6.7.11–6.7.13. Read the local Stacks ringed-site internal-Hom statements at Tags 08J9 (`lemma-internal-hom`) and 08JA (`lemma-section-RHom-over-U`). The proof is marked agent-origin: it expands the reduction-bound induction and the canonical tensor/scalar coherence beyond the source's abbreviated argument. No SGA source or SGA route is used.

The new node follows Bhatt–Scholze 6.7.13 with the complete local coefficient ring replaced by the finite local ring O_E/varpi^n, with its nilpotent maximal ideal. The finite-Tor hypotheses preserve the source's perfect-on-strata constructibility convention. This is not the assertion for arbitrary bounded complexes over a nonregular finite ring. No exact Stacks tag for this finiteness theorem was found; the source is explicitly Bhatt–Scholze, not a misassigned Stacks tag.

## Problems found and corrections

The imported item had an empty proof. Its statement is correct, and no hypotheses or conclusions were changed. In particular “any field” includes characteristic zero; this prevents using the positive-characteristic condensed-coefficient lemmas without an additional result. The integral coefficient sheaf remains the completed sheaf, not the discrete constant ring. The explicit tower definition of completed tensor needs a comparison with completion of ordinary tensor; Step 2 proves that comparison from its actual representatives.

A separate boundedness proof for each finite quotient would not establish the uniform reduction interval in the category's definition. Step 5 instead uses the exact sequence 0 -> R/varpi -> R/varpi^n -> R/varpi^(n-1) -> 0, tensoring one flat-term K-flat representative of H, and inducts with the same interval at every n. This avoids importing a global-field Tor bound into an arbitrary-field argument.

The statement of the integral scalar-operations lemma provides isomorphisms and tower compatibility, but does not by itself specify evaluation normalization in its displayed Hom clause. Step 8 uses the existing, explicitly evaluation-transposed finite-free ringed-site Hom theorem; its tensor formula is checked on representatives and completion. Step 9 writes the tower and adjunction compatibility calculation, rather than using an unspecified isomorphism or the proof of the scalar lemma as a black box.

No chapter or unit record is changed: this is an auxiliary descendant of lem-per-artin-gabber-affine-curve through lem-per-qbar-arbitrary-field-duality, not the key node realizing the curve-perverse unit's statement. Generic off-unit tools are declared in split_report.tool_uses; they supply coefficient, ringed-site, homological, and constructibility inputs, without replacing the unit's geometric argument.

## Unfinished work

The single new finite-coefficient lemma is intentionally statement-only and joins the queue. No proof of it is hidden in its statement. No other part of the assigned split is left open.

## Searches and reuse

Read all nine search responses recorded by msearch.py in this sandbox. Searches used LeanFinder with two finite-coefficient phrasings, LeanSearch, Loogle, and source grep; the item's searches also used an adic closed-category phrasing. Exact queries and result digests are retained in mathlib_searches. No service was unavailable in these searches. LeanFinder returned scheme-morphism constructibility and finite-type results, while LeanSearch returned ordinary sheaf Hom and categorical closedness. Read the plausible light-condensed closed structure in Mathlib/Condensed/Light/Monoidal.lean and the reflective closed-category theorem in Mathlib/CategoryTheory/Monoidal/Braided/Reflection.lean. Neither identifies the complete constructible pro-etale category or proves its finiteness assertion. Loogle's constructible hits concern subsets, and its TorAmplitude search and both targeted source greps returned no hits.

Searched the whole DAG by internal Hom, finite Tor, finite-free change of rings, residue-field and source lemma numbers; used blueprint_refs.py ancestor and whole-blueprint search, including “6.7.12”, “6.7.13”, “internal Hom finiteness”, “finite Tor”, “internal sheaf”, and “finite coefficient internal Hom”. Read the statements of all cited nodes. In particular reused lem-sf-ringed-finite-free-hom-base-change and lem-weil-finite-free-completed-scalar-comparison instead of creating scalar-comparison nodes.

## Not duplicates

lem-per-finite-tor-internal-hom-any-field vs lem-sfb-finite-field-internal-hom-finiteness: the existing node assumes positive characteristic and only a finite coefficient field; the new node permits characteristic zero and all O_E/varpi^n, with finite Tor amplitude explicitly required for nonfield coefficients.

lem-per-finite-tor-internal-hom-any-field vs thm-sf-hom-ctf: the existing node fixes the algebraic closure of a finite field and the etale site, and additionally gives a numerical Tor interval; the new node covers the pro-etale site over any ground field, and asserts bounded constructibility only.

lem-per-finite-tor-internal-hom-any-field vs sk-thm-sf-hom-ctf: this imported blueprint node uses the standing finite-field setting and the etale site with a numerical interval; it does not supply the arbitrary-field pro-etale result.

lem-per-finite-tor-internal-hom-any-field vs lem-trf-proetale-internal-hom-ctf: the existing node fixes k as the algebraic closure of a finite field; the new node does not, including characteristic-zero bases. No added Tor-output conclusion is used from the existing node.

lem-per-finite-tor-internal-hom-any-field vs det-rem-sf-matrix-hom-devissage: the existing node assumes a separably closed ground field and states an etale result; the new node has neither that field hypothesis nor that site restriction.

lem-per-finite-tor-internal-hom-any-field vs lem-sfb-dc-hom-preserves: the existing node concerns condensed integral/rational/algebraically closed coefficients in positive characteristic, not arbitrary-field finite constant coefficients.

lem-per-finite-tor-internal-hom-any-field vs lem-sfb-dc-hom-single: the existing node is a single-sheaf condensed-coefficient result in the positive-characteristic setting; the new one concerns bounded finite-coefficient complexes on arbitrary-field pro-etale sites.

lem-per-finite-tor-internal-hom-any-field vs lem-sfb-constructible-internal-hom-continuity: the latter is a filtered-colimit comparison for ordinary condensed integral/rational coefficients, not finite-coefficient internal-Hom finiteness.

lem-per-finite-tor-internal-hom-any-field vs lem-sfb-open-closed-internal-hom-formulas: the latter gives formal open/closed internal-Hom identities and explicitly asserts no constructibility preservation. It does not supply this finite-coefficient theorem.

lem-per-finite-tor-internal-hom-any-field vs lem-per-adic-closed-constructible: the new node is a finite-coefficient theorem with finite Tor hypotheses, not a restatement of integral preservation, completed adjunction, or scalar compatibility. The parent proves those by residue comparison, completeness, uniform reduction bounds, the completion reflector, and finite-free scalar extension.

## Review by NY

I read the item's Bhatt–Scholze source and the relevant parts of the current blueprint ancestor's Step 3. The ancestor uses duality for the lower perverse bound; this split supplies the closed integral operation required by the already split arbitrary-field duality node. It does not attempt to repair or reroute the ancestor's other geometric claims. For the new finite-coefficient node I checked the coefficient-ring specialization of 6.7.13 and Definition 6.5.1, including the finite-Tor/perfect-on-strata qualification. Finite type over a field gives the quasi-excellent, Noetherian, finite-dimensional domain needed by that source; invertibility of ell is retained. The new node makes no unjustified claim for arbitrary bounded torsion complexes over a nonregular coefficient ring.

In Step 1 the actual DVR node supplies the residue field and Noetherian DVR assertion; the constant-completion equivalence supplies flatness and the quotient identifications. The noetherian finite-type and finite-dimension statements apply to T over Spec k. The stratified-perfect characterization explicitly applies to the same complete integral category, so its one-stratum model really supplies the unit. I did not identify different coefficient categories by notation.

In Step 2 the reflector statement gives the needed bijection for maps INTO complete objects, and the constant-completion statement identifies the Koszul and quotient-tower units. The integral-operation definition actually gives the strict reduction tower being compared. The written balancing maps are inverse on pure tensors, commute with differentials and transitions, and therefore identify the completed tensor constructions. No definition node is being cited for an unasserted comparison theorem.

In Step 3 the integral Hom reduction statement explicitly applies to arbitrary ambient inputs, asserts completeness when the second input is complete, and specifies the comparison as evaluation-defined. Thus neither constructibility of H nor site-perfectness of P is presumed. The integral category definition supplies the bounded residue reductions, and the DVR node makes the residue coefficient a field. Step 4 uses precisely the new node's bounded finite-Tor pro-etale conclusion; its ground-field hypothesis is verified for the given k, including characteristic zero.

In Step 5 I checked the coefficient short exact sequence on the DVR, and the triangle node states exactly that a short exact sequence gives a distinguished triangle. A flat-term K-flat representative justifies tensoring it. The long-exact-cohomology node supplies the induction, the discrete Noetherian constructible-Serre node applies to each finite A_n, and the finite-ring etale-origin node turns intrinsic bounded constructibility into the etale-origin condition required here. There is no n-dependent degree enlargement. The final category definition requires completeness AND all these reductions with one interval; both have now been proved.

In Step 6 the tensor-preservation node really states closure in the complete constructible category. The reflector, internal currying, and H^0-of-internal-Hom nodes together give the asserted Hom bijection; the currying node alone is not silently used as a global-Hom result. Step 7 writes the removal of an intermediate completion using the completeness conclusion of the Hom reduction node and the reflector bijection; the constraints descend from the actual tensor maps. It verifies coherence by the injectivity of these universal bijections, not by an unproved claim that completion automatically preserves every tensor product.

In Step 8 the finite-free completed scalar comparison states that the completed coefficient sheaf is finite free and that ordinary tensor is the actual integral scalar functor on complete inputs. The ringed finite-free Hom node applies to arbitrary complexes and explicitly normalizes its comparison by evaluation. The constructibility-preservation node gives the target integral objects. The pure-tensor formula checks that the specified tensor comparison is the one used, rather than inferring evaluation compatibility from the existence of some isomorphism. In Step 9 the two tower routes evaluate to h(p) multiplied by the same product ss'u'; uniqueness of transpose gives equality. The identity case and the formula for an arbitrary adjunction arrow are both written out. No rational-only composition assertion is used for integral coherence.

I checked delivery-errors B–E against the written files: the new node introduces all its objects and is statement-only; its notions cite the actual definitions; its source is the local PDF and exact lemma rather than a guessed tag; searches were run and read. The duplicate comparison above distinguishes the available narrower hypotheses. Every proof citation is a node whose statement supplies what is used, and citations.json records exact statement text for each uses entry. I checked the merged dependency closure for a path back to the item and found none. There is no child that restates an integral clause or carries the entire assigned theorem. Every proof step is below 2000 characters. The two short new identifications (the tensor tower and the intermediate completion) are proved directly from the cited universal properties, rather than hidden as “standard” lemmas.

Small cases checked: T empty, P or Q zero, E=Q_ell, n=1, n=2, nonperfect positive-characteristic k, characteristic-zero k, ramified finite L/E, and identity/two successive coefficient extensions. At a geometric point, integral objects include R/varpi with its two-term residue reduction; the proof does not incorrectly force that reduction into degree zero. For nonregular A_n the new node retains finite Tor assumptions, so a nonperfect residue-field module is not an unintended counterexample. For H_1=0 the induction gives every reduction zero and uses the harmless interval [0,0]. Ramification is handled by the existing completed finite-free comparison, not by identifying powers of different uniformizers.

## Validation

Required command `python3 /home/ubuntu/weil-launcher-nt/deliver.py NY lem-per-adic-closed-constructible --no-push` exited 0 and printed `OK (not pushed) deliver/NY/lem-per-adic-closed-constructible at ca313b8b71: preflight passed`. This validates the DAG and split through the server preflight. A final dry run is performed after recording this evidence, followed by the authorized direct push; the delivery command reruns its gates. One new unsplit node, zero Mathlib leaves. No Lean or compilation work was performed.
