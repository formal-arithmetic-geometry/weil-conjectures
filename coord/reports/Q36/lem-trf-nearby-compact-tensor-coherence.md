# Worker report: lem-trf-nearby-compact-tensor-coherence

1. Files written: `dag/nodes/sec-trace-formula/lem-trf-nearby-compact-tensor-coherence.json`: statement, split into fourteen proof steps; Mathlib searches do not match the geometric theorem. `citations.json` quotes every cited statement, including the full interfaces where several clauses are used. No new nodes, no Mathlib leaves, no unit edits.
2. Attachments: none. Searched the read-only slopmaster2 project for the exact blueprint tag, nearby-cycle notions, and compact-support exchange; no exact project declaration was found. The item has no attached Lean audit declaration to reuse.
3. WANTED: none. Varshavsky, the Stacks source files, and the cited abstract interfaces are present. The existing flat-model and enriched-derived-calculus nodes remain agent-formulated foundational obligations whose source records request further references; this split uses their statements and does not certify their proofs. The unbounded/general-trait argument is explicitly agent-origin; Varshavsky alone only states the bounded constructible finite-Tor specialization package.
4. Problems in the imported item: no statement correction was required. Its proof was empty. Its reference to the deformation-specialization definition is a normalization of the formula, not evidence that that definition already constructed the whole unbounded functor. The split uses the separate unbounded compact-support theorem to extend that formula. A geometric generic point is not an open immersion. The closed fibre of the finite total-space map is not generally the ordinary closed fibre over the extended trait: it is a nilpotent thickening, treated explicitly in step 13.
5. Unfinished: no clause of this one-level split remains unaccounted for. Existing unsplit interfaces remain existing DAG obligations, not new duplicate nodes.

## Sources and searches

Read `literature/varshavsky-lefschetz-verdier-trace-formula_arXiv-math0505564.pdf` as text: 1.3.1(e), 1.3.2(b)--(c), 1.3.3(a), 4.1.3(I)--(IV),(VI), and 4.1.4(b). Read the current main-20261015 ancestor proof `sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md`: its normal-cone argument calls for this specialization input before duality. Also read the chapter and unit records and SETUP's three levels; this delivery changes neither unit nor chapter route.

Read Stacks `more-etale.tex`, Tags 0F7J (`lemma-shriek-composition`) and 0F7L (`lemma-base-change-shriek`), including the proper/open construction and its compatibility requirements; `etale-cohomology.tex`, Tags 0F09 (`lemma-smooth-base-change-general`), 0F0C (`lemma-proper-base-change-mod-n`) and 04DZ (`theorem-topological-invariance`); and `sites-cohomology.tex`, Tags 07A4 (`lemma-pullback-tensor-product`), 0D6E (`lemma-derived-pushforward-composition`) and 0E48 (`remark-compatible-with-diagram`). In particular 0F09 is not used as an unbounded smooth-exchange theorem. The cited bounded-constructible smooth theorem is sufficient for precisely the clause requested.

Whole-DAG searches included the tags 0F7L, 0F7J, 0F09, 04DZ, and phrases for monoidal mates, projection/exchange, finite trait changes and derived cone models. Whole-blueprint searches with `tools/blueprint_refs.py` used `nearby`, `tensor coherence`, and `specialization`; none states this item in another form. The ancestor command identifies `lem-trf-local-term-locality`. Existing general ordinary-etale tools cover all the needs; restricted pro-etale and bounded-below nearby-exchange nodes were read but not used to justify broader claims.

The Q36 `msearch.py` log contains one grep, one Loogle, one LeanSearch and two differently phrased LeanFinder queries. Read all hits: the Loogle results are normed-ring units; LeanSearch finds general lax monoidal composition and right-adjoint monoidal structures; LeanFinder finds underived sheaf/presheaf pullback composition and counit identities. Those tools are useful abstractly but do not state the nearby-cycle compact-support package, and are not an attachment. All five calls succeeded. Existing Q86 searches in the imported item are retained verbatim; the Q36 calls are appended exactly as logged. No new node required a separate search.

## Not duplicates

No new nodes. The potentially reusable nearby-cycle-finiteness node assumes the special deformation trait and bounded inputs; the restricted pro-etale compact-support-counit node also has different domains. They are neither substitutes for this statement nor grounds for adding a duplicate. Existing generic monoidal, compact projection/exchange, proper torsion base-change and topological-invariance nodes are cited directly.

## Review by Q36

I checked the actual item and every cited statement against the domains of the proof, not merely their names. The finite ring is held constant, all functors here use small etale module sheaves, and no pro-etale/condensed equivalence is silently substituted. The finite torsion-ring proper theorem and the unbounded compact comparison theorem permit arbitrary unbounded inputs. The source's bounded-constructible restriction is used only where the item itself asks for smooth invertibility. Neither lax nearby tensor nor any projection map is declared invertible.

1. Exact inverse image, its tensor isomorphism and the monoidal composition theorem supply the left-adjoint data. The two monoidal-adjunction statements actually provide the right-adjoint lax structure and monoidal counits. The formula given here specifies the same tensorator as Varshavsky; there is no implicit tensor-isomorphism assumption.

   Cited statements: `prop-weil-pbc-inverse-image-modules-exact`, `lem-kun-inverse-image-monoidal`, `lem-kun-derived-pullback-composition-monoidal`, `lem-sfb-monoidal-adjunction-mates`, `lem-sfb-monoidal-adjunction-unit-counit`. Each was opened and its used formula or clause is included verbatim in `citations.json`.

2. Nagata applies to separated finite-type maps over the given qcqs bases. The finite-type-over-Noetherian statement verifies the schemes are in the domain of the unbounded compact-support comparison theorem. That theorem explicitly supplies both the exchanges and refinement independence. The deformation definition supplies the exact normalization, not the unbounded extension. The displayed transpose defines d_u using the ordinary adjunction in the projection-map definition. I checked its direction and every source and target.

   Cited statements: `thm-nagata-compactification`, `lem-weil-pbc-finite-type-over-noetherian`, `lem-amb-unbounded-compact-support-comparisons`, `def-trf-deformation-specialization`, `def-kun-projection-formula-map`. Each was opened and its used formula or clause is included verbatim in `citations.json`.

3. The flat-model statement characterizes cofibrations by K-flat flat-term cokernels, so exactness and preservation of those cokernels prove the Quillen hypothesis directly. The pullback/tensor statement explicitly preserves K-flat complexes with flat terms. The enhanced derived calculus then supplies enhanced units, counits and mates. This avoids citing the bounded-below filtered-lift lemma for arbitrary unbounded complexes.

   Cited statements: `lem-coef-sheaf-flat-model`, `prop-weil-pbc-inverse-image-modules-exact`, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, `lem-coef-dg-derived-quillen-calculus`. Each was opened and its used formula or clause is included verbatim in `citations.json`.

4. Extension by zero is exact, and the open tensor node states the underived comparison from which its unbounded comparison is derived. Applied to acyclic complexes this proves preservation of K-flatness, giving the remaining Quillen input. The enhanced calculus is used only for these concrete sheaf functors and adjunction maps, not to lift an arbitrary triangulated natural transformation. Compact comparison supplies the normalized equivalences inverted here. Cone/shift compatibility is in each tensor variable separately.

   Cited statements: `lem-weil-pbc-extension-by-zero-exact`, `lem-pur-etale-open-derived-tensor`, `lem-coef-sheaf-flat-model`, `lem-coef-dg-derived-quillen-calculus`, `lem-amb-unbounded-compact-support-comparisons`. Each was opened and its used formula or clause is included verbatim in `citations.json`.

5. Derived direct-image composition is explicitly unbounded. Proper torsion-ring exchange has no lower bound on E. Its application to i and the total proper u yields the correct ordinary exchange. Mate pasting and the displayed transpose identify the compact map with its inverse, not merely some isomorphism of the same endpoints. This is the proper base-change calculation of 1.3.2(c).

   Cited statements: `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`, `lem-kun-proper-base-change-torsion-ring`, `lem-weil-pbc-mate-pasting`, `lem-amb-unbounded-compact-support-comparisons`. Each was opened and its used formula or clause is included verbatim in `citations.json`.

6. The bounded-constructible smooth theorem places smoothness on the inverse-image edge, as required for the u versus geometric-generic inclusion square. The latter edge is affine and therefore qcqs. A power of ell kills A and is invertible on the base because ell differs from p. No constructibility of the nearby-cycle output is inferred. Field pullback composition needs no smoothness.

   Cited statements: `sbc-thm-bounded-derived-smooth-base-change`, `lem-kun-derived-pullback-composition-monoidal`. Each was opened and its used formula or clause is included verbatim in `citations.json`.

7. The mate-pasting statement supplies its actual two pasting formulas and identity formula. The compact-support comparison statement supplies compatibility with both composition and change of base. I transposed the two possible compact-support composites and checked that the intervening unit and counit cancel. Hence the statement has exactly the requested order C_v after Rv_!C_u, including identity and inverse maps.

   Cited statements: `lem-weil-pbc-mate-pasting`, `lem-kun-derived-pullback-composition-monoidal`, `lem-amb-unbounded-compact-support-comparisons`. Each was opened and its used formula or clause is included verbatim in `citations.json`.

8. The monoidal-adjunction statement really asserts monoidality of the counit, and the inverse-image composition theorem supplies monoidality of the pullback identifications. Transposition reduces the tensor identities to the tensor of the source counits. The counit formula for e is its mate characterization, with b evaluated at Ru_*M. This is a direct diagram chase from the cited statements, not a new geometric monoidality lemma.

   Cited statements: `lem-sfb-monoidal-adjunction-unit-counit`, `lem-kun-derived-pullback-composition-monoidal`, `lem-weil-pbc-mate-pasting`, `def-kun-projection-formula-map`. Each was opened and its used formula or clause is included verbatim in `citations.json`.

9. The compact projection/exchange node explicitly allows arbitrary unbounded M and Q and arbitrary Noetherian base change. Thus it applies to i, the geometric generic point, and field extension. The symmetric tensor constraint changes its left-factor convention to the statement's convention. Multiplication by the inverse exchange gives the field-extension formula with C, with no inversion of the projection map.

   Cited statements: `lem-asd-compact-projection-exchange`, `lem-kun-tensor-sym`, `lem-amb-unbounded-compact-support-comparisons`. Each was opened and its used formula or clause is included verbatim in `citations.json`.

10. The same compact projection/exchange and monoidal-counit identities reduce both transposes to the displayed PF_h followed by the two counits. I checked that its source is Rh_! of the generic restriction of Rj_X*M tensored with the generic restriction of Rj_Y*N. Its target is Rh_!(M tensor h*N), so this proves the full mixed nearby/projection identity, including b. Applying i and its projection exchange yields the requested final source and target.

   Cited statements: `lem-asd-compact-projection-exchange`, `lem-sfb-monoidal-adjunction-unit-counit`, `def-kun-projection-formula-map`, `lem-weil-pbc-mate-pasting`. Each was opened and its used formula or clause is included verbatim in `citations.json`.

11. The strict-henselian statement equates sections with the stalk for every sheaf; since stalks are exact, this also computes the derived value. The separably closed point theorem computes higher cohomology, and unbounded direct-image composition identifies the resulting global sections. The constant section unit sends a to a. For q, the exact inverse-image statement includes the canonical constant-ring identification.

   Cited statements: `lem-weil-pbc-strictly-henselian-sections-stalk`, `lem-kun-0ezp`, `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`, `prop-weil-pbc-inverse-image-modules-exact`. Each was opened and its used formula or clause is included verbatim in `citations.json`.

12. The surjective-closed-immersion statement gives a universal homeomorphism; the site-equivalence statement gives the equivalence of etale sites. Exact inverse image and monoidal tensor then transport ordinary module adjunctions. The compact comparison theorem and mate pasting identify the actual maps. I explicitly allowed nonreduced special fibres, since reduced total space need not have reduced special fibre.

   Cited statements: `lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism`, `lemma-weil-pbc-universal-homeomorphism-site-equivalence`, `prop-weil-pbc-inverse-image-modules-exact`, `lem-kun-inverse-image-monoidal`, `lem-amb-unbounded-compact-support-comparisons`, `lem-weil-pbc-mate-pasting`. Each was opened and its used formula or clause is included verbatim in `citations.json`.

13. Finite-proper supplies properness of r, and the proper torsion-ring theorem applies to the unreduced Cartesian closed fibre. Writing t=vs^e exhibits its nilpotent thickening explicitly. Residue fields agree since the extension is finite and the original residue field is algebraically closed. The DVR definition also states the discrete value-group description, which gives t=vs^e with e positive for this local dominant map. The closed-immersion and etale-equivalence nodes remove the thickening. Compatible geometric generic points identify the other fibre; no separability or unramified hypothesis is inserted.

   Cited statements: `lem-weil-pbc-finite-proper`, `lem-kun-proper-base-change-torsion-ring`, `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`, `lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism`, `lemma-weil-pbc-universal-homeomorphism-site-equivalence`, `def-sc-discrete-valuation-ring`. Each was opened and its used formula or clause is included verbatim in `citations.json`.

14. The compact comparison theorem gives tower coherence for B, pullback composition gives tensor coherence, and the mate-pasting formula identifies units and counits in pasted diagrams. The explicit transpose for C checks compatibility of the canonical arrow under finite trait extension. The same two existing composition laws handle towers of separably closed extensions. This completes the maps clause as well as the objects clause.

   Cited statements: `lem-weil-pbc-mate-pasting`, `lem-amb-unbounded-compact-support-comparisons`, `lem-kun-derived-pullback-composition-monoidal`, `lem-sfb-monoidal-adjunction-unit-counit`. Each was opened and its used formula or clause is included verbatim in `citations.json`.

No new statement was introduced. I tested the argument on identity maps, empty schemes and zero complexes, a point over the base field, and a ramified trait extension t=s^e with e>1. Identities reduce to adjunction triangles; zero and empty cases give the zero maps; the point gives the identity on A; ramification forces the nilpotent thickening handled in step 13. The coefficient A=Z/ell^2 also illustrates why arbitrary derived tensors may be unbounded below and why a finite-Tor shortcut would not justify this item.

During self-review I corrected the wording of the inclusion in step 13: Z_0 itself need not be reduced, so it is called a canonical closed inclusion, not a reduced inclusion. No node statement changed. Every proof step is below 2000 characters (maximum 1156); the projection argument is a single two-counit transpose calculation, not an unspecified standard comparison. Generic off-unit interfaces are declared in split_report.tool_uses with their use, since the local-term unit does not restate these general tools. No SGA route, new purity theorem, Lean edit, compiler, or build was used.

## Validation

The first required server dry run exited successfully: `OK (not pushed)` at `8dcbf3c6a9`; server preflight passed. After that check I added the already-existing DVR definition to the trait calculation and its citation to make the uniformizer convention explicit. A final dry run and direct push follow for these final files.
