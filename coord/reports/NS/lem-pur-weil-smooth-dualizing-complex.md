# Stage-1 delivery: lem-pur-weil-smooth-dualizing-complex

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-weil-smooth-dualizing-complex.json: statement, split into four steps, using existing nodes only; not a Mathlib leaf.
- citations.json: one verified verbatim statement excerpt per step/node citation.
- report.md: this report. searches.jsonl contains the actual msearch results. No new DAG nodes, no new Mathlib leaves, no unit changes.

## Attachments

None. The project declaration AlgebraicGeometry.WeilComplex.nonempty_dualizingComplex_iso at lean/WeilConjectures/WeilSheaf/VerdierDual.lean:196 has a sorry at line 201. Searching the entire WeilConjectures tree for the item tag and declaration found its call in VerdierDualLocalization, not a finished proof of the item. The finite-coefficient etale dualizing isomorphism is a different assertion.

## WANTED

None: all material used is available locally. No SGA source is used.

## Statement corrected

STATEMENT-DISPUTED: the imported statement identifies the category of def-weil-weil-sheaf-complex with Lean `WeilComplex k₀ ℓ X`. They are different categories. The former explicitly defines Frobenius-fixed pairs over a geometric derived category and explicitly denies being a derived category of Weil sheaves. The latter is a full subcategory of the derived category of pro-etale Weil sheaves, as lean/WeilConjectures/WeilSheaf/Category.lean:61-76 explicitly states.

Here is a point test: let X₀ = Spec(k₀) and let Λ = Qbar_l with trivial Frobenius. A two-dimensional Jordan block with Frobenius matrix [[1,1],[0,1]] defines a nonsplit extension of the trivial Weil sheaf by itself: an invariant splitting would be a vector projecting to 1 and fixed by that matrix, which is impossible. It therefore gives a nonzero Ext¹ and a nonzero morphism Λ → Λ[1] in the derived category of Weil sheaves. In the fixed-pair category every such morphism has underlying morphism in Hom_D(Spec(k),Λ)(Λ,Λ[1]) = 0. Thus these categories cannot be identified as asserted while preserving the indicated objects and forgetful functor. This exact issue is recorded in the definition node itself; it is not a conjectural failure of purity.

I repaired the statement faithfully to its blueprint/definition meaning: X₀ denotes the original scheme, X its geometric fiber; WC(X₀) explicitly denotes fixed pairs; the compact-support functor is the equivariant lift; the constant object and its Tate twist have their canonical Weil structures. The hypotheses (finite field, different prime, separated finite type, smooth relative dimension d, existence of the chosen right adjoint) and the isomorphism conclusion are retained. The shift is explicitly the shift of the underlying complex and Weil arrow and makes no triangulated-category assertion. The misleading Lean parentheticals and reference to a raw E-only twist definition were replaced by the definition nodes that actually define the qbar fixed-pair objects and operations.

The existing `lean` field is maintainer-owned and has been retained verbatim, but is NOT a claim that the repaired statement matches the upstream signature. The maintainer needs to reassess that attachment. This delivery proves the source-intended fixed-pair assertion; it supplies no equivalence with the upstream derived category and does not claim to remove the upstream sorry. The read clone has one DAG citer, lem-a1-local-boundary-duality. Its statement already uses the fixed-pair coefficient conventions, and its smooth-curve duality step directly cites geometric rational purity; that mathematical formula is unaffected. Its upstream Lean proof uses the derived-Weil declaration, so that implementation route still needs the separate reassessment just described. I did not edit the citer.

## Sources and route

I read the main-20261015 unit sk-thm-purity-transport, the matching corollary in sk-cor-sp-all-coefficients (statement and proof), prop-weil-operations (statement and proof), thm-pur-weil-equivariance-of-purity-and-trace (statement and proof), cor-coef-verdier-weil-equivariance (statement and proof), and det-sp-unique-right-adjoint's categorical source. The current corollary is located in sk-cor-sp-all-coefficients, rather than its older sk-thm-purity-transport directory. The split realizes the unit's specialization to the constant coefficient object, followed by the existing Frobenius-equivariant adjunction lift. It does not replace the lecture-notes finite-purity route.

The generic tools from other units are declared in split_report.tool_uses: geometric base-change permanence, equivariant adjunction, equivariant operation comparison, right-adjoint uniqueness, and the rational purity/mate identification. These supply typing and categorical transport; none replaces the geometric smooth-purity theorem of this unit.

## Searches and duplicate check

There are no new nodes. I searched the DAG and blueprint for dualizing complexes, smooth dualizing formulas, and Weil equivariance, and read the actual statements of every node subsequently cited. The geometric corollary is reused: it proves the geometric formula but has no Weil datum. The equivariance theorem alone defines smooth exchange through purity, so I also use the existing rational Weil naturality/mate lemma, which identifies that exchange with the actual adjunction mate. No new copy of those statements was made.

The item's Mathlib searches were run using msearch: LeanFinder with two phrasings, Loogle for `"dualizingComplex"`, grep for `dualizingComplex|upperShriek|WeilComplex`, and LeanSearch for smooth purity. I read the returned hits: scheme-limit, smooth-dimension and ordinary module-pullback results, with no matching Weil dualizing assertion. All new records copy the executed query texts and actual results from searches.jsonl. The imported historical searches are retained rather than silently rewritten.

## Not duplicates

No new nodes. The blueprint same_as entry is retained as the provenance of the underlying smooth dualizing formula, not an assertion that forgetting the Weil datum is a category equivalence.

## Review by NS

I checked delivery-errors B through E against the four steps, the cited statements and the source text. Step 1 uses separated finite-type base-change permanence and fixed-relative-dimension smooth base-change permanence, both of which explicitly allow precisely this field extension; it then applies the existing dualizing corollary at Λ = Qbar_l to the geometric structure map. That corollary identifies its isomorphism as the inverse of transported purity, so the later use of gamma is justified by its statement, not its proof. The geometric corollary supplies the hard purity calculation already on the required route.

In step 2 the coefficient-equivariance corollary explicitly says the constructible exceptional adjunction lifts to Weil pairs with equivariant unit and counit. The operations node identifies the compact-support lift in the same category. I apply uniqueness of right adjoints within the fixed-pair categories themselves, so the chosen right adjoint in the statement is covered even if it is not the canonical lift. The uniqueness lemma's statement supplies mutually inverse transposes of the counits. I did not cite an exceptional-inverse-image definition as a substitute for this theorem.

Step 3 uses the twist node that covers qbar coefficients, not just the E-only raw-coefficient definition. Its tensor Weil map and pullback/shift comparisons identify the source structure. The rational naturality/mate node explicitly supplies BOTH naturality for every rational morphism and identification of e with the adjunction mate. The operations node says the exceptional lift uses exchange and adjunction maps. Substitution into the three displayed equalities proves the required square without assuming a stable integral lattice. This corrects the potential gap of treating the purity-defined exchange as automatically the actual exceptional exchange.

Step 4 is elementary algebra on that commuting square. I wrote the inverse morphism equation explicitly, used functoriality Q(gamma^-1) = (Q gamma)^-1, and used the stated definition of composition and morphisms of fixed pairs. Nothing is promoted to a derived-category morphism by faithfulness alone. Every cited statement was opened and every citations.json quote was checked by exact substring membership. All four steps are below 2000 characters; no long step hides a new comparison lemma.

The small cases are consistent: d = 0 gives the untwisted unshifted etale formula; X₀ empty gives the unique zero objects and isomorphism and needs no dimension maximum; X₀ = Spec(k₀) gives the constant object and trivial twist. The sign is [2d], hence the resulting sheaf is in cohomological degree -2d. The Jordan-block point test specifically prevents the incorrect identification of coefficient categories. No hypothesis of properness or a Frobenius-stable lattice is introduced. There are no new statements to test, no new same-tag pairs, and no new unsplit child hiding a clause of this item.

## Unfinished work

No unfinished stage-1 argument for the corrected fixed-pair statement. The upstream derived-Weil interpretation requires a separate comparison or an independently justified derived-Weil purity argument; the retained Lean attachment must not be accepted as an exact rendering of this node.
