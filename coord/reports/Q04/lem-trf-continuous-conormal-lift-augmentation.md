## Worker report

Files written: dag/nodes/sec-trace-formula/lem-trf-continuous-conormal-lift-augmentation.json (statement, split; no Mathlib match), citations.json, and this report. Eight proof steps, with the exact union of their cited nodes as proof_deps. No Lean was written or compiled. All writes are in the assigned sandbox.

## New nodes

None: 0 new nodes, 0 new Mathlib leaves. The existing DAG already contains the needed completion comparison, finite-level gradient formula, relative-derivation expansion, polynomial differential basis, localization theorem, and power-series unit criterion. In particular no clause of the item was moved into a new node.

## Attachments

None. Searches in lean/WeilConjectures for the exact blueprint tag, continuous conormal maps, completed differentials and conormal lifts found no declaration of this complete assertion. ConormalComplementPolynomialLift concerns a different algebraic complement construction, and SmoothSectionCompletionChart constructs a smooth-section chart; neither supplies this item. The Mathlib algebraic cotangent-map API is not an attachment of a project declaration.

## WANTED

None. The proof is explicitly agent-formulated, using existing auxiliary nodes and the local Stacks sources below; it is not claimed to occur verbatim in Stacks.

## Findings and corrections

The original statement has no detected error, and is unchanged. Its unsplit proof is now an eight-step argument. The notation for the two uses of a hat differential is disambiguated in the proof: D_T is the gradient derivation into T^n, its reduction defines C_T's differential, and widehat d has values in M_R. In particular there is no identification of ordinary differentials of T with free continuous differentials.

The definition def-trf-completed-differential-extension asserts a predicate only; it cannot establish existence or uniqueness. Step 4 instead cites the actual theorem lem-trf-completion-kahler-differential-comparison with residue extension k/k. The formal-coordinate chain-rule node assumes an isomorphism and equal numbers of variables, so it cannot justify arbitrary presentation maps. Steps 6 and 7 instead use lem-trf-formal-relative-derivation-expansion, which allows arbitrary local formal maps and different numbers of variables.

Blueprint ancestor search returns lem-trf-local-term-locality. I read its current latest proof and the chapter/unit records. The latest proof uses the contracting-correspondence theorem, whereas this node's historical from.place follows the semistable/nearby-cycle descent retained by its parent. The original provenance and via list are retained, and split_report explains this distinction; no chapter or unit route was rewritten. Whole-blueprint searches for conormal, presentation, continuous conormal, continuous differentials and derivation expansion found no equivalent blueprint statement. No new blueprint node is introduced.

## Mathlib searches

searches.jsonl records the exact five commands run for this item on 2026-10-23: LeanFinder twice with distinct phrasings, Loogle, grep of RingTheory/, and LeanSearch. The actual results are appended to mathlib_searches without inventing queries. The inherited Q14 searches are retained as history. LeanSearch was available in this session and returned analytic rather than algebraic formal-series calculus. LeanFinder returned KaehlerDifferential.map, map_d, algebraic CotangentSpace.map and map_comp_cotangentComplex, and then derivation-composition APIs. I read Kaehler/Basic.lean lines 650--671 and Extension/Cotangent/Basic.lean lines 143--156 and 197--209: these concern ordinary algebraic differentials and do not state the continuous module-valued chain rule or the lifted comparison with the completed algebraic differential module. The grep returned MvPowerSeries/Derivative.lean and Kaehler/JacobiZariski.lean; their existence does not establish this whole node. Thus the item remains a split statement, not a Mathlib leaf.

## Review by Q04

I read varieties.tex Tag 0C52 (lemma-complete-local-ring-structure-as-algebra), including its coefficient-field and chosen-coordinate surjection argument; algebra.tex Tags 00MA (lemma-completion-tensor) and 05GG (lemma-hathat-finitely-generated), including their finite-generation hypotheses; Tags 00RT (lemma-differentials-localize), 00RU (lemma-differential-seq), 00RX (lemma-differentials-polynomial-ring), and 02HQ (lemma-differential-mod-power-ideal); curves.tex Tags 0C4B (lemma-fitting-ideal-well-defined) and 0C4D (lemma-nodal); and more-algebra.tex Tag 07PE (lemma-derivation-extends). These motivate the agent assembly but do not themselves state every formal comparison clause. There are no new nodes whose statements require a further source comparison.

Step 1 uses the statement of lem-weil-pbc-power-series-local-ring, both its unit criterion and its description of the maximal ideal, and the actual fractions definition of localization. Choosing v_i is justified by the given surjectivity, not formal smoothness. Because the maps are local k-algebra maps and every residue field is the specified k, the residues of v_i are the rational coordinates a_i, so precisely the inverted denominators become units. The inverse-image calculation also proves locality of the constructed lift. This is a short coordinate and fractions argument from the cited statements.

Step 2 uses the polynomial differential basis and the localization isomorphism, both read from their node statements; together they supply the localized basis rather than an unsupported assertion about P. The definition of Kahler differentials supplies its universal property, and the formal partial-derivative definition supplies the Leibniz laws. Applying that universal property to D_T alpha and reducing modulo J gives f^0 directly. The proof spells out alpha(I^2) contained in J^2 and the action of P modulo J; thus the degree -1 map is A-linear before extension to R. It never assumes alpha factors through A.

Step 3 uses only those defining derivation laws. I checked the square-ideal calculation separately for I and J, and checked the chain equation on a general ideal class [h], not just chosen relations. This needs neither regular sequences nor freeness of either conormal module. The same calculation gives q_P on the source complex.

Step 4 uses the full statement of lem-trf-completion-kahler-differential-comparison: it actually asserts the isomorphism eta and its equality on every completed element. Its finite-separable hypothesis holds for k/k; the coefficient section is the structural k-map. The node lem-trf-power-series-adic-gradient-control actually asserts the finite-level identity in Omega(T/a^r), for all r and all series. Locality of pi supplies T/a^r to R/m_R^r. Applying the map on differentials follows from the cited universal property, so no unproved inverse-limit exactness or continuity exchange is used. Equality is tested coordinate by coordinate and transported back only by the cited isomorphism. For elements of J this also proves q_T kills the conormal differential.

Step 5 checks the augmentation on every basis element using the previously established chain rule and the prescribed extension property on A. The zero degree -1 components are stated. This is an elementary equality of linear maps, not a new normalization theorem.

Step 6 applies the statement of the relative-derivation expansion to E_j = partial'_j beta and psi = beta. The target is the actual formal-series ring T', not its quotient R; thus the node's target hypothesis holds. Locality is exactly its maximal-ideal containment hypothesis. Reduction modulo J' then uses pi' beta = pi. The augmentation computation invokes Step 4 for the second presentation and writes the whole sum, so it does not infer augmentation compatibility merely from the chain equation.

Step 7 checks identities and writes the coefficient of each composite matrix. The relative-derivation expansion for gamma is applicable to beta(z_i) and also to alpha(u_i); there is no need for these maps to be invertible or for their variable counts to agree. Composition in degree -1 is literal composition on ideal classes. The derivative node states its values on variables, which gives the identity matrices.

Step 8 uses the universal property to form the algebraic differential maps, writes the inverse and fraction formulas from Leibniz, and checks their augmentations on all symbols dp. This includes denominators, arbitrary relations, identities, composition, and polynomial maps followed by a formal lift. Tensoring the already established equality gives the extension to R; no flatness or exactness is inferred just from tensoring.

The three algebraic statements from other units (the power-series local-ring criterion, the polynomial basis, and the localization isomorphism) are generic tools; they are declared with explanations in split_report.tool_uses, not in the maintainer-owned tool_uses field. All other substantive auxiliary inputs belong to this item's unit. A dependency traversal found no path from any cited node back to the item.

I checked small and degenerate cases: zero variables (T=k and empty gradients), zero relation ideal, nonregular relation ideals, nonreduced A such as k[u]/(u^2), arbitrary characteristic including p, and unequal formal variable counts (for example redundant parameters mapping to zero). No division by an integer appears. The proof never asserts that an arbitrary formal presentation is smooth over R. Polynomial coordinates need not be centered at zero: the residues a_i are retained in Step 1. The proof uses no SGA source.

Against delivery-errors B--E: there are no new statement-only-node or duplicate-node issues; all non-elementary inputs are cited existing statements; each cited statement was opened and its used assertion is quoted verbatim in citations.json; every non-elementary step is below 2000 characters; no proof hidden inside a cited node was used as extra content. The calculations retained in elementary steps are the displayed ideal-square, fractions, universal-property and generator calculations. No unresolved mathematical gap or statement dispute remains.

## Not duplicates

No new nodes, hence no new/existing node pairs.

## Unfinished work

None in the stage-1 split. The cited existing auxiliary theorems remain their own DAG work; this delivery claims no Lean proof.
