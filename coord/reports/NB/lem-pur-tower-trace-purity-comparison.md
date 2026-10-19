## Worker report

1. Files written:

- `dag/nodes/sec-poincare-duality/lem-pur-tower-trace-purity-comparison.json`: split statement, six proof steps, and the field-extension/rational transport dependencies.
- `dag/nodes/sec-poincare-duality/lem-pur-tower-rank-one-level-uniqueness.json`: statement node, Mathlib searches found no match.
- `citations.json`: verbatim statement quotes for every cited node in every item step.

2. Attachments:

- No sorry-free Lean declaration matched the item or the new node.

3. WANTED:

- None.

4. What was wrong or incomplete in the imported node:

- The imported item had an empty proof and `proof_deps`, despite its source note requiring an explicit comparison of the tower orientation, counit-preserving right-adjoint comparison, and trace transpose. I supplied those arguments and retained the exact statement.
- The argument needs the rank-one tower uniqueness sentence in the tower-gamma proof. No DAG node stated that fact, so I added the strictly smaller levelwise uniqueness node after searching the DAG, blueprint, source repository, and Mathlib.
- The item is attached to `prop-weil-operations` in the imported blueprint ancestry; I filled its previously unspecified proof place and recorded the tower-gamma, field-extension, and rational-transport blueprint clauses realized by the split.

5. What could not be finished:

- Nothing remained unfinished at the stage-1 natural-language level.

## Not duplicates

- `lem-pur-tower-rank-one-level-uniqueness` vs `det-sp-tower-gamma`: the new node proves equality of any two compatible degree-zero tower maps from their level components; the existing node constructs the specific tower orientation and purity maps and does not state this general uniqueness criterion.
- `lem-pur-tower-rank-one-level-uniqueness` vs `lem-coef-derived-system-evaluation-calculus`: the new node concerns equality of degree-zero morphisms in the tower derived category, while the existing node gives an evaluation criterion for isomorphisms of derived systems and explicitly does not assert reconstruction or arbitrary morphism faithfulness.

## Review by NB

I read the item node, the fixed chapter `sec-poincare-duality`, and unit `sk-lem-finite`, then checked the imported statement against the source interfaces in `sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md`, `sk-lem-sp-field-extension/sk-lem-sp-field-extension-towers.proof.md`, and the rational-purity transport source. I also read every cited DAG statement. The hypotheses on the algebraically closed finite-field datum, $ell\ne p$, finite coefficient fields, separated finite-type schemes, smooth separated pure relative dimension $d$, completed integral categories, compactification, and finite-Tor constructible inputs agree with the item statement; no coefficient category was silently changed.

Step 1 uses `det-sp-tower-gamma` for the diagonal orientation, its finite levels, and the projection/counit transpose; `det-sp-integral-adjunction-bijection` for the derived-limit right adjoint and the integral purity map; and `lem-sf-integral-compactification-system-realization` for the canonical compactification realization maps. Their statements provide exactly the orientation, limit, and realization facts used. Step 2 uses `det-sp-unique-right-adjoint` for the unique counit-preserving comparison and the preceding integral-adjunction and realization statements for the common functor and counit. Step 3 uses the level clause of `det-sp-tower-gamma`, the new levelwise uniqueness statement, the realization comparison, and the exceptional-adjoint notation; after removing the common shift, both maps are degree-zero rank-one tower maps with the same finite components, so the cited node applies. Step 4 uses `det-sp-field-extension-towers`, whose statement explicitly transports compact supports, exceptional adjoints, units, counits, purity maps, and associativity across finite coefficient extensions; the compact-support notation and integral adjunction statements supply the displayed objects. Step 5 uses the tower-gamma definition, the realization statement that preserves projection/counit transposes, `def-exchange-projection`, and the field-extension comparison. The only elementary inference is injectivity of an adjunction hom-bijection after the two transpose composites are identified. Step 6 uses the rational and $overline{\mathbf Q}_\ell$ purity statement, simultaneous adic scalar naturality, field-extension transport, and the definitions of the rational and common-stage categories; these statements give the final scalar-localized and common-stage equality.

For the new node I read the tower definition, the tower abelian-category statement, and the derived-category definition. Its one proof step is the componentwise morphism argument in the cited tower-gamma source. The statement was tested on the one-point rank-one tower (where equal reductions force equal units) and on the zero/degree-zero tower (where both maps are uniquely zero); both edge cases satisfy the claim. The Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch and returned only generic chain-map extensionality or unrelated orientation facts. I searched the whole DAG and blueprint for rank-one tower uniqueness, tower-level equality, the cited source place, and the key terms before creating it; the two closest existing nodes are distinguished above.

I corrected the item by adding the missing proof, proof dependencies, levelwise uniqueness prerequisite, blueprint proof place, citations, and tool-use declarations. Every citation quote is copied verbatim from the cited node statement, and each proof step names all of the non-elementary nodes it uses.
