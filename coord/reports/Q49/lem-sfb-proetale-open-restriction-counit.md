# Q49 stage-1 report: lem-sfb-proetale-open-restriction-counit

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-proetale-open-restriction-counit.json` — statement item, split with three proof steps, no new nodes.
- `citations.json` — verbatim citations for every proof-step dependency.

## Attachments

None. I searched the project declarations and found no sorry-free declaration stating this item exactly.

## WANTED

None.

## Not duplicates

No new nodes were created, so there are no new/existing node pairs to distinguish. The existing `lem-sfb-proetale-object-inverse-image-restriction` is a site-object restriction lemma used as an ingredient; it does not state direct-image base change or the counit equation.

## Statement and split checks

The statement is unchanged from the repository copy. The Lean source was searched under `WeilConjectures/` for the item identifier, open-restriction/direct-image terminology, and counit names; only the general pro-etale open-immersion restriction and direct-image declarations were found, with no declaration of this base-change comparison. I read the item source metadata (Stacks `proetale.tex`, Tag 09A5, together with `sites.tex` Tag 00XZ) and the blueprint ancestor `det-prop-scalar-six-pullback`; the blueprint place is now the final sentence of Proof (1), compatibility with restriction to open subschemes.

The three proof steps use the following sources and statements. Step 1 uses the actual pro-etale inverse-image construction, the open-immersion base-change fact, site-morphism composition, and the ringed-topos module adjunction. These establish that h and its base change g define compatible site morphisms and that the module inverse/direct-image adjunctions and the comparison α have the required types. Step 2 uses the reviewed open-slice ringed-site equivalence, the direct-image section formula, the reviewed pro-etale object inverse-image restriction lemma, and the fibre-product universal property. At an object E→W, both sides reduce to the same section after the canonical identification `X_W ×_W E ≅ X ×_Y E`; the component maps are natural and module-linear. Step 3 uses the module adjunction statement for the counits, the direct-image restriction formula, the unit-compatible site-composition comparison α, the open-slice equivalence, and fibre-product uniqueness. After the same objectwise identifications, both sides of the counit equation are the restriction map from `M(X ×_Y E)` to `M(X_W ×_W E)`, so the equality follows by naturality.

I read every cited node statement before writing `citations.json`; each quote is copied verbatim from the statement field. The hypotheses used in the calculation are exactly those in force: h is open, g is its fibre-product base change, E→W is a pro-etale object, and R is an arbitrary sheaf of commutative rings. No properness, finiteness, Noetherian, or constant-ring assumption was introduced. The search records already present on the item were retained because the statement and search question did not change; they report generic Mathlib sheaf/module hits but no full pro-etale base-change theorem.

## Review by Q49

I checked the item against the read-only Lean source and found no exact finished declaration. I read the statements of `def-weil-proetale-inverse-image`, `def-weil-proetale-module-direct-image`, `lem-weil-pbc-open-immersion-base-change`, `lem-weil-pbc-site-morphism-composition`, `lem-weil-pbc-ringed-topoi-module-adjunction`, `lem-weil-pbc-proetale-ringed-open-comparison`, `lem-sfb-proetale-object-inverse-image-restriction`, and `def-pc-fibre-product`. Step 1 cites the site and adjunction statements for precisely the existence and compatibility data it takes. Step 2 cites the open-slice equivalence and restriction lemma for both h and g, and the direct-image and fibre-product statements for the displayed section identification; no proof-only construction from a cited node is used. Step 3 checks the counit components directly on E→W and uses the unit-compatible composition comparison for α, so the two composites are the same restriction map. I corrected the inherited blueprint place to point to the restriction-compatibility sentence of the ancestor proof, added the complete split and proof dependencies, and recorded verbatim citations for every use. No new node was needed and no duplicate or source error was found.

## What remains

Nothing remains for this stage-1 split; the required delivery dry run is the remaining validation step.
