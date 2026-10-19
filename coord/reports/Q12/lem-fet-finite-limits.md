# Worker report: lem-fet-finite-limits

## Files written

- `dag/nodes/sec-curve-estimates/lem-fet-finite-limits.json` — item split into twelve proof steps; no new DAG nodes.
- `citations.json` — 42 verbatim step-to-node citations.
- No Mathlib leaves or new nodes were created.

## Attachments

No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` states this item exactly. The source does contain finite-limit and finite-coproduct interfaces in `AlgebraicGeometry.Scheme.FiniteEtale`, but no declaration of all finite colimits and arbitrary-base-change exactness, so this is not an attachment.

## WANTED

None. The Stacks source, the current and 2026-10-15 blueprint text, and all cited DAG nodes were available locally.

## Source error and correction

The imported blueprint proof says that after an étale cover one may write the base as a coproduct of copies of one scheme and uses a single finite index set globally. This is false for a disconnected base: finite étale covers can have different ranks on different connected components. For example, over `Y = Spec(k) ⊔ Spec(k)`, take one point over the first component and two points over the second. I retained the item statement and corrected the proof route by using the existing pointwise local-splitting node `lem-weil-pbc-finite-etale-etale-local-split`, allowing finite sets `S_i,T_i` to vary with the cover member. The local finite-set quotient and its base-change compatibility are then glued by the existing representable-sheaf and effective étale-descent nodes.

The project Lean source was checked by searching all `WeilConjectures/` files for the item id and finite-étale limit/colimit declarations. `GaloisCategory.lean` proves `HasFiniteLimits` and finite coproducts for `Scheme.FiniteEtale`, but does not state finite coequalizers, finite colimits, or exactness of every base-change functor; its sorry-free declarations therefore do not attach this item.

## What could not be finished

Nothing remains for this stage-1 split. The proof is natural-language only, as required; no Lean file, compiler, Lake, or build tool was run.

## Review by Q12

I read the item node, the unit `sk-prop-h2`, the chapter record, and both the old and `main-20261015` blueprint copies. I read the Stacks proof at Tag 0BN9 in `pione.tex`, the finite étale local-splitting lemma Tag 04HN, the finite-limit criterion Tag 002O, the finite/étale locality tags 01WI, 035D, 02GN, 02GW, 02GO, and the representable-sheaf and descent material at Tags 03O3/03O4, 0245, 02LA, and 02VN. The item hypotheses are exactly “Y is a scheme” and an arbitrary morphism `Y' → Y`; no connectedness, constant rank, or finiteness hypothesis on the base-change morphism was added.

For steps 1–3 I checked the statements of `def-weil-pbc-finite-etale-category`, `lem-weil-pbc-finite-permanence-over-separated`, `lem-weil-pbc-etale-composition-cancellation`, `def-pc-fibre-product`, `lem-weil-pbc-finite-composition`, and `lem-weil-pbc-finite-limits-from-terminal-pullbacks`: they supply precisely the finite/étale structure of morphisms, scheme fibre-product universal property, and finite-limit preservation used there. Step 4 uses the existing scheme coproduct, finite-coproduct, étale-coproduct, and fibre-product/coproduct-base-change statements; its empty-union argument is checked directly on affine charts. Steps 5–7 use the pointwise local-splitting statement, the clopen-summand coproduct statement, and the finite-set quotient argument; I explicitly made the varying finite sets `S_i,T_i` local rather than asserting a global rank. The equality propagation in step 7 is elementary from the generated equivalence relation.

For step 8 I read the statements of the scheme-coproduct, étale, finite-local-on-target, representable-etale-sheaf, finite-étale-category, base-change-covering, and fibre-product nodes. They justify the component covering, finite and étale properties of `Q'`, and gluing of maps and factorizations. The proof now applies the representable-sheaf statement to the pulled-back component coverings and does not use a finite-family lemma for an arbitrary coproduct. Step 9 is the elementary overlap uniqueness/cocycle calculation using the fibre-product definition. Step 10 uses exactly the equivalence, fullness, and faithfulness asserted by `lem-galois-descent`; I checked that this node’s statement includes finite étaleness and descent of morphisms. Step 11 uses the stated stability of surjective étale coverings under base change and the same descent equivalence to prove universal coequalizers. Step 12 uses the definition of finite limits/colimits and exact functor, and writes the standard coproduct/coequalizer presentation of a finite diagram, including the empty diagram.

I regenerated `citations.json` from the repository statements so every quote is verbatim. I ran the required LeanSearch, Loogle/LeanFinder, and Mathlib-grep searches recorded in `searches.jsonl` (including a second semantic phrasing); they found general scheme limits, finite/étale stability, coproduct and gluing APIs, but no theorem for finite-étale coequalizers with arbitrary base-change preservation. No new node was needed, so there are no duplicate-node pairs or additional Mathlib leaves to report.
