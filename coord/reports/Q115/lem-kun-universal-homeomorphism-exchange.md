## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-universal-homeomorphism-exchange.json`: statement node, split; no Mathlib match.
- `citations.json`: verbatim interface quotes for all cited nodes and steps.
- `searches.jsonl`: mandated LeanFinder, Loogle, grep, and LeanSearch records (all four searches were run; no matching theorem was found).

## Attachments

None. The source checkout contains no sorry-free project declaration tagged `(blueprint: lem-kun-universal-homeomorphism-exchange)`, and the previous proposed attachment used a distinct Mathlib notion of universal homeomorphism. The item is therefore split rather than attached.

## WANTED

None. The Stacks sources and all cited DAG statements are present locally.

## What was wrong or incomplete

The imported item was statement-only and had no proof. The earlier attachment proposal was rejected because the Mathlib `topologically IsHomeomorph` universal notion is distinct from the project's stronger `IsUniversalHomeomorphism` interface. I retained the statement and supplied the missing proof. No statement hypothesis was changed, no coefficient category was introduced, and no new node was necessary. The proof uses the existing topological-invariance equivalence, the existing sectionwise exchange description, the direct-image formula, and the existing direct-image composition coherence. The current parent blueprint's Step 1 explicitly calls for this underived exchange and its unit equation.

## What remains unfinished

Nothing for this item. No Lean was written, and no compiler, Lake, or build tool was run.

## Review by Q115

I read the current item node, the parent `lem-kun-0f1c` blueprint update, and the statements of every dependency used below. I also read the Stacks Project Etale Cohomology proof of Tag 0F1C (the perfect-closure reduction) and Proposition 03SI (topological invariance). The item hypotheses are exactly a cartesian square of schemes with both horizontal maps universal homeomorphisms and an arbitrary abelian etale sheaf; no quasi-compactness, coefficient ring, torsion, or field-extension hypothesis was added.

Step 1 uses `thm-weil-pbc-universal-homeomorphism-invariance`, whose statement gives an equivalence of small etale sheaf categories compatible with inverse and direct images. I checked that this applies separately to `g` and `g'`. The cited inverse-image definition says that inverse image is left adjoint to direct image and names the unit, so the unit maps used in the step are the adjunction units. Equivalence makes both units isomorphisms and makes `g_*` conservative.

Step 2 uses `lem-weil-pbc-underived-exchange-sectionwise`, which explicitly says that the exchange component sends a representative section on `X ×_Y W` to its restriction on `X' ×_{Y'} V`; this is exactly the map used in the calculation. The direct-image definition supplies the section formula `(u_*F)(W)=F(W×_V U)`. The direct-image-composition coherence node supplies the canonical fibre-product comparison identifying `g_* f'_*` with `f_* g'_*`. On each etale test object, both sides of the displayed unit equation take the same representative section to its pullback along `g'`; common refinements make the equality independent of representatives. I verified the source and target of the equation are both `f_*F → f_*g'_*g'^{-1}F` after this composition identification.

Step 3 uses the same topological-invariance equivalence. Since the right side of Step 2 is `f_*` applied to the isomorphism `η_{g',F}`, it is invertible; with the unit `η_{g,f_*F}` invertible, the equation makes `g_*(γ_F)` invertible. Conservativity of the equivalence then reflects this to `γ_F`. I checked the identity square, a nilpotent thickening/universal-homeomorphism square, and `f=id`; all reduce to the expected identity exchange and unit equation. I checked the proof-dependency union against the three steps and placed every cited statement's verbatim text in `citations.json`.

No new node was created, so there is no duplicate pair to record. The longest non-elementary step is below 2000 characters. No SGA source is cited.
