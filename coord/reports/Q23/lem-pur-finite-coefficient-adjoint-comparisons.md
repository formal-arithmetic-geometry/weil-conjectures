# Stage-1 worker report: lem-pur-finite-coefficient-adjoint-comparisons

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-finite-coefficient-adjoint-comparisons.json`: existing item, retained as a 13-step split; status `split`, not a Mathlib leaf.
- `citations.json`: 62 step/node records, each quoting the cited node statement verbatim.
- No new DAG nodes and no new Mathlib leaves.

## Attachments

None. I searched the read-only slopmaster2 source by the exact blueprint id and by exceptional-adjoint and finite-coefficient terminology. No sorry-free project declaration states this whole arbitrary-field theorem. The existing declarations and DAG nodes used below are dependencies, not attachments for this item.

## WANTED

None.

## Corrections and route

The item statement is unchanged: it treats an arbitrary separated finite-type morphism over a positive-characteristic field, finite DVR quotient coefficients and finite-free coefficient extensions, and the specified counit-normalized exceptional adjunction and mate. The current proof follows the main-20261015 smooth-purity route. It uses the smooth affine-space coefficient comparison only for local affine factors, then closed-support triangles and ordinary étale localization for general morphisms. It does not invoke the forbidden SGA 4 trace route.

The inherited split has no hidden new lemma to add: every non-elementary fact used by its 13 steps is already an existing DAG statement. Step 1 explicitly proves finite generation of the extension of valuation rings using finite representatives modulo the uniformizer and completeness before applying the DVR freeness statement. Step 8 uses the current `det-sp-reduction-exceptional` chart theorem together with the existing coefficient-square, site-comparison, and counit-preserving uniqueness statements; it does not infer invertibility of a mate merely from invertibility of the left comparison. The proof dependency union is exactly the union of the step uses.

## Review by Q23

I read the item, the `sec-smooth-purity` chapter, the `sk-thm-purity-transport` unit, and the current blueprint files named in the item and in each proof source. I opened every one of the 40 cited DAG node files and checked the quoted sentence in `citations.json` against its statement. The following records the hypothesis and conclusion checks for each step.

1. Step 1 applies finite-type-over-Noetherian to schemes finite type over `Spec(k)`, uses the valuation-ring, finite-quotient, absolute-value, and completeness statements for the coefficient tower, and proves finite generation and then finite freeness before reducing modulo powers of the uniformizer. The cofinal ideal identity is checked from `t = u v^e`; no geometric finite-field hypothesis is introduced.
2. Step 2 uses the relative torsion cohomological-dimension bound for finite-type morphisms, restriction of scalars along `Z -> A`, and the long exact sequence of a triangle to obtain a uniform boundedness interval for bounded inputs. It does not assume finite absolute cohomological dimension of the base field.
3. Step 3 applies bounded constructibility, the bounded flat constructible model, finite-constant projection, and the residue-field Tor test. Step 1 supplies that the coefficient rings are finite Noetherian DVR quotients and that the relevant residue and extension modules are finitely presented. Restriction of scalars reflects the stated comparison isomorphism.
4. Step 4 uses exactness and the stalk formula for étale extension by zero, checks the tensor map termwise on flat models, and invokes conservative geometric stalks to identify the canonical comparison. The constructibility stratification is extended by the closed complement.
5. Step 5 uses the ordinary étale exceptional adjoint, Nagata compactifications, unbounded compact-support composition/refinement, source-open locality, and mate-pasting. The chosen compactification and every local factor are between Noetherian finite-type schemes, so the hypotheses of those statements hold.
6. Step 6 verifies the closed-support finite-Tor proposition using the complementary quasi-compact open and Step 2. For affine-space projections it uses the vector-bundle purity statement, exact inverse image, tensor-pullback, and the finite locally constant twist statement. Finite affine covers and closed embeddings into affine space give the local factorization; bounds and constructibility stratifications glue over the finite cover.
7. Step 7 checks both directions of finite étale/pro-étale constructible derived origin, exact comparison pullback, tensor compatibility, the bounded-below site comparison, the residue Tor test, and compact-support site comparison. These yield preservation of the specified subcategories and transport the adjunction, unit, counit, and projection comparison.
8. Step 8 applies `det-sp-reduction-exceptional` only to a smooth affine-space projection. Its finite ell-primary coefficient hypotheses include quotient and finite-free maps, and its counit equation is matched with the ordinary coefficient comparison using the existing direct-image mate, site/coefficient square, adjunction-transfer, and counit-preserving unique-right-adjoint statements. Thus the chart mate is invertible with the exact normalization required by the item.
9. Step 9 tensors the closed-support triangle with the coefficient ring, uses the Step 3 projection comparison on the open complement and the closed pushforward, and applies triangle two-out-of-three. The fibre map is the specified closed exceptional mate, so the resulting isomorphism is the required mate rather than an arbitrary isomorphism.
10. Step 10 uses composition and localization of the ambient adjoint together with mate-pasting, semilinear tensor compatibility, and conservative stalks to pass from the smooth and closed local factors to arbitrary separated finite-type `f`. The argument checks the canonical counit transposes on the finite affine cover.
11. Step 11 is the explicit adjunction calculation: counit naturality, projection naturality, and the triangle identity show that the proposed composite is the `B`-unit; the mate's counit equation is its defining transpose equation.
12. Step 12 applies the semilinear enhanced-section and cartesian-section mate statements to constant coefficient systems and finite strings. The ordinary right adjoints and invertible specified mates have already been proved in Steps 5–10, so the enhanced adjunctions and mixed coherence diagrams follow without an inverse-limit adjunction.
13. Step 13 uses the valuation-ring, finite-quotient, and DVR-freeness statements to identify `S/t^n S` with `S/v^(en)` and proves cofinality of the ramified subsequence. It makes no integral, rational, or condensed identification.

I tested the statement and the coefficient maps on the identity morphism, the zero object, the `r=0` affine projection, a non-flat reduction such as `Z/l^2 -> Z/l`, equal coefficient levels, ramification index `e>1`, and empty schemes. These cases agree with the displayed unit/counit and cofinality formulas. The whole DAG and blueprint were searched for duplicate statements; since no new node is created, there is no duplicate pair to report. The Q23 Mathlib searches were run with `msearch.py` for LeanFinder, Loogle, grep, and LeanSearch, each with a second phrasing where the first search was inconclusive. They returned only abstract mates, derived-category, or ordinary sheaf adjunction declarations, so the item remains an unsplit project theorem rather than a Mathlib leaf.

## Unfinished work and validation

No mathematical work remains at stage 1. No Lean file was written and no compiler, Lake, or build tool was run. The required server-side dry run is the next validation step.
