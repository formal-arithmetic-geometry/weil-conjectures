# Stage 1 report: sk-thm-sf-identification

## Files written

- `dag/nodes/sec-six-functors/sk-thm-sf-identification.json`: item split into eight proof steps.
- `citations.json`: full verbatim statements for every cited node in every step.
- No new node: the earlier self-injectivity node was removed because `lem-weil-coefficient-frobenius` already states the needed result.

## Attachments

`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_coefficientDual_of_orientation` in `WeilConjectures/SixFunctors/Etale/Derived/GlobalDuality.lean:118` is sorry-free in slopmaster2 but states only a `Nonempty` isomorphism at the sheaf level. The source docstring explicitly says that the identification with the pairing adjoint is not formalized, so it does not attach this item.

## WANTED:

None.

## Not duplicates

No new nodes remain, so no duplicate pair was introduced. The removed `lem-sf-finite-coefficient-self-injective` duplicated the finite-stage clause of `lem-weil-coefficient-frobenius`.

## Review by Q13

I read the item and unit records, the current main-20261015 unit statement and proof, the source declaration and its surrounding docstring in `WeilConjectures/SixFunctors/Etale/Derived/GlobalDuality.lean`, and the source Poincare-pairing file. The source declaration is closed but only gives `Nonempty` for the lower-star/coefficient-dual isomorphism; its docstring says the pairing-adjoint identification is still unformalized, so I did not attach it.

Step 1 uses `prop-sf-dualizable` only to type the coefficient dual of a site-perfect object, `def-sf-pairing` for the exact evaluation/trace composite, `sk-def-sf-orientation` for the orientation, `sk-thm-sf-dual-perfect` and `sk-lem-sf-twist-interchange` for the map from Verdier dual to the twisted coefficient dual, and `sk-thm-sf-global-duality` for the canonical global duality map. I opened each statement and checked that its hypotheses include the smoothness, finite type, pure dimension, coefficient stage, and perfectness assumptions used here.

Step 2 replaces the earlier invalid citation to the composition-mate lemma. I read `sk-thm-sf-tensor-hom` and `def-sf-datum`; their statements provide the tensor/internal-Hom exchange and the finite-Tor adjunction/projection axioms. I wrote the complete test-object Hom chain, with the explicit pullback counit, exceptional counit, and projection formula, and checked that all objects lie in the finite-Tor domains.

Step 3 reads `def-sf-cup` and `def-sf-pairing` line by line. Their statements say that cup product is the projection map followed by the pullback counit and that the pairing then applies twisted evaluation and the normalized trace. Substitution into the Step 2 formula gives the actual adjoint of `beta_K`; no detection lemma is used to assert equality. `lem-sf-point-fibre-derived-tensor` and `lem-weil-point-fibre-equivalence` are used only to transport the monoidal calculation to the point coefficient category.

Step 4 checks the proper finite and field stages against `lem-weil-point-fibre-equivalence`, `lem-weil-coefficient-frobenius`, `lem-weil-pbc-bounded-below-injectives-kinjective`, `def-pur-derived-internal-hom`, and `lem-sp-exact-functor-preserves-homology`. The former gives bounded finite-cohomology point complexes; the coefficient-frobenius statement gives self-injectivity, exact ordinary duality, and finite-module biduality; the K-injective and derived-Hom statements justify the explicit dual complex; and exactness gives `H^{-i}(C^vee) = Hom(H^i(C), Lambda)`. The common finite-stage interpretation is checked for `Qbar`.

Step 5 applies the derived adjoint and the shift convention, then uses finite-module biduality from `lem-weil-coefficient-frobenius` to obtain perfect degreewise pairings. I checked the zero-group and nonfree finite-module edge cases.

Steps 6–8 address the integral warning that the earlier attempt omitted. I read `lem-weil-l-adic-extension-integers-dvr`, `def-pc-perfect-ring-complex`, `def-weil-pbc-projective-module`, `lem-sc-dvr-saturation-line-smith-normal-form`, `lem-sc-bounded-above-projective-kprojective`, `def-pur-derived-internal-hom`, `lem-weil-pbc-ext-long-exact-first-variable`, and `lem-weil-pbc-projective-ext-criterion`. Step 6 follows the Stacks Tags 0A66/07VI projective-complex calculation; Step 7 computes the exact Ext sequence from cycles and boundaries and identifies its torsion term; Step 8 tests the claim on `X = Spec(k)` and `K = (O_E/varpi_E)` in degree zero, where the degree-zero pairing is visibly degenerate. This verifies the proper smooth dimension-zero edge case and the claimed failure mechanism.

I searched the whole DAG and blueprint before retaining any dependency. The only additional node attempted by the previous worker, `lem-sf-finite-coefficient-self-injective`, was a duplicate of the existing coefficient-frobenius node and was deleted. The prescribed searches for the item were run with LeanFinder, Loogle, Mathlib grep, and LeanSearch; they found only generic currying or ordinary algebraic pairing results, not this geometric statement.

## What was wrong or corrected

The imported proof cited `sk-lem-sf-mate` for a fact it does not state, cited `lem-sf-detection` as if it identified the actual morphism, omitted the `sk-lem-sf-twist-interchange` use in its earlier step, and did not prove the integral-stage warning. I replaced it with explicit unit/counit formulas, removed the duplicate self-injectivity node, and added the integral Ext calculation and counterexample. The item statement is unchanged.

## What remains

No new unsplit node remains. The item is ready for the second reader.

## Earlier second reading (a previous round; superseded)

- Source statement: checked against the main-20261015 blueprint node `sk-thm-sf-identification` and its proof file; all hypotheses (global-duality setting, fixed orientation, site-perfect coefficient object, proper coefficient-stage clause, and integral warning) agree, with definition citations made explicit.
- Step 1: checked against `sk-thm-sf-global-duality`, `sk-thm-sf-dual-perfect`, `sk-lem-sf-twist-interchange`, `prop-sf-dualizable`, `def-sf-pairing`, and `sk-def-sf-orientation`; the candidate (B) is a composite of stated isomorphisms, while the adjoint equality is deferred to Steps 2–3.
- Step 2: checked the tensor-Hom statement and the (A1)/(A3) clauses of `def-sf-datum`; the displayed test-object Hom chain uses the stated units, counits, exceptional adjunction, and projection isomorphism, with finite-Tor domains named.
- Step 3: checked `def-sf-cup` and `def-sf-pairing` line by line, then `sk-thm-sf-tensor-hom` and the two point-fibre nodes; the projection/counit/evaluation/trace composite is exactly the pairing, and the coefficient comparison is used only after the sheaf calculation.
  The current live `def-sf-cup` statement was re-read after the return: its displayed map uses `PF_{a_X,K,Ra_{X*}L}` with second input on the point, followed by `Ra_{X!}(1_K\otimes\varepsilon_L)`, and explicitly fixes the four coefficient-stage operations. The Step 3 citation was regenerated from that exact current statement.
- Step 4: checked `lem-weil-point-fibre-equivalence`, `lem-weil-coefficient-frobenius`, `lem-weil-pbc-bounded-below-injectives-kinjective`, `def-pur-derived-internal-hom`, and `lem-sp-exact-functor-preserves-homology`; exact self-injective duality gives the displayed (H^{-i}) identification without a projectivity assumption on cohomology.
- Step 5: checked the shift convention and finite-module biduality clause of `lem-weil-coefficient-frobenius`; applying (H^{-i}) gives both degreewise adjoints, including zero and nonfree finite modules.
- Step 6: checked the DVR source (Stacks Tags 0A66 and 07VI) and every cited projective, Smith-normal-form, K-projective, and derived-Hom statement; the bounded finite-projective representative and ordinary dual-complex computation are justified over (mathcal O_E).
- Step 7: checked the cycles/boundaries calculation against the exact Ext sequence, projective Ext criterion, projective-module definition, and Smith form; the short exact sequence and torsion Ext term have the correct indices and arrows.
- Step 8: checked the small case (X=s=\operatorname{Spec}k), (d=0), (K=[R\xrightarrow{\pi}R]); the degree-zero dual cohomology vanishes while (H_c^0=R/\pi R), so the integral degreewise form is genuinely degenerate. The zero object, field stages, and (n=1) cases are consistent with the stated conclusions.
- New nodes: none remain. The attempted self-injectivity node was confirmed to duplicate `lem-weil-coefficient-frobenius` and remains removed; no Mathlib leaf or definition node was added.

Changes made in this second reading:

1. Removed the stale, nonexistent citation `[sk-lem-sf-mate]` from Step 1 and wrote the global-duality candidate (B) explicitly; Steps 2–3 now carry the unit/counit verification of the adjoint equality.
2. Added `[def-weil-site-perfect-complex]` and `[def-sf-pairing]` citations in the item statement so its notions are self-contained.
3. Marked the module-duality and integral counterexample steps non-elementary because they use substantive exact/Ext calculations.
4. Regenerated `citations.json` from the repaired proof so every quote is verbatim from the cited node.

## Second reading by Q13

- Item statement: checked against `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-identification/_section.md`, node order 2508; the hypotheses, derived pairing, canonical adjoint, three self-injective stages, and integral warning agree clause by clause. Added explicit definition citations for site-perfectness and the derived pairing.
- Step 1: checked against `prop-sf-dualizable`, `def-sf-pairing`, `sk-def-sf-orientation`, `sk-thm-sf-dual-perfect`, `sk-lem-sf-twist-interchange`, and `sk-thm-sf-global-duality`; the orientation and evaluation transpose define the candidate inverse, and every cited statement supplies the asserted isomorphism.
- Step 2: checked against `sk-thm-sf-tensor-hom` and `def-sf-datum`; the test-object Hom chain uses only the stated exceptional adjunction, ordinary pullback adjunction, projection map, and finite-Tor domains, with the unit/counit composite written explicitly.
- Step 3: checked against `def-sf-cup`, `def-sf-pairing`, `sk-thm-sf-tensor-hom`, `lem-sf-point-fibre-derived-tensor`, and `lem-weil-point-fibre-equivalence`; substitution of the cup, evaluation, and trace definitions gives the actual pairing adjoint, and the point comparison is used only to transport the calculation.
- Step 4: checked against `lem-weil-point-fibre-equivalence`, `lem-weil-coefficient-frobenius`, `lem-weil-pbc-bounded-below-injectives-kinjective`, `def-pur-derived-internal-hom`, and `lem-sp-exact-functor-preserves-homology`; exact coefficient duality gives the displayed cohomology identification at (A_{E,n}), (E), and the common finite stage for \Qlb.
- Step 5: checked the shift convention and finite-module biduality clause of `lem-weil-coefficient-frobenius`; the degreewise adjoint and its reverse are isomorphisms, including zero and nonfree finite modules.
- Step 6: checked the Stacks Tags 0A66 and 07VI route against `lem-weil-l-adic-extension-integers-dvr`, `def-pc-perfect-ring-complex`, `def-weil-pbc-projective-module`, `lem-sc-dvr-saturation-line-smith-normal-form`, `lem-sc-bounded-above-projective-kprojective`, and `def-pur-derived-internal-hom`; the bounded finite-projective representative and ordinary dual-complex calculation are justified over the DVR.
- Step 7: checked the cycles/boundaries calculation against `lem-weil-pbc-ext-long-exact-first-variable`, `lem-weil-pbc-projective-ext-criterion`, `def-weil-pbc-projective-module`, and `lem-sc-dvr-saturation-line-smith-normal-form`; the short exact sequence and \Ext^1 torsion term have the stated indices and arrows.
- Step 8: checked the edge case (X=s=\operatorname{Spec}k), (d=0), (K=(\mathcal O_E/\varpi_E)_s) in degree zero; the dual complex has (H^0=0) while (H_c^0=\mathcal O_E/\varpi_E), so the integral degreewise form is genuinely degenerate. The zero object, field stages, and (n=1) cases are consistent.
- New nodes: none. The attempted `lem-sf-finite-coefficient-self-injective` was confirmed to duplicate `lem-weil-coefficient-frobenius` and remains removed; no Mathlib leaf or definition node was added.

Changes made in this second reading:

1. Replaced the stale one-step proof and nonexistent `sk-lem-sf-mate` citation with eight explicit steps covering the orientation, adjunction chain, actual pairing, field-stage degreewise result, and integral Ext calculation.
2. Regenerated `citations.json` from the repaired proof so every quote is verbatim from the cited node.
3. Updated the unit realization to record all eight proof steps and added the self-contained definition citations in the item statement.
4. Preserved the first worker's report and the existing no-new-node outcome.
