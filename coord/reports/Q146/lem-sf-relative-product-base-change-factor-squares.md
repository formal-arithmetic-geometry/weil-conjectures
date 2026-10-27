# Stage-1 report: lem-sf-relative-product-base-change-factor-squares

## Files written

- `dag/nodes/sec-six-functors/lem-sf-relative-product-base-change-factor-squares.json`: statement; split into seven proof steps using existing nodes only. The statement and its four statement dependencies are unchanged. Mathlib verdict: no match for the individual derived compact-support factor squares.
- `citations.json`: 16 citations, each quoting the part of the cited node's statement used in that step.
- `report.md`: this report. `prepare.py` is a sandbox-only preparation script; `searches.jsonl` is the search command's actual log.

New nodes: 0. New Mathlib leaves: 0. No unit record is changed: this item is a supporting lemma, not the unit's key statement.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and the relative-product, Kunneth, projection-formula and base-change coherence notions. The exact item tag has no hit. In `WeilConjectures/SixFunctors/Etale/Derived/Kunneth/Relative.lean`, `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct` at line 132 has `sorry` at line 142 and asserts existence of an isomorphism, not these six squares. `Kunneth.lean` explicitly says at lines 75–78 that the canonical comparisons and their base-change compatibilities are not stated. The closed assembly specializations in `Relative.lean` also assert existence and do not state this item's comparison equations. There is no attachment claim.

## WANTED

None. The proof uses the current blueprint's relative-product route and existing DAG statements. The supporting Stacks material and the blueprint sources are locally available. No SGA source was used.

## Problems found and changes

The imported item was unsplit and had no proof. Its detailed statement already specifies the exchange order in every beta comparison and the finite witnessed/higher coefficient domains; I retained these. The common broad assertion that coherence follows from pasting was replaced by the individual equations, especially the inverse-exchange square for factor 2. The latter needs two horizontal pastings of one Cartesian cube; naturality of exchange alone would not identify it. I used the actual pasting assertion in `fix-lem-exchanges`, rather than citing the composition theorem for a base-change compatibility that its statement does not give.

The canonical pullback symmetry is not an assertion of the tensor-pullback-isomorphism node alone. I instead use `lem-sfb-ringed-derived-monoidal-comparisons`, whose statement explicitly makes the canonical pullback symmetric strong monoidal, and `lem-pur-integral-coherence-tower`, whose statement explicitly gives strict-tower symmetry, composition, and the resulting completed equations. Both are recorded as generic tool uses in `split_report.tool_uses`.

The proof is agent-written expansion of coherence clause (iii); it does not claim that the brief blueprint proof itself contains all six calculations. There is no statement dispute or change of the unit route. The earlier blueprint proof's swapped order of the external tensor inputs is immaterial here because I follow the six arrows explicitly fixed in the unit statement, as this item requires.

## Unfinished work

None within this stage-1 item. The cited existing nodes retain their own status and proof obligations. No Lean file was written and no compiler, Lake, library build, or local DAG/preflight checker was run.

## Not duplicates

No new nodes were created. The whole-DAG keyword searches, and whole-blueprint searches for `relative product`, `factor squares`, `Cartesian cube`, `projection transformations`, `projection formula`, `pullback`, and `monoidal comparisons`, found the existing generic results used here. The relative-product and Kunneth coherence nodes give whole-composite assertions or different symmetry/associativity comparisons; they are not a finished project attachment for these individual factor squares. Reusing the exchange, PF, and monoidal-comparison nodes avoids new nodes for clauses of the item or elementary inverse-square algebra.

## Review by Q146

I read the chapter and unit records, the current `main-20261015` relative-product `_section.md`, and its `thm-sf-kunneth-relative.proof.md`. The unit's explicit coherence explanation says to use PF base change for the projection to Y along the base-changed b, PF for g along b, and pasting of the exchange squares. The delivered proof does exactly that. I also read the current blueprint `prop-sf-pf-coherence.md` and its proof, and `fix-lem-exchanges.md` and its proof. The first spells out the PF base-change square and its monoidal vertical maps; the second spells out the horizontal and vertical exchange-pasting laws. I cite their existing audited DAG statements, which specify the coefficient domains more carefully than those original source paragraphs.

For the generic monoidal ingredient I read `lem-sfb-ringed-derived-monoidal-comparisons` in full, together with the locally available Stacks `sites-cohomology.tex`, labels `lemma-pullback-tensor-product` (07A4), `lemma-derived-pullback-composition` (0D6D), and `lemma-adjoints-push-pull-compatibility` (0FPI). I read the full statement of `lem-pur-integral-coherence-tower`, and its strict-system/limit meaning against `lemma-derived-limit-is-ok` (0941) and the existing `lem-pur-completed-operation-tower-substitution` statement. These are already existing nodes; none is created or split here. I read the rational and algebraically closed clauses of `def-weil-derived-pullback-tensor-hom`, and the raw-localization and common-stage category definitions, to check that applying their functors to equations is legitimate and does not involve reduction of field coefficients.

Step 1 uses precisely the symmetric strong monoidality and monoidal composition assertions of `lem-sfb-ringed-derived-monoidal-comparisons` at finite coefficients, the explicit strict-system symmetry/composition equations and their completed limit equations in `lem-pur-integral-coherence-tower`, and the on-morphisms rational/common-stage formulas of `def-weil-derived-pullback-tensor-hom`. It invokes only A2–A4 of `def-sf-datum` for invertibility. The integral argument uses equality in the strict system followed by a functor; it never assumes that separate finite reductions detect derived integral morphisms.

Step 2 cites `fix-lem-exchanges`: its vertical-pasting formula inserts the compact-support composition comparison, and its clauses 2 and 4 explicitly include completed and transported forms. With the successive maps v and g, inversion of the composition comparison gives exactly factor 0. Naturality accommodates the final identification of the pulled-back H. The intermediate exchange order is g then v, as beta1 requires.

Step 3 cites the displayed PF base-change square of `prop-sf-pf-coherence` for v along y and its naturality, and the object-naturality of exchange in `fix-lem-exchanges`. I checked the first PF input is P on T and the second is L on Y, rather than interchanging them. Reversing the two invertible PF arrows is the written elementary multiplication by their inverses; applying Rg'! and outer exchange naturality gives factor 1.

Step 4 cites horizontal pasting and comparison of square data in `fix-lem-exchanges`. I checked both bottom composites are gy=bg', both upper composites identify T' with the same iterated fibre product, and both routes start at Lg'^*Lb^*Rf!K and end at Rv'!Lu'^*K'. The displayed equality is inverted only in the two horizontal f-exchange arrows, retaining the v/y and f/b comparison directions. Tensoring with L', applying Rg'!, and using the cited naturality give factor 2. This is a proof of the cube identity, not a citation of a mere naturality assertion as a substitute for it.

Step 5 cites the monoidal/symmetry statements established in step 1 and the exchange-naturality clause of `fix-lem-exchanges`. I checked that a has source Ly^*Lg^*Q and target Lg'^*Rf'!K', so naturality of signed symmetry has exactly the swapped-input beta4 comparison. Koszul signs are retained.

Step 6 uses `prop-sf-pf-coherence` for g along b, now with inputs (L,Q), plus its stated second-variable naturality at E_{f,b}. The latter is needed because the preliminary bottom PF uses Lb^*Q, whereas d4' uses Rf'!K'. The equation moving e through the inverse PF is written explicitly. Its two vertical comparisons are beta4 and beta5, with the exchange order g,f on beta5.

Step 7 uses the same finite, integral and transported pullback-symmetry equations from step 1. Naturality of symmetry with the two actual exchange maps gives the final displayed equality: beta5 has order g,f and beta6 has order f,g. This proves factor 5 without suppressing the order of coefficient or exchange comparisons.

For hypotheses, all schemes are separated finite type over the fixed field; their fibre products remain in that setting. Maps between these separated finite-type k-schemes are separated finite type, so b and its pullbacks meet the domain in `fix-lem-exchanges`. The datum supplies operations on the stated finite-Tor categories, hence P, Q and every PF input have the required domain. The item explicitly restricts finite compact-support assertions to etale-origin witnessed inputs and restricts higher coefficients to their completed/transported domains; I did not replace these by arbitrary pro-etale inputs. No uniform amplitude, lattice, or stage requirement was removed. Scalar localization preserves equations, and the algebraically closed equation is represented over one common finite coefficient field, including after further extension.

I checked zero inputs and empty fibre products: all maps are the corresponding natural comparisons on zero objects and the same equations hold. When b is the identity, the identity-pasting clause and canonical comparisons make every square the naturality/identity square. Taking either f or g to be an identity reduces the relevant exchanges/composition maps to their identity forms; the PF-inverse directions and both symmetries remain correctly typed. These checks found no false clause.

Finally I checked delivery-errors B–E against the files. There are no new statement-only nodes to restate clauses, duplicate a fact, hide an argument, or require additional searches. Every non-elementary assertion in the proof is backed by a cited statement whose text I opened; every use has its verbatim quotation in citations.json. The local quote comparison against the current read-only DAG passed. The largest step has 1393 characters, so no step exceeds the 2000-character review threshold. The five new searches in searches.jsonl were actually run with msearch.py; their displayed hits concern module base change, unrelated Cartesian braidings, homological tensor conditions, or compactly supported functions, and none states this item. The inherited search records are preserved as required.
