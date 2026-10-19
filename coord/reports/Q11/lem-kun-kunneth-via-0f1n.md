## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-kunneth-via-0f1n.json`: statement; split into seven proof steps using existing nodes; Mathlib searches found no exact match or one-line specialization.
- `citations.json`: 33 step/node entries, each copied verbatim from the cited statement.

## Attachments

None. I searched the slopmaster2 project by the item id, blueprint tag, `0f1n`, Kunneth, projection, and counit terminology, and checked `dag/lean_names_upstream.json`. The nearest declaration, `AlgebraicGeometry.Etale.nonempty_iso_kunneth` in `WeilConjectures/SixFunctors/Etale/Derived/Finiteness/Kunneth.lean:72`, asserts existence of an isomorphism and has `sorry`; it neither states the equality of canonical morphisms nor supplies an attachment. Upstream master was treated only as reference material.

## WANTED

None. The master blueprint proof, current main-20261015 statement, and relevant Stacks sources are present locally.

## Corrections and scope

The imported proof cited `lem-kun-03qu-sep-closed` for an equivalence of sheaves with modules, whereas its statement gives only higher-cohomology vanishing. I replaced that use by the existing field sheaf/Galois equivalence and evaluation-on-fields statements, specialized to the trivial absolute Galois group. The imported use of `lem-kun-0f12` likewise did not supply an adjunct formula; `def-kun-constant-projection-morphism` supplies that actual formula.

The original hypotheses and equality are retained. The added statement paragraph specifies the existing canonical map: exchange, symmetry, the usual projection map, and symmetry inside pushforward. It also fixes the direction of the Leray comparison. This is a normalization of the source's canonical arrows, not a new isomorphism assertion or a statement dispute. Step 4 checks this normalization directly by its counit adjunct. No bounded-below version has been applied to unbounded objects.

I checked the chapter and unit records and the current unit section. The route remains the constant projection formula, the 0F1N tensor/exchange map, and Leray, as in the original proof; no unit metadata is changed. The unit record's pre-existing `realized` entries concern another item and are not this item's assignment. The generic off-unit tools needed for the point identification and unbounded functor normalizations are declared, with reasons, in `split_report.tool_uses`.

## Unfinished

No missing argument in this one-level split. Zero new nodes; zero Mathlib leaves. Existing dependency nodes retain their own work. No Lean was written or compiled, no shared repository file was changed, and no delivery was pushed.

## Not duplicates

No new nodes were created. Whole-DAG and blueprint searches for Kunneth maps, projection-formula comparisons, `0F1N`, and pulled-back counits found the existing definitions and lemmas now cited. `lem-kun-kunneth-map-agrees` assumes a proper first factor and identifies an inverse via proper base change; it does not state this item, which has no properness hypothesis. `thm-kun-0f1p` asserts the Kunneth isomorphism and does not give this comparison of its canonical map. Consequently `blueprint.same_as` is empty.

## Review by Q11

I read the current main-20261015 item and unit, the master item's three-paragraph proof, and Stacks `etale-cohomology.tex` at Tags 04JQ, 04JM, 0F12, 0F1J, and 0F1N. I read `sites-cohomology.tex` at Tags 0B56, 07A4, 07A6, and 0D6E, `sites-modules.tex` at 03D8, `derived.tex` at 08BJ, `morphisms.tex` at 01T6, and `schemes.tex` at 01KO. There are no new-node sources to audit. No SGA source is used.

Step 1 uses the statements of `lem-exc-abelian-sheaves-gmodules` and `lem-exc-field-sections-stalk-invariants`: the former really supplies the equivalence, and the latter really supplies evaluation at `Spec k` as invariants. Taking the separable closure to be k makes the group trivial; k need not be perfect or algebraically closed. I wrote out the scalar-endomorphism transport to retain constant module coefficients, exactness of the equivalence, and the passage to unbounded complexes. The constant-sheaf and RΓ definitions and the pullback-constant lemma give precisely the remaining identifications. This repairs the imported 03QU citation failure.

Step 2 explicitly checks the hypotheses previously omitted. The finite-type definition gives finite affine covers, and the tensor algebra chart calculation gives finite type of W. The finite-type-over-Noetherian node gives local Noetherianity and quasi-compactness; the affine-open-ring and affine-Noetherian-space statements give Noetherian chart spaces. The open-cover argument written in the step proves quasi-compactness of all relevant opens, without assuming separatedness of X or Y. The affine-cover criterion supplies quasi-separatedness of X. The diagonal of p has Noetherian source W, so the same open argument proves its quasi-compactness. The two precise clauses of `lem-kun-0f10` give finite cd(X) and cd(p), allowing the actual hypotheses of 0F12 and unbounded Leray. Finally I matched all six objects/arrows of 0F1N to the product diagram and verified that no Tor-amplitude or boundedness condition is needed there.

Step 3 uses the constant projection *definition*, whose statement says that its map is the adjunct of the tensor comparison followed by the counit. I checked its counit normalization against the K-injective Hom formula in the Kunneth-map definition. The inverse-image monoidal lemma supplies the invertible bifunctorial tensor comparison. This fixes the second imported citation gap without inventing a lemma that restates the item.

Step 4 uses exactly the mate formula in the exchange definition and the adjunct formula in the projection-map definition. I tracked the order of factors: the right projection formula requires a symmetry before applying it and a symmetry under Rp_* afterwards. Naturality moves these symmetries past the counit, leaving `1 tensor counit`; the equation `counit_p composed with p^{-1}(xi) = delta` then removes the exchange mate. The displayed beta has the correct source `p^{-1}(E tensor C)` and target B. This is an elementary calculation from the four cited statements, not an appeal to the proof of 0F1N.

Step 5 checks the Leray comparison against the actual adjunctions, rather than assuming that an arbitrary object isomorphism preserves adjuncts. The right-adjoint-preserves-K-injectives statement applies because the coefficient inverse image is exact, as the Kunneth-map definition explicitly records. Thus p_*I is K-injective and both global-sections calculations use the same complex. The module-linear composition node explicitly includes preservation of composite adjunction units, which is the compatibility used here. The resulting adjunct is beta composed with p^{-1}(rho).

Step 6 supplies the compatibility previously hidden in “composing adjunctions”: both canonical tensor/composition paths send local tensor generators to the same pair. I wrote out the identification of constant-ring module pullback with inverse image, its exact derived specialization, passage through degrees and total differentials, and the bidegree sign check for symmetry. The generic derived-tensor-pullback statement really gives K-flat flat-term representatives and their preservation under pullback, and the tensor-descent statement really gives uniqueness of transformations on those representatives. Its remaining equation is the tensor bifunctor composition law. Step 7 compares with the *statement* of the Kunneth-map definition, including both gamma composition maps, and applies injectivity of the Hom bijection.

For delivery-errors B, there are no statement-only new nodes to check, no new ids or duplicate-tag pairs, and no unsupported Mathlib leaf claims. Every Mathlib query in the item was run with `msearch.py` and recorded with its exact query text. Two semantic phrasings plus Loogle, LeanSearch, and source grep found ordinary tensor, cotangent, and structure-sheaf results, not this derived etale comparison. For C, I opened every cited statement and checked that its quote covers the use; the two original C4 failures were repaired, generic tool uses are declared, and proof_deps is exactly the union of uses. For D, all seven steps carry the argument and no clause is moved to a renamed child. For E, I checked n=1 (zero coefficient category), E or K zero, X or Y empty, X=Y=Spec k (identity counits), shifted complexes (the two symmetry signs cancel), and finite-type nonseparated schemes (the finiteness argument uses Noetherianity, not properness or separatedness). Unboundedness is retained in all three canonical maps and the K-injective computation.

## Second reading by Q11

- Statement: compared line by line with the current `main-20261015` blueprint node and Stacks `0F1N`; the hypotheses, product diagram, canonical Künneth map, and Leray composite agree. I removed the worker's appended normalization paragraph because it changed the imported proposition; the normalization remains proved in steps 3–5.
- Step 1: checked against Stacks `04JQ` and `04JM` and the quoted field-point/evaluation nodes; the trivial absolute Galois group specialization and module-scalar transport support the constant-coefficient identification. Verdict: sound after moving the notation definitions from the statement into this step.
- Step 2: checked against Stacks `0F10`, `0F12`, `0F1N`, Morphisms `01T6`, Schemes `01KO`, and every quoted finiteness node; finite-type product charts, Noetherian open quasi-compactness, qcqs of the projection, and finite-cd hypotheses are all present without separatedness. Verdict: sound.
- Step 3: checked the constant projection adjunct against `def-kun-constant-projection-morphism`, `def-kun-kunneth-map`, and inverse-image monoidality `07A4`; the displayed counit composite is the defining adjunct. Verdict: sound.
- Step 4: checked the exchange mate against `def-kun-unbounded-exchange`, the projection-map definition (`0B56`), tensor symmetry, and inverse-image monoidality; the two symmetries and counit yield the displayed beta with the correct factor order. Verdict: sound.
- Step 5: checked the Leray normalization against `lem-kun-leray-unbdd`, K-injective preservation (`08BJ`), the K-injective Hom formula in `def-kun-kunneth-map`, and module-linear composite adjunctions; the adjunct is beta composed with the projection counit map. Verdict: sound.
- Step 6: checked tensor and inverse-image composition coherence against `07A4`, the module-linear composition node, derived tensor pullback/descent, and constant pullback; the local-generator calculation and total-complex signs give the stated composite. Verdict: sound.
- Step 7: checked the final identification against the full statement of `def-kun-kunneth-map`; equality follows by injectivity of the same adjunction Hom bijection. Verdict: sound.
- New nodes: none; consequently there were no new statements, Mathlib leaves, sources, or duplicate nodes to audit. All cited existing statements were opened and their quoted text in `citations.json` checked against the uses.
- Changes made: restored the source-faithful statement and its original four statement dependencies, introduced `S,W,p,q,b,c,a,\\Lambda,Q,B,P` at the start of proof step 1, and reclassified the substantive mate and tensor-coherence calculations in steps 4 and 6 as non-elementary (their dependencies are explicitly cited). No Lean or shared-repository files were changed.
