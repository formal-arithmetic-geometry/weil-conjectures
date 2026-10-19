# Stage-1 worker report

1. Files written:
   - `dag/nodes/sec-proetale-coefficients/lem-sfb-left-resolution-bicomplex-total-exists.json`: statement split into four proof steps; Mathlib verdict for the item is no exact match.
   - `dag/nodes/sec-proetale-coefficients/lem-sfb-left-resolution-chain-complex-map-zero.json`: statement node, Mathlib exact match `CategoryTheory.Abelian.LeftResolution.chainComplexMap_zero` at `Mathlib/Algebra/Homology/LeftResolution/Basic.lean:167`.
   - `citations.json`: verbatim statement excerpts for every cited node in every proof step.
   - `report.md`.
2. Attachments: none.
3. WANTED: none.
4. The imported item was unsplit. I did not change its mathematical statement or hypotheses. I found no duplicate node for `chainComplexMap_zero`; the whole blueprint search for the zero-input support fact returned no match. The existing `lem-sfb-left-resolution-additive-total-transport` node supplies the generic total-existence result, so no duplicate total-existence node was created.
5. Nothing remains unfinished.

## Review by N1

I read the item's source, `WeilConjectures/FromJoel/Algebra/Homology/LeftResolution/CochainComplexMinus.lean`, lines 32–108, including the definition of `bicomplexFunctor`, the support instances, and all three `HasTotal` instances. I also read the unit and chapter records, the parent bounded-minus node, the complete statements of `lem-sfb-left-resolution-objectwise-cochain`, `lem-sfb-left-resolution-additive-total-transport`, `def-sp-abelian`, `def-weil-preadditive-category`, and `def-weil-pbc-additive-functor`. The source variables provide a preadditive `C` with a zero object and finite coproducts, an abelian `A`, a full faithful additive `\\iota`, and a zero-morphism-preserving left resolution, exactly as required by the item.

Step 1 uses the objectwise node only for the construction and functoriality of `R`; its statement explicitly gives the cochain-complex resolution functor and says that `R` acts on morphisms. This matches the source's `bicomplexFunctor` definition, whose term at `(p,q)` is the `q`-term of `R(K^p)`, followed by termwise application of `\\iota`.

Step 2 uses the objectwise node's explicit sentence that every `R(X)` is strictly supported in degrees `q <= 0`, with the same assertion after applying `\\iota`. This is exactly the source support instances at lines 52–64, so it proves the claimed vanishing for `q > 0` without adding a hypothesis.

Step 3 uses the new Mathlib leaf `chainComplexMap_zero` and the objectwise functor statement. For `p>b`, `K^p` is the zero object, whose identity is its zero morphism. The Mathlib equation identifies the induced resolution chain map with the zero chain map; functoriality identifies that same map with the identity of the resolution of `K^p`, so every component is zero. The extension from natural resolution degrees to integer cochain degrees preserves these zero components, and termwise `\\iota` preserves the resulting zero morphisms/objects. This is the mechanism represented by the source's `K.IsStrictlyLE` support instances at lines 66–90. I checked the edge cases `K=0` and a complex concentrated in one degree: the asserted upper support is immediate in both cases.

Step 4 uses the existing additive-total-transport statement. Its support hypothesis is precisely “zero whenever `p>b` or `q>0`,” established in Steps 2–3. The ambient category `C` has the required zero object and finite coproducts by the item's hypotheses; `A` is preadditive by the definition of abelian category; and `\\iota` is additive by the cited additive-functor definition. The theorem therefore gives both diagonal total complexes with shape `up(\\mathbb Z)`, exactly as the source's `HasTotal` instances at lines 92–108.

The only new node is strictly smaller than the item and is an exact Mathlib interface lemma, not a restatement of the item's bicomplex support or total-existence conclusion. I ran LeanFinder, Loogle, grep, and LeanSearch searches for both the item and this new node; the item has no exact Mathlib match, while the new node matched `CategoryTheory.Abelian.LeftResolution.chainComplexMap_zero` exactly. All citation quotes in `citations.json` are copied verbatim from the cited node statements.
