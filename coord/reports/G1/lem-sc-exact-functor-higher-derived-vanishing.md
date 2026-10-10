1. Files written

- `dag/nodes/sec-curve-estimates/lem-sc-exact-functor-higher-derived-vanishing.json` — item split into three proof steps; no new nodes.

2. Attachments

None.

3. WANTED

None. The cited Stacks source is the imported source named by the existing node.

4. Problems found

The item was unsplit, with an empty proof. The surrounding Cohomology Lemma 02UV node already relies on it for the vanishing of higher direct images. The DAG already contains the exact-functor/cohomology statement needed for the argument, so I did not duplicate it as a new node. No statement or blueprint error was found.

5. What remains

Nothing in the split itself remains unfinished.

## Review by G1

I read the item's source entry for Stacks Derived Categories, Lemma 015F, and checked the statement against the existing node: abelian categories with enough injectives, an exact additive functor, and vanishing of all positive right derived functors. I also read the three cited node statements. `def-sp-left-exact-additive` explicitly defines the right derived functors as the cohomology of the functor applied to an injective resolution; `def-sp-injective-resolutions` explicitly says that such a resolution has cohomology concentrated in degree zero; and `lem-weil-pbc-exact-functor-complex-cohomology` explicitly gives the natural isomorphism H^r(F(K)) ≅ F(H^r(K)) for an exact functor.

Step 1 uses those statements to choose the resolution and record its positive cohomology vanishing; exactness implies the left exact/additive hypotheses required by the derived-functor definition. Step 2 applies the exact-functor cohomology isomorphism to obtain H^q(v(I)) ≅ v(0) = 0 for q > 0. Step 3 uses the defining equality R^qv(M) = H^q(v(I)) to conclude the result. The only elementary part is the zero object calculation v(0)=0 and transport of an isomorphism to a zero object; all non-elementary inputs are cited. I searched the whole DAG and blueprint for an existing node with the item's statement or the same source result and found none; the exact-functor/cohomology fact was already present and is cited rather than duplicated. I checked the edge cases q=1 and the zero object M: the resolution argument gives the same vanishing, and no positivity or boundedness hypothesis is omitted.
