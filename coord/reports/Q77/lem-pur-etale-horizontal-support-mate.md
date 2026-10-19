# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-etale-horizontal-support-mate.json`: ten-step diagonal proof of the item, with the correct typed inverse of delta.
- `citations.json`: verbatim statement excerpts for each of the 21 step/node citations.
- `report.md`: this repair and self-review.

Zero new nodes and zero new Mathlib leaves. The rejected `lem-pur-etale-compact-support-tower-mate` is withdrawn from the delivery. Its original JSON, the returned item, report and citations remain under `repair-history/` in the sandbox for historical reference; `searches.jsonl` is retained unchanged. Neither those archives nor the scratch Python scripts are delivery files.

## Repair of D1/D2, G2 and the typing/B1 points

The return is correct: the proposed tower-mate helper was equivalent to the item after transporting an adjunction. I removed its citation and its delivery file. No replacement statement-only node carries the missing calculation. The item now gives that calculation, using the existing open-horizontal theorem on a different square: the pullback of the clopen diagonal of the separated etale base map.

Steps 2–4 set up the two self-base-change squares and identify their transported units with diagonal insertions. Step 5 applies the existing open-horizontal mate to the diagonal square. Steps 6–7 calculate how this insertion passes through the comparison for the vertical map, using explicit naturality, composite-base-change and associativity equations. Step 8 writes the two composition/base-change equations for the two factorizations of the original composite. Step 9 substitutes them and cancels by the adjunction triangle. Thus the substantive calculation remains in the item's proof. This changes the argument, rather than rebasing or renaming the returned helper.

Step 1 now writes, with ordinary right-to-left composition,

`delta_L^{-1} = F_f(d_{u',L}) ∘ alpha_{f,u'}^{-1} ∘ alpha_{u,f'} ∘ d_{u,N}^{-1}`.

This repairs the ill-typed order specifically identified in the return. The B1 concern is removed with the rejected helper: there is no new unsplit node whose statement contains a proof sketch. The item's statement is byte-for-byte unchanged, including finite coefficients, Noetherian hypotheses, separated finite-type maps, arbitrary unbounded ordinary-etale complexes and the specified compactification maps.

## Attachments and searches

No attachment. I searched the slopmaster2 `WeilConjectures/` source by the item identifier, the blueprint tag, horizontal/mate terminology and the etale compact-support and sum-extension notions. The exact item is not a sorry-free declaration. `SixFunctors/Etale/LowerShriek/EtaleMap.lean` constructs sum extension and its sheaf adjunction, not this compact-support compatibility. `SixFunctors/Finite/BaseChange.lean` concerns finite direct-image base change, not the item.

The existing item's recorded searches are preserved. I read the retained `searches.jsonl`: its generic mate-equivalence, condensed adjunction and ordinary sheaf pullback hits do not supply this normalized geometric equality. There is no new mathematical statement requiring a new Mathlib search. The rejected helper's searches remain historical evidence in the log and archive; they are not relabelled as searches for a different node.

I searched the whole DAG for diagonal, graph, proper/open interchange and horizontal mate statements, and used the existing clopen-section, etale base-change, separated finite-type base-change and locally-Noetherian finite-type nodes. `tools/blueprint_refs.py ancestor` confirms `thm-pur-composition-coherence`; whole-blueprint searches for `etale diagonal` and `horizontal support mate` returned no same-statement blueprint node. The filled blueprint ancestry and `same_as: []` are retained.

## Not duplicates

There are no new nodes. The rejected equivalent helper is not in the delivery. The open-horizontal theorem is cited as an existing, strictly narrower theorem, applied to the diagonal square; its dependency closure has no path back to the item.

## Sources and route

I read the current blueprint `main-20261015` proof of `thm-pur-composition-coherence`, Step 1's last paragraph on composition compatibility, and the whole `sk-thm-smooth-purity` unit. This item supplies a comparison calculation below that step; it does not change the unit's diagonal/deformation/vector-bundle route.

The local Stacks sources read were `more-etale.tex`, Tags 0F7J (`lemma-shriek-composition`), 0F7K (`lemma-pseudo-functor`), 0F7L (`lemma-base-change-shriek`), and its `lemma-shriek-proper-and-open`; `etale-cohomology.tex`, Tags 03S6 (`lemma-shriek-base-change`) and 0F4L (`lemma-shriek-into-star-separated-etale`); `etale.tex`, Tag 024T (`proposition-properties-sections`); and `schemes.tex`, Tag 01KT (`lemma-section-immersion`). The proof is marked agent-written: the self-base-change reduction is written here using the DAG's precise unbounded comparison interfaces; I do not attribute the entire item verbatim to a Stacks lemma.

The support-map and quasi-finite comparison tools have the same accepted foundational roles as in the return. I additionally declare as generic geometry tools the existing section-clopen theorem, etale base-change theorem, separated finite-type base-change theorem and finite-type/locally-Noetherian theorem. They verify the hypotheses of auxiliary diagrams. They do not replace a purity, trace or duality step. The open-horizontal mate lies on `sk-prop-an`, which this unit uses. No SGA source is used.

## Review by Q77

I opened the statement of every cited node and checked what each step takes from it. The decisive change is that the diagonal square has open horizontal arrows: the existing open theorem therefore applies with its actual hypotheses, while the original etale-horizontal item is proved rather than cited under another name.

Step 1 uses the unbounded compact-support comparison node for the specified alpha and C and the etale adjunction node for the whole derived adjunction. Taking the inverse reverses the four factors, which I checked from the source and target of each. The transported counit absorbs `F_f(d_{u'})` on the correct side.

In Step 2 the etale finite-limit/base-change statement gives the etale projections; the separated finite-type base-change statement gives their finiteness and separatedness. The two diagonals are sections of these separated etale projections, exactly the hypotheses of the clopen-section node. The locally-Noetherian finite-type node gives local Noetherianity of V and P, and their quasi-compactness gives finite affine covers. The Cartesian square for h along t is a fibre product of schemes, not just a statement about underlying points. Compactifications of h, b and the etale projections are obtained by pulling back the compactifications of f', the given composite, u and u'; t and e have their open compactifications.

Steps 3–4 use the quasi-finite comparison's stated composition formula and nested-lift normalization to express J and J' as diagonal-summand inclusions. The support-map node's clause (1), not its tensor clause, identifies the compactification exchange with the specified sum-extension base-change map. I checked the unit on the presheaf lift summands and its compatibility with restriction before passing to sheaves. The etale adjunction node explicitly says the exact termwise functor is adjoint on the entire unbounded categories, so this is an equality of chain maps descended to D, not an inference that degreewise or stalkwise evaluation is faithful on derived morphisms. The open compactification of t or e makes its proper-support comparison the ordinary open-extension identification.

Step 5 uses the full assertion and normalization of the open-horizontal mate node, with f there equal to h here, u there equal to t, and its pullback equal to e. Its input is a*L and its resulting source is F_t F_f' L. All four schemes are Noetherian by Step 2. This theorem actually states equation (O); the proper/open interchange definition alone would not suffice.

Step 6 uses the comparison node's composite-base-change and identity clauses: p1 composed with t is the identity, so t*Q is the inverse of C_{h,t}. Substitution into (O), plus the naturality of the evaluation counit, gives the two displayed lines. Step 7 uses the same comparison node's explicit associativity assertion, first for (p2,h,e), then (p2,t,f'), and finally (f',v,e). I checked all three intermediate sources: the common map is F_b(epsilon_e) alpha_{b,e}^{-1}, from N to F_b a*L. This proves (D) by the displayed calculation; it is not an unproved compatibility moved into prose.

Step 8 invokes precisely the stated compatibility of C with alpha, for the two factorizations uf' and fu'. Both equations end in F_b a*L. The third equation is naturality at the transported counit. In Step 9 I substituted B2, B1, and D in that order. The remaining factor is u'^*(epsilon^c_{u'}) eta^c_{u',u'^*M}, so the triangle identity applies with exactly L=u'^*M. Step 10 uses invertibility of C and the adjunction bijection. All arbitrary inputs stay unbounded throughout.

For the B–E checks: no new nodes, no new statement claims, no duplicate or equivalent helper, all statement notions and imported metadata retained, every non-elementary ingredient cited by a statement that contains it, and no path from the cited open theorem to this item. I checked the displayed equations on u=id, on a split finite etale cover (J selects the diagonal matrix entries and the triangle cancels that inclusion), on an open immersion (the diagonal selection is the identity), on the empty base and on zero complexes. None requires invertibility of the ring order, constructibility, a dimension bound, or faithfulness of derived evaluation.

All ten proof steps are shorter than 2000 characters. The only comparison calculated inside them is the explicit chain of naturality and associativity substitutions in Steps 6–9, with no additional geometric lemma left unstated. I retained the search history and the old files in the sandbox archive, regenerated citations against the current shared statements, and checked the statement against both the returned item and current shared item. No Lean, compiler, Lake, live launcher edit, shared-repository write, or git command in the shared repository was used.

## WANTED

None.

## Validation

The required initial dry run of the retained returned split exited OK at `166f2b32ff`; it was diagnostic only and was not pushed. The repaired ten-step split passed the required server dry run at `4dcc861568` (preflight OK, not pushed). The push command repeats the preflight on the final delivery.
