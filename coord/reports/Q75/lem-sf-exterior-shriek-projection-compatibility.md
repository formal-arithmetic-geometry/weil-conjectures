# Stage 1 report: lem-sf-exterior-shriek-projection-compatibility

## Files written

- `dag/nodes/sec-six-functors/lem-sf-exterior-shriek-projection-compatibility.json`: repaired split statement; no new nodes.
- `citations.json`: verbatim statement quotations for every cited node in every proof step.

## Attachments

None. I searched the slopmaster2 source for the item statement and blueprint tag and found no sorry-free declaration stating this item.

## WANTED

None.

## What was wrong and what changed

The returned delivery directly cited the existing projection-coherence node in step 3 (and again in step 5), whose metadata has an SGA 4 external source. This violated the project route lock, which permits no SGA source except SGA 5 for the specified pairing. I removed that dependency from the proof and `proof_deps`. Steps 3 and 5 now use the existing `lem-sf-exterior-projection-kunneth` statement: its displayed exterior-product projection identity is applied to `(f,id_Z)`, with the second source factor the tensor unit and second target factor `Q`; the specified exchange and identity-factor maps then give the inverse-projection base-change identity used by the item. I read that node's complete statement and checked that it supplies the product projection equality, while `def-exchange-projection`, `fix-prop-projection-formula`, and `lem-pur-derived-pullback-tensor-iso` supply the named maps, invertibility, and reassociations. No SGA 4 or SGA 4½ source remains cited by this split.

The item statement, hypotheses, coefficient category, and five-step route are otherwise unchanged. I regenerated `citations.json` from the current proof uses, with each quote copied verbatim from its node statement.

## Review by Q75

I read the item, its ancestor unit `sk-thm-sf-kunneth-verdier`, the alpha paragraph of the main-20261015 blueprint, Scholze's *Six-Functor Formalisms*, Lecture III, Remark 3.13, and the complete statements of every cited node. The finite-field and finite-Tor domains, separated finite-type hypotheses, product square, exchange map, projection maps, and naturality clause agree with the item statement. Step 1 uses the actual operation domains, finite-level exchange isomorphism, and projection-formula invertibility. Step 2 expands the specified exchange/projection composites and uses the canonical pullback-tensor comparisons. The repaired step 3 uses the exact exterior-product projection identity of `lem-sf-exterior-projection-kunneth` in the identity-factor specialization; I checked the source and target factors and then read the exchange through `def-exchange-projection` and `def-cbc-exchange-map`. Step 4 uses the unit and associativity equations in `def-sfb-projection-formula` and the invertibility from `fix-prop-projection-formula`. Step 5 substitutes the repaired step-3 identity into step 4 and uses naturality of the specified maps and reassociations. Every cited statement says the fact taken from it, every use occurs in `proof_deps`, and the graph is acyclic.

I checked the edge cases `Z=Spec k`, `Q=A`, `f=id`, zero objects, and shifts; the maps reduce to the corresponding identity or projection comparisons. The repaired proof cites no SGA source, and no new lemma or statement correction is needed.
