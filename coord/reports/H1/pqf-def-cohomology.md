# Stage-1 report: pqf-def-cohomology

Files written:

- `dag/nodes/sec-abelian-varieties/pqf-def-cohomology.json`: item, split; no new child nodes.
- `citations.json`: verbatim dependency quotes for all three proof steps.

Attachments: none.

WANTED: none.

The item was not already stated by one exact, sorry-free project declaration. The Lean source has separate declarations (`AlgebraicGeometry.Scheme.Modules.H`, `AlgebraicGeometry.Scheme.Modules.higherDirectImage`, and the long-exact cohomology lemmas), so it cannot be attached as a whole. Existing DAG nodes already cover the needed general constructions, avoiding duplicate nodes.

## Review by H1

I read the item node and the surrounding abelian-varieties unit, then checked the relevant Lean source in `AlgebraicGeometry/Cohomology/Defs.lean`, `AlgebraicGeometry/Cohomology/DirectImage.lean`, and `AlgebraicGeometry/Cohomology/LongExact.lean`. The first proof step cites `def-sc-ringed-space-module-cohomology`; its statement explicitly defines module cohomology from an injective-resolution global-sections complex and identifies it with right derived global sections. The second cites `def-pc-ringed-spaces-derived-direct-image`; I checked that its hypotheses are a morphism of ringed spaces and that it constructs the derived pushforward from a K-injective resolution, which specializes to a scheme morphism and gives the higher derived functors. The third cites `lem-weil-pbc-right-derived-universal-delta-functor`; its statement supplies the connecting morphisms for every short exact sequence and the exact delta-functor sequence, which is the long exact cohomology clause. Each citation quote is copied verbatim into `citations.json`. I verified that no existing node states the exact combined item and that the Mathlib searches found only general `Sheaf.H` and derived-functor primitives, not this project definition.

## Second reading by H1

- Item statement: checked the cohomology and module higher-direct-image clauses against Stacks `01DZ`, `015B`, and `079W`; hypotheses and conclusions agree. The external source metadata was corrected from the unrelated `01EO`/`01EY` tags.
- Step 1: checked against `def-sc-ringed-space-module-cohomology`; its injective-resolution, global-sections, resolution-independence, and right-derived claims supply the step.
- Step 2: checked against `def-pc-ringed-spaces-derived-direct-image`; its ringed-space morphism hypotheses and K-injective construction supply the derived pushforward.
- Step 3: checked against `lem-weil-pbc-right-derived-universal-delta-functor`; its connecting maps and exact delta-functor sequence supply the long exact clause.
- Existing-node audit: grep over `dag/nodes` found a broader ringed-space cohomology node and a separate functoriality node, but no node combining all three clauses; no child node is needed.
- Small cases: the empty scheme and `\\operatorname{Spec}(k)` give the zero and exact-global-sections cases; degree zero agrees with ordinary sections.
- Mathlib audit: recorded LeanFinder, Loogle, and grep searches found only general sheaf-cohomology and derived-functor primitives.
- Change made: corrected the item source metadata to Tags `01DZ`, `015B`, and `079W`, replacing the incorrect `01EO` and `01EY` references.
