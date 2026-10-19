# Stage-1 report: lem-trf-free-subtraction-flatness

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-free-subtraction-flatness.json`: statement, split; Mathlib searches found no direct match.
- `dag/nodes/sec-trace-formula/lem-trf-flat-fp-geometrically-integral-projective.json`: statement-only unsplit input for Stacks Tag 05FT; Mathlib searches found no direct match.
- `dag/nodes/sec-trace-formula/lem-trf-local-generic-basis-universal-injective.json`: statement-only unsplit input for Stacks Tag 05I3; Mathlib searches found no direct match.
- `dag/nodes/sec-trace-formula/lem-trf-universal-injective-check-stalks.json`: statement-only unsplit input for Algebra Tag 05CL; Mathlib searches found no direct match.
- `citations.json`: verbatim quotations for every cited node in each item proof step.

## Attachments

None. I found no sorry-free declaration tagged `(blueprint: lem-trf-free-subtraction-flatness)` or stating this item exactly in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`.

## WANTED

None.

## What was wrong or incomplete

The imported item had no proof and its source place combined the local Stacks Tag 05I3 argument with the Algebra Tag 05CL globalization. The DAG had no node stating the non-Noetherian projectivity input (Tag 05FT), the local generic-basis criterion (Tag 05I3), or the stalkwise universal-injectivity criterion (Tag 05CL), so I created those three unsplit statement nodes after searching the DAG and blueprint for duplicates. The item statement itself was mathematically retained unchanged.

## What could not be finished

The three supporting nodes are intentionally statement-only and remain in the stage-1 queue for later workers; no Lean code, compiler, Lake, or build tool was run.

## Not duplicates

- `lem-trf-flat-fp-geometrically-integral-projective` vs `lem-weil-pbc-flat-mod-injective`: the existing node is a Noetherian-local module-injectivity theorem; the new node is the non-Noetherian projectivity theorem for the algebra (A).
- `lem-trf-local-generic-basis-universal-injective` vs `lem-weil-pbc-flat-mod-injective`: the existing node assumes a Noetherian target algebra and injectivity modulo a maximal ideal; the new node uses a flat finitely presented algebra with geometrically integral fibres and a basis at the fibre generic point.
- `lem-trf-universal-injective-check-stalks` vs existing localization or flatness nodes: the new node characterizes universal tensor-injectivity of an (A)-module map by all (A_mathfrak q) localizations, which no existing node states.

## Review by Q64

I read the item node, the sec-trace-formula chapter and unit records, Stacks flat.tex Tag 05I3 (including its complete proof), flat.tex Tag 05FT, and Algebra Tag 05CL in algebra.tex. I also read the statements of every dependency cited by the item and checked that each quote in `citations.json` is copied verbatim from its node.

Step 1 localizes (R) at an arbitrary (mathfrak p), identifies the generic fibre prime with the maximal ideal extension, and applies the new local Tag 05I3 node using exactly its flatness and residue-basis hypotheses. Step 2 uses the new Tag 05CL node to pass from universal injectivity after all base-prime localizations to injectivity after tensoring with every (R)-module. Step 3 applies the same local criterion at an arbitrary (mathfrak q) for the forward implication; the reverse implication is the explicit short-exact-sequence tensor diagram chase, with the localized free module flat because (A) is (R)-flat. I checked (r=0), the zero ring/empty spectrum cases, and the case (H_mathfrak q=0); all are covered by the same statements. The projectivity node is a genuine Tag 05FT input to the proof of the local criterion, rather than a restatement of the item. All Mathlib searches were run through `msearch.py` and recorded in the three new nodes and the item.

- lem-trf-local-generic-basis-universal-injective vs lem-trf-free-subtraction-flatness: the new node is the local-ring implication (1)⇒(2) of Tag 05I3, while the item globalizes over all base primes and also states the converse flatness implication at every q.
- lem-trf-universal-injective-check-stalks vs lem-trf-free-subtraction-flatness: the new node is the general algebraic stalkwise characterization from Tag 05CL, while the item applies it to the specific generic-basis map and combines it with the local 05I3 flatness equivalence.
