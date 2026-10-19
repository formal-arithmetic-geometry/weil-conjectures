# Stage-1 report: lem-trf-localized-finite-module-spread

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-localized-finite-module-spread.json`: statement node, split; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement quotes for every cited definition in every proof step.

Attachments: none.

WANTED: none.

The imported statement is correct. I did not change its hypotheses or conclusion. The imported node had no proof; I supplied the inverse-image-of-kernel proof from Stacks Tag 05N5, clause (1), specialized to the powers of `f` and `I=0`. No duplicate node was created: the localization and finite-generation notions already have definition nodes, and the finite-module descent assertion itself is not stated elsewhere in the DAG. The item is not a target node and no statement dispute is needed. No off-unit tool lemma is used.

Nothing remains unfinished.

## Review by Q49

I read the item node and the `sk-i-curve-zero` unit, including the blueprint ancestor `lem-trf-local-term-locality`; its relevant proof sentence is the finite-module spread used in the Tag 0AFZ argument. I read the Stacks source `literature/stacks-project/algebra.tex` at Tag 05N5 (lines 31490–31508), including the short exact sequence and inverse-image construction in clause (1), and checked the specialization `I=0`, `S={1,f,f^2,…}`. I also read the existing definition nodes `def-weil-finitely-generated-module`, `def-weil-ring-localization-away`, and `def-weil-pbc-module-localization`; their statements provide exactly the notions used in the item and the fraction formulas used in the proof.

Step 1 uses those three definitions to choose a finite generating set, form the surjection `q:R_f^n→L`, and define `K` as the inverse image of its kernel under the localization map. Step 2 uses the finite-generation definition to verify that `M=R^n/K` is finitely generated and uses the localization definitions to form the induced map `M→L`. Step 3 uses the explicit localization fraction formula and the fact that powers of `f` act invertibly after localization: every element of `L` has a representative `q(x/f^r)` (surjectivity), while a zero image forces `q(x/1)=0`, hence `x∈K` (injectivity). Thus the induced map `M_f→L` is an `R_f`-module isomorphism. Each citation quote in `citations.json` is a verbatim substring of the cited node statement. I tested the construction on `f=0`, on a unit `f`, on `L=0`, and on a finite free localized module; the same kernel and fraction arguments cover all cases. I also ran and inspected the required LeanFinder, Loogle, grep, and LeanSearch queries; Mathlib has only forward localization-finiteness results, so no Mathlib leaf applies.
