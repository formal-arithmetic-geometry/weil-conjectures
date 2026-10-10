Files written:

- `dag/nodes/sec-nagata-compactification/lemma-nagata-affine-fp-descends.json`: statement split into three proof steps; no new nodes.
- `citations.json`: verbatim citations for all step dependencies.

Attachments:

- None. No sorry-free project declaration states this item exactly.

WANTED: `literature/blueprint/master/blueprint/sec-nagata-compactification/sk-prop-nagata-sketch-approximation/lemma-nagata-affine-fp-descends.md`, `## Proof`, for `lemma-nagata-affine-fp-descends` (the referenced source file is not present in this checkout).

The imported proof was one compressed paragraph and did not cite its defining node. I kept the statement unchanged, added the existing definition as the sole proof dependency, and expanded the argument into: finite presentation from the finite quotient; coefficientwise identification after tensoring; and the generatorwise inverse for `beta_B`. No new node was warranted because each step is a direct verification from the definition.

## Not duplicates

None: no new nodes were created.

## Review by E1

I read the item node, `def-nagata-affine-fp-descent`, the unit `sk-prop-nagata-sketch-approximation`, the chapter record, and the corresponding Lean source commentary in `WeilConjectures/Compactification/FinitePresentation.lean`. The item statement uses exactly the algebra and comparison map introduced by the definition node. Step 1 uses the definition's explicit finite quotient and therefore establishes finite presentation directly. Step 2 uses the definition's coefficient compatibility sentence, which states that each lifted relation maps to the original relation; this verifies the tensor quotient is the chosen presentation of `B`. Step 3 uses the definition's declaration of `beta_B` as the generator-preserving map and the preceding identification; the inverse on generators is therefore two-sided. I checked that all hypotheses and choices (`lambda_B`, lifted coefficients, and the finite relation list) are supplied by the cited definition. The Mathlib searches found only general finite-presentation/base-change results, not this constructed statement; LeanSearch was unavailable and recorded as such. I corrected the imported proof by adding its missing dependency, explicit source metadata on each step, and the required blueprint, search, citation, and split-report metadata.

## Second reading by E1

- Item statement: checked against the available `def-nagata-affine-fp-descent` statement and its displayed quotient/comparison-map data; hypotheses and conclusions match. The named blueprint source file is absent from this checkout, so direct source-text comparison was unavailable.
- Step 1: checked against the cited definition's explicit finite quotient by a finite relation list; finite presentation follows elementarily. Verdict: pass.
- Step 2: checked against the cited definition's coefficient-transport equality and displayed tensor quotient; the base change has exactly the relations of the chosen presentation of `B`. Verdict: pass.
- Step 3: checked against the cited definition's generator description of `beta_B` and the preceding quotient identification; the generator-preserving reverse map is two-sided inverse. Verdict: pass.
- New nodes: none; there are no new-node statements to audit, and no duplicate node was introduced.
- Small cases: the quotient argument specializes to `m = 0`, `n = 0`, the zero ring, and a field without changing any step.
- Changes made: appended this second-reading record only. No node or proof repair was needed.
