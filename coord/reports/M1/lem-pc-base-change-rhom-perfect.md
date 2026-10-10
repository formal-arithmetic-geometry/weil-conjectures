Files written:

- `dag/nodes/sec-picard-framework/lem-pc-base-change-rhom-perfect.json` — statement split, no new nodes, Mathlib searches found no exact match.
- `citations.json` — verbatim statement excerpts for every cited node in the proof steps.

Attachments: none.

WANTED: none.

The item was not already stated by a sorry-free declaration in the project Lean sources, and `blueprint_refs.py search` found no duplicate blueprint node. The imported statement is interpreted on the affine scheme `Spec(A)` when applying the scheme-level perfect-complex definition. The proof was expanded from the Tag 0AA8 clause into three steps: bounded finite-projective model and K-projective RHom computation; the finite-projective tensor-Hom scalar-extension calculation; and identification with the derived base-change map. No new node was introduced because the middle calculation is an elementary finite-summand argument and a separate node would restate the item.

## Review by M1

I read the item node, the `sk-thm-picard-duality` unit, and the existing definitions and lemmas cited by the split. `def-pc-perfect-complex` explicitly gives a bounded finite-projective affine model, which is exactly the hypothesis used in Step 1. `lem-sc-bounded-above-projective-kprojective` states the K-projectivity needed to compute Hom against a K-injective representative; `def-pc-derived-rhom-algebra-module` supplies the derived internal-Hom construction. Step 2 is elementary: finite projective modules are direct summands of finite free modules, and the finite free tensor-Hom isomorphism is degreewise and differential-compatible. Step 3 uses `def-pc-derived-pullback` for the derived scalar-extension objects and reuses K-projectivity over `A'`. I checked the zero complex and finite-free rank-zero cases, and the argument remains valid. The required LeanFinder, Loogle, grep, and LeanSearch searches were run; LeanSearch was unavailable and recorded as such, while the other searches found no exact RHom base-change declaration.

## Second reading by M1

- Item statement: checked against Stacks Tag 0AA7, label `perfect-lemma-affine-morphism-and-hom-out-of-perfect`, clause (1), after affine specialization; hypotheses and conclusion agree.
- Step 1: checked `def-pc-perfect-complex`, `def-pc-derived-pullback`, `lem-sc-bounded-above-projective-kprojective`, and `def-pc-derived-rhom-algebra-module`; repaired the representative choice to K-flat so derived tensor is computed correctly.
- Step 2: checked the finite-projective direct-summand calculation and differential compatibility; elementary and valid for zero and rank-zero summands.
- Step 3: checked `def-pc-derived-pullback` and K-projectivity after scalar extension; explicitly supplied that scalar extension preserves finite projectivity.
- New nodes: none; B1-B7 do not apply. Existing-node search covered the cited definitions and K-projectivity leaf.
- Small cases: zero complex, zero ring map target, field extension, and finite-free rank 0 or 1 all reduce to the displayed chain isomorphism.

Changes: corrected the source from the incorrect `more-algebra.tex` description to Tag 0AA7 in `perfect.tex`; fixed `created.item` metadata; replaced the invalid K-injective tensor representative by a K-flat representative and added its citation; expanded the scalar-extension projectivity justification.
