1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-finite-sheafhom-affine.json` — statement, one elementary proof step, no new nodes, Mathlib searches recorded.
- `citations.json` — empty because the sole proof step cites no node.

2. Attachments: none.

3. WANTED: `literature/stacks-project/duality.tex`, Tag 0AX2 source text was not present in this checkout; the item and proof follow the imported Stacks citation and the ancestor blueprint.

4. No new node was created. Searches of the DAG and blueprint found no duplicate statement or narrower dependency. The item statement was retained. The slopmaster2 source was searched by item id and by affine/internal-Hom keywords; no declaration states this item.

5. Nothing remains unfinished.

## Review by K1

I read the item node, its ancestor `lem-sc-finite-duality`, and the related derived-Hom node. The ancestor's first proof paragraph supplies exactly the affine restriction-of-scalars calculation used here. The item hypotheses introduce an affine morphism `f:Y→X`, its algebra `A=f_*O_Y`, and an arbitrary `O_X`-module `F`; the affine-local calculation specializes to `U=Spec(R)`, `f^{-1}(U)=Spec(S)`, an `S`-module `M`, and `N=F(U)`. The sole step writes both directions of the bijection explicitly, checks that they are inverse and natural, and states the localization compatibility needed to glue the sheaf adjunction. Evaluation at `1∈S` is exactly the counit claimed in the statement. Since this is a two- or three-line calculation from the definitions and the affine-local section description, I marked it elementary and cited no node; `citations.json` is therefore empty. I also checked the statement's `def-pc-scheme` and `def-pur-sheaf-hom` dependencies exist in the DAG. The Mathlib searches returned only generic module or pushforward adjunctions, not this sheaf-Hom formula; LeanSearch was unavailable and recorded as such.

## Second reading by K1

- Item statement: checked against Stacks `duality.tex`, Tag 0AX2, `lemma-compute-sheafhom-affine` (lines 2488–2517); the affine hypothesis, restriction adjunction, and affine section formula agree. The counit evaluation at `1` is the explicit module adjunction counit and is compatible with the stated formula.
- Step 1: checked against the same Tag 0AX2 proof and against `def-pur-sheaf-hom`; the displayed maps are mutually inverse, natural, and localization-compatible, and the cited definition supplies the sheaf-Hom restriction/gluing structure. The step remains elementary.
- New nodes: none; the delivery contains only the repaired split item statement.
- Edge cases checked: the zero module gives the zero Hom bijection, a field extension gives the usual vector-space restriction adjunction, the empty scheme gives vacuous affine sections, and the unit evaluation is defined for every ring (including the zero ring).
- Changes: added `def-pur-sheaf-hom` to the step's uses and added its verbatim statement quote to `citations.json`; this makes the gluing fact explicit under C1 while preserving the elementary affine calculation. Corrected the prior review sentence that said the step cited no node.
