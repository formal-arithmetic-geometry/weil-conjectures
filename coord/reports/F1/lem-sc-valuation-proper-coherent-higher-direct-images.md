# Stage-1 report

1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-valuation-proper-coherent-higher-direct-images.json` — item split into two proof steps.
- `dag/nodes/sec-abelian-varieties/lem-sc-coherent-ring-perfect-complex-cohomology.json` — one new unsplit statement node; Mathlib searches found no match.
- `citations.json` — verbatim statement quotes for every cited node in both steps.

2. Attachments: none. The source declaration `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage` in `WeilConjectures/AlgebraicGeometry/Cohomology/DirectImage.lean:651` has a `sorry`, so it is not an attachment.

3. WANTED: none.

4. The imported item had no proof. I checked the parent blueprint clause and the Stacks route: Tag 0B91 supplies perfectness of the derived direct image for a proper finitely presented morphism and a finitely presented flat sheaf; the valuation-ring argument then uses coherence and the affine finite-projective model of a perfect complex. The new child records only the strictly smaller coherent-ring complex lemma, rather than restating the item. Existing DAG searches found no duplicate child. The item's existing Mathlib searches were rerun; the new child was searched with LeanFinder, Loogle, grep, and LeanSearch (the latter unavailable).

## Review by F1

I read the target's Stacks source, More on Morphisms Tag 0EX8, and the source-side Lean declaration and docstring. I also read the statements of every cited existing node: the locally-free definition gives quasi-coherence and finite presentation on affine opens; `lem-pc-rf-perfect-base-change` gives perfectness under proper finite-presentation and flat finite-presentation hypotheses; `def-pc-perfect-complex` gives the bounded finite-projective affine model; and `def-pc-derived-direct-image` identifies the cohomology sheaves with higher direct images. Step 1 checks the finite-rank locally-free module supplies exactly the module hypotheses required by the perfect direct-image theorem. Step 2 checks that a valuation ring is coherent, applies the new child's stated finite-presentation result to the affine perfect model, and then uses the derived-direct-image definition to identify the resulting module with `H^q(X,F)`. I tested the child statement on the zero complex and a one-term finite free complex (cohomology is respectively zero or finite free), and checked the item at `q=0`, where it specializes to the existing coherent-global-sections item. The only correction to the imported material was adding this genuine algebraic child and replacing the empty proof with the two cited route steps; no statement or hypothesis was weakened.

## Second reading by F1

- Item statement: checked against More on Morphisms, Lemma 0EX8, Tag 0EX8 and the existing degree-zero sibling; hypotheses proper, flat, finite presentation, valuation ring, and finite locally free coefficient are preserved.
- Step 1: checked against `def-amb-finite-locally-free-module` and `lem-pc-rf-perfect-base-change`; the local finite-free argument now explicitly supplies finite presentation and flatness over the base before applying perfectness.
- Step 2: checked against `def-pc-perfect-complex`, `def-pc-derived-direct-image`, and the coherent-ring child; the affine module/sheaf cohomology identification is now stated explicitly.
- New node `lem-sc-coherent-ring-perfect-complex-cohomology`: checked against More on Algebra, Tag 0ASU and the bounded finite-projective coherent-ring argument; self-contained, statement-only, TeX-correct, and no Mathlib match after the recorded searches.
- Small cases checked: zero complex, one-term finite free complex, field valuation ring, and `q=0`; all give the expected finitely presented modules.

Changes: expanded Steps 1 and 2 to close the finite-presentation, flatness, and affine-cohomology dependency gaps; no statements or hypotheses were weakened, and the new child remains a strictly smaller algebraic input.
