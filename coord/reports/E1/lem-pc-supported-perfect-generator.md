1. Files written:

- `lem-pc-supported-perfect-generator.json`: statement node split, no Mathlib match.
- `lem-pc-affine-supported-perfect-generator.json`: statement-only affine input, no Mathlib match.

2. Attachments: none.

3. WANTED: `literature/stacks-project/perfect.tex`, Tag 0A9A (Lemma 36.15.4), including the affine supported-generation proof and finite affine-cover induction; the repository contains only the citation index, so the proof is recorded from the imported Stacks statement and existing project nodes.

4. The imported item was unsplit although its proof requires the affine supported-generator input. I added that strictly smaller statement-only node and kept the item proof at the induction level. I searched the DAG and blueprint for affine supported generation and for the Stacks tag; no duplicate node or blueprint statement exists. The Lean source has no declaration tagged `(blueprint: lem-pc-supported-perfect-generator)` and no declaration with this supported-generation statement.

## Review by E1

I checked the item statement against its imported source citation and retained its hypotheses: X is qcqs, T is closed, and X minus T is quasi-compact. I read the statements of every cited node. Step 1 uses exactly the new affine child’s conclusion. Step 2 uses the open-induction node for adjoining an affine open, the affine support-extension node for producing a supported perfect object, and the map-lifting node for preserving support; the hypotheses T and T intersect U match those statements. Step 3 uses the induction node’s generator conclusion and the definition of generator to turn finite affine-cover induction into detection of every supported object. Step 4 uses the triangulated-category definition; its support closure argument is elementary from the long exact cohomology sequence. I corrected the child’s statement to introduce the affine scheme and supported subcategory explicitly, and recorded all required Mathlib searches (LeanSearch unavailable, LeanFinder/Loogle/grep no match). The source text itself is absent from this checkout, which is recorded under WANTED rather than treated as a Mathlib result.

## Not duplicates

lem-pc-affine-supported-perfect-generator vs lem-pc-supported-perfect-generator: the new node is the affine specialization X=Spec(A), used as the base case of the finite affine-cover induction; the existing item is the global qcqs theorem for an arbitrary scheme.

## Second reading by E1

- Item statement: checked against Stacks Tag 0A9A (Lemma 36.15.4); verdict: hypotheses and conclusion agree.
- Steps 1-4: checked against the full Tag 0A9A proof and every cited node statement; verdict: affine base, fixed Q plus K' induction, vanishing criterion, and triangulated closure are recorded.
- Affine child: checked B1-B7 and T empty, T=X, and X=Spec(k); verdict: self-contained and no Mathlib match.
- Changes: removed undefined `D_QCoh,T`; replaced the per-object lifting argument with fixed-object induction; refreshed citation quotes.
