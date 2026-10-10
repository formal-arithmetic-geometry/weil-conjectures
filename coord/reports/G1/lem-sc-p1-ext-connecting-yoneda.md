Files written:

- `dag/nodes/sec-picard-framework/lem-sc-p1-ext-connecting-yoneda.json` (statement, split; no Mathlib match for the scheme-module resolution formulation).
- `dag/nodes/sec-picard-framework/lem-sc-p1-derived-connecting-extclass.json` (statement, Mathlib leaf; exact derived-category declaration `CategoryTheory.Abelian.Ext.preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply`).
- `citations.json` (five verbatim statement quotes, covering every citation in both steps).

Attachments: none.

WANTED: `literature/stacks-project/derived.tex`, Tags 06XP, 06XR and 05TE, for `lem-sc-p1-ext-connecting-yoneda` (the checkout contains citation metadata but not the source TeX).

The original item was statement-only. Its proof now has two steps: identify the injective-resolution connecting morphism with the derived-triangle connecting morphism, then apply the generic derived identity and identify the composite with Yoneda composition. No statement was weakened. The new leaf is strictly more general than the item and is not a restatement of its scheme-module resolution claim.

Nothing remains unfinished in the split.

## Review by G1

I read the item source pointer (Stacks Cohomology Lemma 0B3A as imported in the node) and the derived-category route at Tags 06XP, 06XR and 05TE. I opened `def-sc-ext-sheaf` and verified that it defines Ext by injective resolutions in the second variable and explicitly supplies the covariant long exact sequence; this supplies the exact connecting map used in Step 1. I opened `lem-weil-pbc-right-derived-universal-delta-functor` and used its statement that right derived functors carry canonical connecting morphisms, and opened `lem-sc-ext-yoneda-composition-derived` to check that derived composition is the stated Yoneda product. For Step 2 I checked the new Mathlib leaf against Mathlib `ExactSequences.lean` lines 49–56: its statement is the derived homology-sequence connecting morphism applied to `x`, equal to `x.comp hS.extClass`. I also checked `lem-sc-p1-ext-yoneda-functoriality` for the degree-zero interpretation of `s` and the Yoneda composition convention.

The two hypotheses needed by the leaf (abelian category and derived category) hold for `Mod(O_X)` by the definitions cited by `def-sc-ext-sheaf`; the short exact sequence and the degree-zero choice `n=0` are explicit in the item. I tested the formula on the split sequence (both sides are zero) and on `s = 0` (both sides are zero), and checked the identity case `s = id` reduces to the extension class. I searched the whole DAG and blueprint for the generic identity and found no existing node; the required LeanFinder, Loogle, grep and LeanSearch records are present, with the unavailable services recorded as such. Every citation quote in `citations.json` was checked verbatim against its node statement. No source statement or hypothesis was changed.

## Second reading by G1

- Item statement: checked against Cohomology Tag 0B3A and derived Ext Tags 06XQ, 06XR, 06XP and 05TE; the arbitrary-first-argument formula is retained as the intended generalization.
- Step 1: `def-sc-ext-sheaf` supplies the resolution long exact sequence, but the original citations did not state compatibility with the derived triangle. Repaired by adding and citing `lem-sc-p1-ext-resolution-derived-connecting`.
- Step 2: checked `lem-sc-p1-derived-connecting-extclass`, `lem-sc-ext-yoneda-composition-derived`, and `lem-sc-p1-ext-yoneda-functoriality`; corrected the intermediate composite wording to `\\delta\\circ s`.
- `lem-sc-p1-ext-resolution-derived-connecting`: checked self-contained hypotheses, definition-node references, TeX escaping, Tags 05TE/06XR, and all three recorded Mathlib searches; it is a non-elementary supporting statement, not a restatement of the item.
- `lem-sc-p1-derived-connecting-extclass`: checked Mathlib `ExactSequences.lean:49-56`; its derived formula is the claimed specialization, including the zero and identity cases.
- Small cases: split sequence and `s=0` give zero on both sides; `s=id` gives the extension class; degree `n=0` is the case used by the item.
- Changes: added the missing comparison node, replaced Step 1 citations and quotes, corrected Step 2 composition order, and updated `citations.json`.

## Source error

Tag 0B3A directly treats the boundary of the unit section (first argument `\\mathcal O_X`), not the arbitrary-first-argument statement written here. The general statement is retained because it is supported by the derived-category route at Tags 06XP, 06XR and 05TE; the source limitation is reported rather than silently weakening the item.

## Not duplicates

`lem-sc-p1-ext-resolution-derived-connecting` vs `lem-weil-pbc-horseshoe-delta-functor` (05TE): the existing node constructs and compares horseshoe-resolution connecting maps, and explicitly makes no claim relating them to distinguished-triangle connecting maps; the new node states that missing relation.
`lem-sc-p1-ext-resolution-derived-connecting` vs `lem-weil-pbc-right-derived-universal-delta-functor` (05TE): the existing node states universality and existence of a derived-functor delta-functor, while the new node compares that triangle delta with the injective-resolution Ext delta.
`lem-sc-p1-ext-resolution-derived-connecting` vs `lem-sc-ext-locally-free-second-naturality` (06XR): the existing node concerns coefficient naturality for locally free sheaf Ext, not connecting maps of short exact sequences.
`lem-sc-p1-ext-resolution-derived-connecting` vs `lem-sc-derived-hom-projective-resolution` (06XR): the existing node concerns projective resolutions computing derived Hom, not the compatibility of two connecting morphisms.
`lem-sc-p1-ext-resolution-derived-connecting` vs `lem-sc-affine-rhom-qcoherent` (06XR): the existing node is an affine sheaf RHom and quasi-coherence statement, not a long-exact-sequence comparison.
`lem-sc-p1-ext-resolution-derived-connecting` vs `lem-weil-pbc-ext-via-injective-resolution` (06XR): the existing node identifies Ext groups with injective-resolution cohomology termwise, while the new node additionally identifies the connecting maps for a short exact sequence.
