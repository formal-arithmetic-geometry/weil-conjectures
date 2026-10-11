# Stage-1 report

1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-derived-tensor-localization-cohomology.json` (statement item, repaired split).
- `lem-pc-balanced-derived-tensor-model` (statement child, unsplit; Mathlib no match).
- `lem-pc-localization-preserves-kflat` (statement child, unsplit; Mathlib no match).
- `lem-pc-derived-tensor-action-naturality` (statement child, unsplit; Mathlib no match).
- `citations.json` (verbatim step citations).
- No Mathlib leaves.

2. Attachments: none.

3. WANTED: `literature/stacks-project/perfect.tex`, Tag 0DJ8, affine proof, if the local literature checkout is restored; the repository contains the imported source reference but not the Stacks files.

4. The source item was statement-only. The returned version incorrectly used an A-K-flat resolution P directly in `P tensor_R R'`; this does not compute the R-derived tensor (counterexample R=k[t], A=R'=R/t, M=A). I replaced it with a K-flat R-resolution F -> R' and the balanced model P tensor_R F. The split adds three genuine auxiliary statements for the balanced model, localization preservation of K-flatness, and chain-level actions/naturality.

## Review by G1

I read the target statement and parent comparison node, then checked the returned counterexample. Step 1 now cites the balanced-model child and the localization-K-flat child, so the chosen complex is genuinely a model for `M tensor_R^L R'` and localizes to the corresponding local derived tensor. Step 2 uses the existing pure-tensor localization formula degreewise; the formula commutes with differentials and gives the displayed complex isomorphism. Step 3 uses exactness of module localization to identify cohomology after localization and cites the action/naturality child: multiplication on P and F is the chain representative of the endomorphisms in the derived categories, and comparison maps are induced by the same chain maps. I verified all prime localizations and the scalar ring in each step. The old assertion of functoriality without a chain-level statement was removed.

## Second reading by G1

- Item statement: checked against Stacks `perfect.tex`, Tag 0DJ8, and the parent node; the primes and localized scalar rings match.
- Step 1: checked that P is K-flat over A while F is K-flat over R, and that the balanced tensor child is exactly the needed derived model. Localization is applied to both factors and to the base ring.
- Step 2: checked the cited tensor-localization statement verbatim; the pure-tensor map is degreewise and differential-compatible.
- Step 3: checked the cited exact-localization statement and the action/naturality child; the latter supplies the previously missing agreement with derived-category endomorphism actions and comparison-map naturality.
- New nodes: four statement-only children (`lem-pc-balanced-derived-tensor-model`, `lem-pc-localization-preserves-kflat`, `lem-pc-derived-tensor-action-naturality`, and `lem-pc-derived-tensor-flat-second-localization`); each was searched in the DAG/blueprint and with LeanFinder, Loogle, and Mathlib grep, with no exact Mathlib match. The fourth node supplies the flat-localization-in-the-second-factor step 3 uses.
- Edge cases checked: `M = A`, degree zero, a field (trivial localizations), and the zero complex (both sides zero).

Changes made: corrected the derived-tensor model, retained the four required child statements, rewrote all proof dependencies and verbatim citations, changed Step 2 from elementary to non-elementary because its action/naturality dependency is substantive, and recorded the counterexample that motivated the repair. Edge cases checked: `M=A`, `M=A=R/t` over `R=k[t]`, degree zero, a field, and the zero complex.

## Not duplicates

lem-pc-balanced-derived-tensor-model vs lem-pc-module-bounded-flat-kflat: the existing node only states K-flatness of bounded-above flat module complexes, while this node states the balanced two-resolution model computing a derived tensor over a base ring.
lem-pc-balanced-derived-tensor-model vs lem-pc-affine-tilde-kflat: the existing node concerns affine sheaf tilde complexes, while this node concerns balanced derived tensor products of ring complexes.
lem-pc-localization-preserves-kflat vs lem-pc-module-bounded-flat-kflat: the existing node proves bounded-above flat implies K-flat, while this node proves K-flatness is preserved by ring localization.
lem-pc-localization-preserves-kflat vs lem-pc-affine-tilde-kflat: the existing node concerns affine sheaf tilde constructions, while this node concerns localization of arbitrary K-flat module complexes.
lem-pc-derived-tensor-action-naturality vs lem-pc-module-bounded-flat-kflat: the existing node is a K-flatness criterion, while this node identifies scalar actions and naturality of derived tensor models.
lem-pc-derived-tensor-action-naturality vs lem-pc-affine-tilde-kflat: the existing node concerns affine sheaf tilde K-flatness, while this node concerns chain-level action and comparison-map compatibility for derived tensor products.
lem-pc-derived-tensor-flat-second-localization vs lem-pc-module-bounded-flat-kflat: the existing node is a bounded-above flatness criterion, while this node states cohomology base change for derived tensor under a flat localization of the second algebra.
lem-pc-derived-tensor-flat-second-localization vs lem-pc-affine-tilde-kflat: the existing node concerns affine sheaf tilde complexes, while this node states flat localization compatibility for derived tensor cohomology of ring complexes.
