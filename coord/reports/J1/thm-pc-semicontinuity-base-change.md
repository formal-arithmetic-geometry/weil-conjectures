Files written:

- `dag/nodes/sec-picard-framework/thm-pc-semicontinuity-base-change.json`: statement node, split.
- `dag/nodes/sec-picard-framework/lem-pc-finite-free-complex-higher-direct-image.json`: statement-only sorried Lean declaration; Mathlib no match.
- `dag/nodes/sec-picard-framework/lem-pc-sections-higher-direct-image-equivalence.json`: statement-only sorried Lean declaration; Mathlib no match.
- `dag/units/sk-thm-picard-semicon.json`: realized statement and proof route.
- `citations.json`: verbatim citations for step 1.

Attachments:

- `AlgebraicGeometry.Scheme.Modules.upperSemicontinuous_hFiber` is not an attachment because its dependency graph contains sorry declarations.

## Not duplicates

- `lem-pc-finite-free-complex-higher-direct-image` vs `lem-pc-proper-support-perfect-direct-image`: the existing node treats a perfect tensor product with proper support and gives perfectness/base change; the new node gives an explicit bounded finite-free complex for a flat finite-presentation sheaf and identifies every pulled-back cohomology with the corresponding higher direct image.
- `lem-pc-finite-free-complex-higher-direct-image` vs `lem-pc-rf-perfect-base-change`: the existing node states that the derived direct image is perfect and commutes with base change, while the new node records the stronger local finite-free complex realization and its degreewise cohomology identifications used by the Lean declaration.
- The removed candidate `lem-pc-sections-higher-direct-image-equivalence` was a duplicate of `lem-pc-cohomology-sections-affine-base`; the item now cites that existing node directly.

WANTED:

- None. The source declaration and its Stacks references are available in the repository.

What was wrong in the imported material:

The imported theorem had a long proof but only three dependencies. The Lean source shows two additional declarations used by the implementation, both still sorried; I added statement-only nodes for them and cited them in the local-model step. The source theorem itself proves only upper semicontinuity, while the DAG item includes the canonical base-change map, the reduced-base locally-free conclusion, and the nonreduced counterexample; those clauses remain in the item statement and are represented by explicit proof steps rather than being silently weakened.

## Review by J1

I read the unit blueprint `_section.md`, the item proof in `thm-pc-semicontinuity-base-change.md`, the existing nodes `lem-pc-rf-perfect-base-change`, `def-pc-perfect-complex`, and `lem-pc-flat-complex-derived-pullback`, and the Lean declarations at `DirectImage.lean:307-324`, `574-615`, and `725-775`. Step 1 uses exactly the existing perfectness/base-change statement, the perfect-complex local description, and the termwise flat derived-pullback statement, plus the two new statements: the finite-free complex computes every base-changed higher direct image, and affine global sections of a higher direct image are additively equivalent to sheaf cohomology. The other steps are the elementary cycle/boundary map, rank/minor linear algebra and semicontinuity argument, the reduced-ring matrix normal form and split exactness argument, and the square-zero elliptic-curve counterexample; they use no uncited DAG theorem. I checked that all cited quotations in `citations.json` are verbatim portions of the cited statements, that both new statements introduce their schemes, morphisms, modules, and hypotheses, and that Mathlib searches were run for each new node with LeanFinder, Loogle, and Mathlib grep. I also checked the small nonreduced test ring $k[\\varepsilon]/(\\varepsilon^2)$ and the rank-zero/rank-full matrix cases underlying the normal-form step.

What could not be finished:

The implementation theorem remains transitively sorried because the finite-free-complex and affine sections declarations are sorried in slopmaster2; this is recorded in `lean_audit.slopmaster2` rather than treated as a closed attachment.

## Second reading by J1

- Item statement: checked against the blueprint theorem and the stated proper finite-presentation, finite-presentation/flatness, reduced-base, and locally-constant-fibre hypotheses; verdict: agrees, including the nonreduced warning.
- Step 1: checked against `lem-pc-rf-perfect-base-change`, `def-pc-perfect-complex`, `lem-pc-flat-complex-derived-pullback`, and the finite-free-complex helper statements; verdict: the restriction identity is now taken explicitly from the helper's identity case, with no uncited restriction theorem.
- Step 2: checked directly on cycles and boundaries in the tensor complex; verdict: elementary and correct.
- Step 3: checked by the rank formula and determinantal rank loci; verdict: elementary and correct, including rank-zero and full-rank cases.
- Step 4 and the reduced-base claim: checked on reduced affine rings and the reduced-ring matrix normal form; verdict: the minor argument, split kernel/image, and tensor exactness are correct.
- Step 5: checked on $k[\\varepsilon]/(\\varepsilon^2)$ with a nontrivial first-order elliptic-curve line-bundle deformation; verdict: the nonflat $H^0$ counterexample is correct.
- `lem-pc-finite-free-complex-higher-direct-image`: checked against the Lean declaration at `DirectImage.lean:574-615` and Stacks Tags 0B91/0A1H; verdict: supporting local-complex statement, not a restatement of the full item; removed the vague extra injective-resolution hypothesis while retaining the usual construction of higher direct images.

Changes made:

- Replaced the uncited assertion that higher direct images commute with restriction by the cited helper's explicit identity case.
- Reworded the finite-free-complex node's injective-resolution clause so it states the standard construction rather than an undefined additional hypothesis.
