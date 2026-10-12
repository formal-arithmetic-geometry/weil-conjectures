## What changed
Reduced the original theorem to three canonical-adjunction components. The main proof supplies the right-adjoint instance from the given adjunction, uses `Adjunction.leftAdjointUniq` to transport finite-limit preservation, and applies Mathlib's compatibility equations to transport the unit and counit isomorphisms. Three new proof imports were added. Existing signatures and public imports are unchanged.

## Proved and sorry left
Closed the direct hole in `AlgebraicGeometry.affine_algebra_module_adjunction_isos`. This is a decomposition, not a proof free of sorry: one hole closed and three added, net -2. The added holes are:

- `AlgebraicGeometry.affine_algebra_module_adjunction_preserves_finite_limits`, node `new-affine-algebra-module-finite-limits`.
- `AlgebraicGeometry.affine_algebra_module_adjunction_unit_iso`, node `new-affine-algebra-module-unit-iso`.
- `AlgebraicGeometry.affine_algebra_module_adjunction_counit_iso`, node `new-affine-algebra-module-counit-iso`.

Each is the whole proof of a public named theorem in its own module. None has the full original conclusion. The canonical adjunction is constructed from the supplied right-adjoint instance; no object is chosen from a new unproved existence theorem.

## No longer needed
No original imports or modules are pruned. The parent no longer uses `lem-weil-pbc-affine-module-correspondence` directly: the unit and counit component nodes retain that dependency. The corresponding module remains exposed through the existing statement imports.

## Where the brief, the DAG or earlier work was wrong
The original plan's flatness-to-exactness argument and identification of alpha and beta with the canonical adjunction have no existing Lean interfaces. Those three mathematical components remain for subsequent workers, while the general adjunction-uniqueness transport is now proved. No statement is disputed. The components hold for empty schemes, zero rings, zero modules, and identity morphisms. The unit's route is retained.

Stacks [0AVW](https://stacks.math.columbia.edu/tag/0AVW) and [01SB](https://stacks.math.columbia.edu/tag/01SB) were read online because the local TeX files are absent. Searches via LeanFinder and Loogle plus pinned-source grep found generic adjunction transport lemmas and the affine-module correspondence, but no theorem providing these canonical components. A first dry run failed because the initial new-node records lacked proof steps and exact signatures; those records were repaired.

## New nodes
`new-affine-algebra-module-finite-limits` states only preservation of finite limits by the canonical left adjoint. Its docstring explains the localization stalk maps, flat tensor pullback, and passage from kernels and finite products to finite limits.

`new-affine-algebra-module-unit-iso` states only the canonical unit's isomorphism on quasi-coherent algebra modules. Its docstring identifies this unit with beta of the affine-module correspondence using tensor associativity and the tensor unit.

`new-affine-algebra-module-counit-iso` states only the canonical counit's isomorphism on quasi-coherent structure-sheaf modules. Its docstring identifies the counit with alpha using the tensor universal property and transports it through the unique left-adjoint comparison.

## Second reading by R2

1. Compared every delivered module against the repository version. The existing theorem signature is byte-for-byte unchanged; only its proof and proof-only imports changed. The three added modules and node records are new declarations, with no accidental edits elsewhere. Verdict: pass.

2. Compiled all four modules with `lcompile.py --all`; compilation succeeds. The parent theorem has no `sorry`; the three split component theorems contain the explicitly reported `sorry`s, and no definition contains `sorry`. The split statements are public named theorems with source docstrings and matching nodes. Verdict: pass.

3. Checked the split statements against the canonical adjunction types and searched the repository and Mathlib indexes for existing declarations. They are strictly smaller component claims, with no added hypotheses beyond the canonical right-adjoint instance and quasi-coherence premises. Verdict: pass.

4. The parent proof uses the canonical right-adjoint construction, `leftAdjointUniq`, and the generic finite-limit and unit/counit transport equations. The three unresolved component results are isolated in separate modules; no imports were removed because the parent still requires all three. The unit route and unit record remain retained. Verdict: pass.

5. The parent and new node `proof`, `proof_deps`, and `proof_origin` records agree with the Lean proof and declarations. The three new nodes carry complete source, proof-step, search, creation, chapter, unit, and Lean records. Verdict: pass.

Changed nothing during second reading; the delivered proof and decomposition are internally consistent.
