## What changed

Completed `AlgebraicGeometry.Etale.exists_compactSupport_openClosed_triangle` without changing its signature or public imports. The proof evaluates the stated bounded-below open-closed recollement triangle, applies the triangulated compact-support functor and the ambient inclusion, identifies the outer vertices using the stated qcqs composition theorem and the elementary immersion compactifications, and applies Mathlib's three homology exactness lemmas. The identity extension is identified by uniqueness of left adjoints; finite direct image exactness and the source library's exact-functor comparison identify the closed term. Added proof-only imports of `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact` and `WeilConjectures.SixFunctors.Finite.Exact`.

Updated the existing node's proof, proof dependencies and proof origin to match the proof, and removed the three obsolete module-sheaf tool approvals. No definitions, existing statements, public interfaces or other modules changed. No change record is required.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.Etale.exists_compactSupport_openClosed_triangle` (node `lem-weil-pbc-etale-compact-support-open-closed-triangle`). The item now contains zero `sorry`. Added zero holes and zero split-offs. The proof uses the already stated, still unproved recollement and qcqs composition declarations as intended for stage 3; this does not claim their transitive axioms are closed.

## No longer needed

Removed these original proof-only imports:

- `Mathlib.AlgebraicGeometry.ZariskisMainTheorem`: immersion/proper instances already available through the required source imports.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: no finite-presentation argument is used.
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`: it states a different module-sheaf encoding; the source supplies enough injectives for the actual coefficient category.
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`: its constant-ring `SheafOfModules` interface is unnecessary for `Sheaf ... (ModuleCat Λ)`.
- `Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`: likewise unnecessary for the actual coefficient category, whose abelian/Grothendieck instances are already available.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`: its required triangulated instance is already imported by the compact-support definition.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`: its declarations are already publicly imported by the compact-support definition.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: already publicly imported by the unchanged public compatibility module.

Removed direct proof dependencies `lem-weil-pbc-quasi-separated-affine-cover-criterion`, `lem-weil-pbc-closed-in-quasi-compact`, and `lem-weil-pbc-finite-over-separated-finite-type`: the established Mathlib permanence lemmas and immersion/composition instances supply the needed source hypotheses without repeating their geometric proofs. Removed direct proof dependencies and their tool approvals `lem-weil-pbc-module-sheaves-enough-injectives`, `lem-weil-pbc-module-direct-image-left-exact`, and `lem-weil-pbc-module-sheaves-grothendieck-abelian`: use the source's existing instances for the actual encoding. The definition-only nodes `def-weil-closed-immersion`, `def-weil-pbc-scheme-conventions`, and `def-weil-triangulated-category` need no separate proof-step citations; their meanings remain unchanged. All statement dependencies are retained.

No unit statement or realized unit step is bypassed. The recollement and qcqs compact-support composition modules remain used. Import removal is a local pruning claim; it does not assert that another target has no need for these modules.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan works. Its geometric verification can use the source's existing quasi-separatedness and compactness permanence lemmas directly. Three original proof imports concern constant-ring `SheafOfModules` rather than the theorem's `Sheaf ... (ModuleCat Λ)` encoding; they cannot supply this proof's instances and are unnecessary because the source library already supplies those instances. Exactness of finite direct image and the exact-functor bounded-below comparison already exist in the source, so no new bridge theorem is needed. Since the statement requires only vertex isomorphisms, transporting the triangle's arrows is unnecessary: retain the mapped triangle and exhibit its vertex isomorphisms.

Edge cases: neither immersion argument requires nonempty source, the coefficient ring can be zero, and no finitely generated closed ideal is used. Each compactification remains independently specified; the two composition isomorphisms provide the required comparisons.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
