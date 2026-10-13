## What changed

Proved `AlgebraicGeometry.Scheme.Modules.scalarExtCup_inverseImage_second` with its signature
unchanged. Two proved private helpers establish naturality under a natural transformation by
induction on Ext degree, and comparison of composite exact functors. Added proof imports of
`Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison`, `Mathlib.Algebra.Category.ModuleCat.AB`,
`Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`, and
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`.
Updated the existing node's proof route and proof dependencies to match.

The composition comparison is a proved tool from another unit: it compares the exact functors,
and does not replace any step of the cube unit. Its `realized` list is empty for this item.

## Proved and sorry left

Closed the one hole in `AlgebraicGeometry.Scheme.Modules.scalarExtCup_inverseImage_second`
(node `lem-sc-scalar-ext-cup-inverse-image-second`). Added zero holes. No sorry remains in the
item or in the private helpers `exactFunctor_naturality` and `mapExactFunctor_composite`.

## No longer needed

None: no original import or proof-dependency node was removed. No new statement modules.

## Where the brief, the DAG or earlier work was wrong

The original plan describes naturality using localization of shifted morphisms, but does not
name a declaration proving it. The proof supplies that step directly through dimension shifting
and the already proved Mathlib naturality of short exact sequence Ext classes.
The pinned Mathlib has no general `mapExactFunctor` natural-transformation naturality lemma
(searches: LeanFinder, Loogle and grep). Its preservation of composition and short exact
sequence classes supplies the induction. No statement or definition was changed.

## Second reading by E2

1. PASS: compared the only delivered Lean module with the repository using `diff`.
   The existing theorem signature and docstring are byte-for-byte unchanged; only private
   proved helpers, proof imports, a declaration-scoped heartbeat option and its proof were added.
   No definitions, existing hypotheses, conclusions or other modules were changed.
2. PASS: the module compiles locally without warnings (43.3 seconds). A scratch copy with
   `#print axioms AlgebraicGeometry.Scheme.Modules.scalarExtCup_inverseImage_second` reports
   exactly `propext`, `Classical.choice`, `Quot.sound`. There are no remaining or added holes,
   hollow definitions, or forbidden declarations. Read the induction: dimension shifting uses
   an actual Mathlib injective embedding and its cokernel, and exact functors carry its short
   exact sequence class naturally. No arbitrary data is chosen from an unproved existence.
3. PASS: no statements were split off and no new public statements were added. Both private
   helpers are fully proved. Degree zero is ordinary morphism naturality; positive degree
   reduces to the preceding degree without assuming the images of injectives are injective.
   Tensor bifunctoriality and unit cancellation also cover zero sheaves and empty schemes.
   Independent grep and Loogle searches found no shorter route available in the pinned library.
   Loogle returned newer `Ext.comp_mapExactFunctor` and
   `Ext.mapExactFunctor_comp_mk₀_natTransApp`, but scratch `#print` commands confirmed both
   constants are absent from the pinned Mathlib. The existing composition comparison is used.
4. PASS: the proof follows the second-factor naturality argument and reuses the proved
   composition comparison. All proof-only imports are plain `import`; the original public
   import supplies the signature. The three Grothendieck-category imports supply enough
   injectives for scalar sheaves. No old proof dependency or import is discarded, so
   `## No longer needed` is complete. Checked `dag/units/sk-prop-av-cube.json`: its realized
   statement and step lists are empty; no unit statement or step is bypassed or changed.
5. PASS: compared the node JSON with the repository. Only `proof`, `proof_deps`, and
   `proof_origin` differ. The three recorded steps match the induction, composite comparison,
   tensor factorization and unit cancellation in Lean; their uses have exactly the recorded
   proof-dependency union. No new node or change record is required.

Changed only this report to record the independent reading and pinned-version search findings.
The Lean proof and node were retained as written.
