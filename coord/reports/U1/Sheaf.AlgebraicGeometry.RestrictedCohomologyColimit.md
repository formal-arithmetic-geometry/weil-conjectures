## What changed

Replaced the only sorry in `Sheaf.AlgebraicGeometry.RestrictedCohomologyColimit`,
`AlgebraicGeometry.Etale.restrictedCohomology_isColimit`, by a complete Lean reduction.
Its signature and existing docstring are unchanged. Module inverse image preserves the
supplied colimit by its existing left adjunction. Forgetting coefficients then preserves
it by the new, proved `constantModuleSheaves_forget_preservesColimits`. Mathlib supplies a
final directed reindexing in universe `u + 1`. The directed cohomology comparison, followed
by the existing proved natural Ext/derived comparison, gives a colimit on this index.
Final-functor reflection gives precisely the original image cocone; all legs are canonical.

Added proof-only imports of `Mathlib.CategoryTheory.Presentable.Directed`,
`Sheaf.AlgebraicGeometry.ConstantModuleSheavesForgetColimits`,
`Sheaf.AlgebraicGeometry.EtaleDirectedCohomologyColimit`, and
`Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison`.
The first new module proves coefficient forgetting preserves all colimits of size `u + 1`:
restriction of scalars to integers is a left adjoint, integer modules are equivalent to
abelian groups, and the sheafification natural isomorphism transfers the induced sheaf
left adjunction to `sheafCompose`. The second new module isolates the directed abelian
cohomology step at the universe required by the item. Updated the item's DAG proof to
match this order and these actual dependencies. No existing definition or signature changed.

## Proved and sorry left

- `AlgebraicGeometry.Etale.restrictedCohomology_isColimit`
  (`lem-weil-pbc-restricted-cohomology-colimit`): complete proof from the named directed
  auxiliary theorem. No sorry remains in the item's module.
- `AlgebraicGeometry.Etale.constantModuleSheaves_forget_preservesColimits`
  (`lem-weil-pbc-constant-module-sheaves-forget-colimits`): complete proof from Mathlib
  adjunctions and the existing library's sheafification infrastructure; no direct sorry.
- The delivery's only direct sorry is
  `AlgebraicGeometry.Scheme.etaleCohomology_isColimit_of_isDirected`
  (`lem-weil-pbc-etale-directed-cohomology-colimit`), in its own new module, with proof
  exactly `by sorry`. Its docstring and node contain the full finite-cover, injective
  embedding, Cech acyclicity, and degree-induction argument, sourced to 03Q5 and 0739.

The original theorem is reduced, not yet free of transitive sorry dependencies. Its new
auxiliary cohomology theorem has neither module coefficients nor an inverse-image functor;
coefficient colimit preservation and final reflection are separately proved in Lean.
All three delivered modules compile locally without warnings. Singleton identity diagrams,
zero sheaves, the empty scheme, and the zero ring are compatible with the two new statements.
The directed index is explicitly nonempty, and the cohomology auxiliary assumes exactly
qcqs for its base scheme. No new torsion, constructibility, or size-shrinking assumption.

## No longer needed

No original import was removed: the original public import supplies the item signature.
Every newly added proof import is used.

The following original direct proof dependencies and their modules are unnecessary for
this reduction; this is a local pruning claim, not a claim that other users no longer need them:

- `lem-weil-pbc-module-sheaves-colimits-forgetful` /
  `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`: replaced by the proved
  coefficient-sheaf forgetful colimit theorem, in the actual sheaf model of the item.
- `lem-weil-pbc-inverse-image-preserves-colimits` /
  `Sheaf.AlgebraicGeometry.EtaleInverseImageColimits`: preservation for module inverse image
  follows directly from its existing left adjunction.
- `prop-weil-pbc-inverse-image-modules-exact` /
  `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`: no compatibility comparison
  between module and abelian inverse image is needed, since restriction happens first.
- `lem-weil-pbc-cohomology-filtered-colimit` /
  `Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit`: its theorem fixes the index
  universe to `u`, so this proof instead needs the new directed theorem at `u + 1`.
  Its abelian proof plan is retained in that new node, with the same underlying steps;
  its module-coefficient clause is unnecessary.
- `lem-weil-pbc-filtered-category-directed-cofinal` /
  `Sheaf.CategoryTheory.ExistsDirectedReindexing`: Mathlib's stronger final-functor
  reindexing theorem directly supplies the needed data.
- `lem-weil-pbc-initial-functor-cofiltered-criterion`: its over-category criteria and
  chosen colimit isomorphism are unnecessary. Mathlib's
  `Functor.Final.isColimitWhiskerEquiv` transports and reflects the supplied cocones directly.

Retained `lem-weil-pbc-filtered-category-exists-directed-final` and
`lem-weil-pbc-sheafH-ext-derived-comparison`; added the left-adjoint preservation node
and the two auxiliary nodes. The unit `sk-thm-p1` and every realized statement and step
remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The original forgetful-colimit dependency uses `SheafOfModules R`, whereas the item uses
`Sheaf J (ModuleCat Λ)`. The original inverse-image compatibility dependency also uses
`SheafOfModules`. Applying these signatures directly would require an additional model
comparison. Restricting module sheaves first avoids that compatibility problem, and the
proved coefficient forgetting theorem deals directly with the item's model.

The original cohomology theorem has `{I : Type u}`, while the item and final directed
reindexing have an index in `Type (u + 1)`. The final reindexing does not shrink universes.
The new auxiliary records exactly the abelian directed comparison at coefficient size,
with the same mathematical finite-cover argument. It does not pretend the existing
universe-`u` theorem applies. The source label for Stacks Tag 03Q5 is `lemma-colimit`,
not `lemma-colimit-cohomology` as the original docstring says; the new node and module
use the actual label. The existing docstring is preserved.

LeanSearch returned Internal Server Error and is recorded as unavailable; actual
LeanFinder, Loogle, and Mathlib grep searches were also run. No exact Mathlib cohomology
preservation theorem was found. The left-adjoint route did close the forgetful step.

## New nodes

`lem-weil-pbc-constant-module-sheaves-forget-colimits` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-constant-module-sheaves-forget-colimits.json`
is realized by `Sheaf.AlgebraicGeometry.ConstantModuleSheavesForgetColimits`. It supplies
the proved colimit preservation for the exact coefficient-sheaf model used by the item,
without qcqs or coefficient finiteness assumptions.

`lem-weil-pbc-etale-directed-cohomology-colimit` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-directed-cohomology-colimit.json`
is realized by `Sheaf.AlgebraicGeometry.EtaleDirectedCohomologyColimit`. It supplies only
the directed abelian derived-cohomology comparison at universe `u + 1`, the step missing
from the current universe-`u` signature. The node records the existing blueprint
cohomology lemma under `same_as` and retains its abelian proof steps. Both new nodes
inherit the item's proper-base-change chapter, `sk-thm-p1` unit, and blueprint ancestor.

## Second reading by U1

1. **Visible interface: pass.** Diffed the existing module against the repository.
   Only four plain proof imports and the body of
   `AlgebraicGeometry.Etale.restrictedCohomology_isColimit` changed. Its signature,
   universes, finite-ring assumption, supplied cocone, conclusion, and docstring
   are byte for byte unchanged. The two other modules are new; there is no existing
   definition change and no change record is needed.
2. **Proof and axioms: pass as a reduction.** Independently compiled all three modules
   in import order without warnings. A scratch copy with explicit `#print axioms`
   showed only `propext`, `Classical.choice`, `Quot.sound` for coefficient forgetting;
   the item and directed cohomology theorem also show `sorryAx`, as reported.
   The only direct sorry is the named directed cohomology theorem. No forbidden
   declaration mechanism or hollow definition occurs. The main proof transports
   the supplied cocone, so its legs remain the images of the original coprojections.
3. **Split statements: pass.** Read Stacks 03Q5 (`lemma-colimit`, statement and direct
   proof), 0739 (`lemma-colim-works-over-collection`, full proof), and 03DB
   (`lemma-limits-colimits`, statement and proof) in the sandbox's source copies.
   The directed theorem matches qcqs, nonempty directed indexing and arbitrary
   abelian sheaves, without a torsion condition; coefficient-size indexing needs
   only finite upper bounds. Checked singleton identity diagrams, zero sheaves,
   degree zero, the empty scheme, and the zero coefficient ring. The forgetful
   theorem is valid even for empty diagrams, giving the zero sheaf. The directed
   auxiliary is strictly the abelian cohomology step: it omits module coefficients,
   inverse image, and general filtered-category reindexing, each handled separately.
   New LeanFinder search for right-derived global sections and coherent directed
   colimits, Loogle search, and Mathlib grep found no exact replacement; the Loogle
   query reported an unknown identifier, rather than a successful exhaustive search.
   Searched upstream SixFunctors and EtaleCohomology and local cohomology modules.
   The existing filtered theorem has an index in `Type u`, so does not apply at
   `Type (u + 1)`. Closing the new cohomology theorem requires the substantial
   finite-cover and degree-induction infrastructure; it is not a short repair.
4. **Route and pruning: pass after import cleanup.** Restricting first uses the
   existing left adjunction and avoids an unnecessary module/abelian inverse-image
   comparison. Mathlib supplies directed final reindexing and cocone reflection.
   Checked `dag/units/sk-thm-p1.json` realized statement and steps: none is bypassed
   or edited. Computed the old/new direct proof-dependency difference; all six
   removed nodes occur in No longer needed. Every added import in the item is
   proof-only and serves the written reduction. Removal tests showed the new
   forgetful module already receives Z-module equivalence and change-of-rings
   infrastructure through its public import; removed those two redundant imports.
   Removing `Mathlib.CategoryTheory.Sites.Adjunction` fails synthesis of the
   compose-and-sheafify left adjoint, so that proof import stays.
5. **DAG agreement: pass after notation repair.** The item's four proof steps and
   proof_deps agree with its inverse-image, forgetting, final-reindexing, comparison
   and reflection proof. Read the new cohomology node's cited statements: qcqs
   permanence and finite affine refinements establish the basis; section-colimit
   and degree-zero results establish the base; functorial embeddings and exact
   colimits give the short exact sequence; injective Cech vanishing and the basis
   criterion establish acyclicity; natural connecting maps and the explicit
   cokernel chase establish induction; the natural derived-single identification
   identifies every leg. The new nodes have matching Lean records, sources,
   search records, creation data and blueprint provenance. Corrected the copied
   unintroduced base name `Y` to `X` throughout the directed node's proof. Corrected
   two forgetful-node search verdicts that accidentally described cohomology.

Second reading changed only two redundant proof imports, the directed-node proof's
base notation, the forgetful-node search verdict descriptions, and this report.
