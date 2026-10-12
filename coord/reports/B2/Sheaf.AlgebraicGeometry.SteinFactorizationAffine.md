## What changed

Proved `AlgebraicGeometry.Scheme.Hom.steinFactorization_affine` with its signature and
statement unchanged. Second reading narrowed the GammaSpecAdjunction source import to proof-only, retaining the Mathlib public import needed by the signature. Integrality uses Mathlib and the affine global-sections
isomorphism. Properness follows from `IsProper.of_comp` and the Stein factorization
identity. Geometric connectedness uses the existing étale criterion and normalized-fibre
theorem. An affine open neighbourhood of each étale point permits use of the already proved
`AlgebraicGeometry.isPushout_appTop_of_flat`; the pushout of an isomorphism is an
isomorphism. Pullback pasting and the open-immersion residue-field isomorphism identify
the relevant fibres. Mathlib supplies the final ordinary-fibre and inverse-image assertions.

Added the proof import
`WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections`.
Updated the item's node proof and dependencies to describe this route. No statements,
definitions, universes, or declaration visibility changed. The source import visibility correction is recorded in `coord/changes/SteinFactorizationAffine-proof-import.md`. The unit's realized statements and steps stay.

Validation: the complete module compiles through `lcompile.py`. Sources inspected include
Mathlib Proper, Fiber and ResidueField, the existing criterion and normalized-fibre modules,
and Stacks `theorem-stein-factorization-general` (Tag 03H2) in the local literature copy.
Searches used leanfinder, loogle, msearch grep, and repository/Mathlib ripgrep.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.Hom.steinFactorization_affine`
(node `lem-weil-pbc-stein-factorization-affine`). There are no sorries left in the item,
no new modules, and no new holes added. The proof uses the existing stated dependencies
`AlgebraicGeometry.Scheme.Hom.geometricallyConnected_fiber_iff_connectedSpace_etale_neighbourhood`
and `AlgebraicGeometry.Scheme.Hom.connectedSpace_fiber_of_isProper_of_globalSections_iso`,
which remain sorry in their own modules. They are the next proof tasks, not holes added here.
The imported source flat-base-change declaration is already proved.

## No longer needed

Removed direct imports:
- `Sheaf.AlgebraicGeometry.ProperGlobalSectionsFlatBaseChange`;
- `Sheaf.AlgebraicGeometry.SteinUniversallyClosedFactor`.

Removed direct proof dependencies:
- `lem-weil-pbc-stein-flat-base-change-global-sections`: replaced by the proved source
  flat-base-change pushout theorem, represented by the Mathlib leaf
  `lem-weil-pbc-flat-base-change-global-sections-qcqs`;
- `lem-weil-pbc-stein-universally-closed-factor`: the first morphism's properness follows
  directly by proper cancellation; its global-section map is the adjunction isomorphism;
- `lem-weil-pbc-separated-cancellation`: proper cancellation handles the whole assertion;
- `def-weil-proper-morphism`: no separate proof step uses its defining conjunction; it remains a statement dependency.

These nodes may still be needed transitively by other modules, including the normalized-fibre
module. This is pruning of this theorem's direct proof route, not a claim that the whole
project can delete them. The proper-permanence node stays for base change. The exact
Mathlib leaf `lem-weil-pbc-proper-over-separated` supplies cancellation; although its unit
is `sk-thm-reduction`, it is a Mathlib leaf rather than an unproved cross-unit tool.

## Where the brief, the DAG or earlier work was wrong

The old plan required substantially more Stein-factorization machinery than this theorem
needs: Mathlib already proves proper cancellation and the source library already proves
flat base change for global sections. The existing theorem docstring records that earlier
plan; the updated node and the Lean proof give the implemented route. No statement was
found false or changed. The affine-neighbourhood passage is needed because the existing
étale criterion tests arbitrary schemes U, while flat base change here has affine base.

## Second reading by B2

1. **Statements and visibility.** Compared the delivered module with `sheaf-dag`; the theorem signature, existing declarations, definitions, and universes are unchanged byte for byte. The proof-only source GammaSpecAdjunction import is now plain `import`; Mathlib GammaSpecAdjunction remains public for the signature. The node statement is unchanged.

2. **Proof and axioms.** Compiled the module with `lcompile.py` successfully. The theorem has no `sorry` in the delivered file; its only `sorryAx` dependencies are the two pre-existing open fibre lemmas it invokes. The source flat-base-change theorem is proved and uses only permitted axioms. No forbidden declarations occur.

3. **Split statements and reuse.** No statements were split off and no new nodes or modules were added. The proof uses existing declarations and the Mathlib properness and fibre results; repository searches found no duplicate theorem. The existing open lemmas are strictly smaller prerequisites, not restatements.

4. **Pruning and route.** The proof follows the affine étale neighbourhood route of the node and retains the unit route `sk-thm-p1`; it removes only the two unused direct imports and the obsolete direct proof dependencies recorded above. The remaining imports are used by the proof or its existing prerequisites.

5. **DAG agreement.** Checked that the node proof steps and `proof_deps` describe the implemented route, including the source pushout declaration, properness instances, the étale criterion, normalized-fibre theorem, and fibre homeomorphism. The unit's `realized` fields are unchanged.

Second reading changed the proof-only source GammaSpecAdjunction import from public to plain, added the corresponding Mathlib public import for the existing signature, and completed the pruning list with `def-weil-proper-morphism`. No proof changes were needed. The import change record lists all 208 downstream modules; no adaptations are necessary.
