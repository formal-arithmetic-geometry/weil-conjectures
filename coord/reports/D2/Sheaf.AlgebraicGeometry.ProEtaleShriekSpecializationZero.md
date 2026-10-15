## What changed

Proved `AlgebraicGeometry.Scheme.ProEt.shriek_sections_subsingleton_of_specializes_closed`
in `Sheaf.AlgebraicGeometry.ProEtaleShriekSpecializationZero`, with its signature unchanged.
Four fully proved private helpers construct the closed-specialization localizations, refine
covering sieves to finite affine localized coverings, exclude lifts to the disjoint open-side
object, and prove that the presheaf Kan extension has zero sections on the refined objects.
The main proof uses local surjectivity of abelian sheafification and sheaf separatedness.

The route remains Stacks Tag 09AG, lemma-jshriek-zero, within the existing proper-base-change
unit. The closed subset is presented by an ideal using the affine spectrum's topology. Maps
from the closed fibre to the empty pullback replace a residue-field detour. The source
library's already-proved final-discrete indexing theorem computes the Kan extension without
importing the module-valued extension-by-zero presheaf interface. The existing docstring's
historical proof plan is preserved; the DAG now describes the actual implementation.

Added private proof imports `Mathlib.CategoryTheory.Sites.LocallySurjective` and
`Mathlib.Algebra.Category.Grp.Zero`. The affine-localization module was already imported.
Updated the item's proof, proof dependencies and proof origin. Attached the source library's
proved indexing theorem to one new DAG node; no new Lean module was added.

Validation: repeated single-file compilation passes cleanly (about 2.5 seconds). The new
private helpers and the main theorem contain no `sorry`. The source indexing theorem and
`AlgebraicGeometry.Scheme.ProEt.isTerminalSectionsOfIsEmpty` have only `propext`,
`Classical.choice` and `Quot.sound` in `#print axioms`.

## Proved and sorry left

Holes closed: one, named
`AlgebraicGeometry.Scheme.ProEt.shriek_sections_subsingleton_of_specializes_closed`
(node `lem-weil-pbc-proetale-shriek-specialization-zero`).

Holes added: none. Holes remaining in the item: none. Split-offs: none.

The completed proof uses the existing stated theorem
`AlgebraicGeometry.affineClosedSpecializationLocalization`
(node `lem-weil-pbc-affine-closed-specialization-localization`), whose proof remains `sorry`
in the shared library. This planned dependency is not changed or duplicated. Consequently
`#print axioms` for the completed item still includes `sorryAx` through that dependency.

## No longer needed

Removed imports:

- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization` (formerly public).
- `Sheaf.CategoryTheory.ExtensionByZeroPresheaf`.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.
- `Sheaf.Paper.SiteSheafificationSectionsLocal`.
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`.
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`.

Removed proof dependencies:

- `lem-weil-pbc-site-sheafification-sections-local`: Mathlib's locally-surjective
  sheafification unit supplies local representatives directly.
- `lem-weil-pbc-closed-immersion-base-change`: only the closed image and its topological
  inverse images are needed.
- `lem-weil-proetale-weakly-etale-localization`: use existing small-site maps and
  weakly-etale composition/cancellation instances.
- `lem-weil-pbc-spec-colimit-limit`: spectral maps between affines verify the covering
  condition, without a scheme limit argument.
- `def-weil-extension-by-zero-presheaf`: use the canonical Kan extension and the already
  proved source indexing result.

These are local proof-dependency removals. Some of these nodes are also statement
dependencies or needed elsewhere in the project. No globally unreachable module is asserted.
The two removed direct geometry imports remain transitively available where their basic
APIs are used. The proper-base-change unit's statement and realized steps are retained.

## Where the brief, the DAG or earlier work was wrong

No statement was found false or changed. The DAG's mathematical route works, but its manual
construction of group operations on set sheafification, closed-immersion presentation,
spectrum-limit argument for affineness, and residue-field construction are unnecessary.
The source library already contains the final discrete Kan-extension computation needed
for arbitrary weakly-etale maps; no monomorphism assumption or coefficient restriction is
added. Empty schemes and empty covering families are included in the implemented argument.

## New nodes

`lem-weil-pbc-localization-kan-discrete-lifts` attaches the existing, fully proved
`AlgebraicGeometry.SmallSite.exists_final_discrete_costructuredArrow_overMap` in
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`. It records the
generic categorical computation needed by the presheaf-vanishing step, including the
explicit lift type, the adjunction proving finality, and the empty case. Its Lean record
uses `existing: true`; no new theorem, module or hole is introduced. Blueprint search
`final discrete localization` found no matching node. Mathlib searches and source inspection
are recorded in the node; LeanSearch was unavailable and was recorded as such.

Change record: `coord/changes/proetale-shriek-specialization-zero-imports.md`.

## Second reading by D2

1. **Signatures and accidental changes — pass.** I diffed the delivered module against the
repository version. The target theorem and every existing declaration keep the same
signature; the only module changes are proof-private imports and the completed proof.
The DAG target statement is unchanged, while its proof, proof dependencies, and origin
record the implemented route. The import change is documented in
`coord/changes/proetale-shriek-specialization-zero-imports.md`.

2. **Proof and axioms — pass.** The module compiles cleanly with
`python3 /home/ubuntu/weil-launcher/lcompile.py` and contains no `sorry`, forbidden
commands, or hollow definitions. The scratch axiom check gives only
`propext`, `Classical.choice`, and `Quot.sound` for the source indexing theorem and
`isTerminalSectionsOfIsEmpty`; the target additionally inherits `sorryAx` only through
the pre-existing affine closed-specialization localization dependency.

3. **Split-off statements — pass.** No Lean theorem with `sorry` was added. The one new
DAG node records the already-proved source-library final-discrete indexing theorem with
`existing: true`; it introduces no hole and is not a restatement of the target. The
source declaration was searched and compiled directly.

4. **Top-down proof and pruning — pass.** The proof follows the unit route: locally
represent sheafified sections, refine a covering to finitely many affine localizations,
show the localization presheaf is zero by the final discrete lift computation, and use
sheaf separatedness. The removed imports and proof dependencies are listed in
`## No longer needed` and the change record; no unused proof dependency remains. The
proper-base-change unit and its realized route are retained.

5. **DAG and report agreement — pass.** The target node's proof steps and
`proof_deps` match the declarations used in the module, and the new node has the
required statement, source, proof, search records, Lean record, chapter, and unit.
The report and import change record describe the same proof and pruning decisions.

I found no proof or statement defect to repair. I added this second-reading section to
record the five checks and their verdicts.
