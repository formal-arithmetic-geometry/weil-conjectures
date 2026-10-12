## What changed

The signature and public imports of `exists_cechComparisonSystem` are unchanged.
Its proof now constructs natural transformations from objectwise canonical maps,
checks degree-zero equality by natural-transformation extensionality, and supplies
the connecting law from the canonical endpoint boundary theorem.

New concrete construction module: `AbelianCechComparisonConstruction` defines the
section complex, the double complex with Čech degree first, the actual chain maps
`abelianCechAlpha` and `abelianCechBeta`, and `IsAbelianCechComparison`. All definition
data and chain-map proofs are complete. The predicate uses Ext cocycles evaluated
at 1 through the constant-sheaf adjunction. It quantifies over every injective
resolution, and contains neither a normalization nor a boundary axiom.

`AbelianCechAlphaQuasiIso.abelianCechAlpha_quasiIso` is proved using the existing
source-library injective Čech exactness and gluing theorems and the proved
first-quadrant augmentation criterion. Degree-zero cycles are transported through
`isoSc'`; the invertible homology projection then gives the row quasi-isomorphism.
This theorem is explicitly supplied to the objectwise comparison existence lemma.

Three new statement modules isolate the remaining argument:
`AbelianCechComparisonMaps`, `AbelianCechComparisonNaturality`, and
`AbelianCechComparisonBoundary`. Each contains one named public theorem, exactly
`:= by sorry`, with a source and a complete proof in words. In particular the
boundary lemma requires the explicit augmentation-quotient characterization,
which is substantially stronger than an arbitrary normalized family of maps.
All existential choices are local to the main theorem's proof; no definition
chooses arbitrary data from an unproved existence theorem.

All six delivered Lean modules compile without warnings through `lcompile.py`.
The second reading also restored the plain proof imports of the augmentation
quasi-isomorphism in the naturality and boundary modules and of prescribed
horseshoe resolutions in the boundary module, as their DAG plans require.
Searches: logged LeanFinder returned sheaf/Mayer-Vietoris and generic resolution
infrastructure, Loogle found the cohomology functor itself, and Mathlib grep found
no comparison construction. LeanSearch returned HTTP Internal Server Error and
is recorded unavailable. Direct source searches found the fully proved
`TopCat.Presheaf.exactAt_cechComplex_of_injective` and
`TopCat.Sheaf.isIso_toCechCohomologyZero_app`; the existing module-valued comparison
has different coefficient categories and is not a comparison for all abelian sheaves.

## Proved and sorry left

Closed the item's single direct hole:
`AlgebraicGeometry.Scheme.Modules.exists_cechComparisonSystem`
(node `lem-pc-cech-comparison-system-existence`).

Added three strictly smaller holes:

- `AlgebraicGeometry.Scheme.Modules.exists_abelianCechComparison_maps`
  (`lem-pc-abelian-cech-comparison-maps`): maps for one coefficient sheaf, their
  augmentation equation on every resolution, and their degree-zero value;
  no naturality between sheaves and no connecting law.
- `AlgebraicGeometry.Scheme.Modules.abelianCechComparison_naturality`
  (`lem-pc-abelian-cech-comparison-naturality`): equality for one coefficient
  morphism and degree between already canonical comparison maps; no existence
  and no connecting law.
- `AlgebraicGeometry.Scheme.Modules.abelianCechComparison_boundary`
  (`lem-pc-abelian-cech-comparison-boundary`): a boundary identity for one short
  exact sequence and degree between already canonical endpoint comparison maps;
  no existence or naturality of a comparison family.

This is a decomposition (one original hole closed, three added; local net -2),
not a complete proof of comparison existence. Separately proved
`AlgebraicGeometry.Scheme.Modules.abelianCechAlpha_quasiIso`
(`lem-pc-abelian-cech-alpha-quasi-iso`) and all construction definitions, with no
new holes in them. No original target statement or existing definition changed.

## No longer needed

Removed the proof imports
`Sheaf.AlgebraicGeometry.Cohomology.CechComparisonSystemComparison` and
`Sheaf.CategoryTheory.InjectiveCechAugmentationQuasiIso` from the item.
The former chooses zero in positive degrees and cannot supply boundary
compatibility. The latter's general-site chosen-product augmentation is replaced
by the fully proved topological injective Čech exactness and degree-zero gluing
interfaces. Neither imported theorem is used by the delivered construction.

Modules removed from this item's source import closure:
- `Sheaf.AlgebraicGeometry.Cohomology.CechComparisonSystemComparison`
- `Sheaf.CategoryTheory.CechZeroCocycleCompatibility`
- `Sheaf.CategoryTheory.InjectiveCechAugmentationQuasiIso`
- `Sheaf.CategoryTheory.SheafCechAugmentationDegreeZero`
- `Sheaf.CategoryTheory.SmallCechFreeComparison`
- `Sheaf.CategoryTheory.SmallCechFreeExact`
- `Sheaf.CategoryTheory.SmallInjectivePresheafCechExact`

DAG nodes whose modules leave that closure:
- `lem-pc-cech-comparison-system-existence-comparison`
- `lem-sc-cech-zero-cocycle-compatibility`
- `lem-sc-injective-cech-augmentation-quasi-iso`
- `lem-sc-sheaf-cech-augmentation-degree-zero`
- `lem-sc-small-cech-free-comparison`
- `lem-sc-small-cech-free-exact`
- `lem-sc-small-injective-presheaf-cech-exact`

These are local closure differences, not a claim that other targets or items no
longer need the modules. `CechComparisonSystemConnecting` is also not used: it
projects a law from an already existing system and cannot establish existence.
The temporary, unnecessary imports of `Mathlib.Algebra.Homology.ShortComplex.Ab`
and `Mathlib.Algebra.Homology.SingleHomology` were removed and the final set recompiled.

## Where the brief, the DAG or earlier work was wrong

The earlier arbitrary-family boundary interface was already corrected in
`coord/changes/cechComparisonSystem_comparison_connecting.md`. Its replacement
only projects the connecting field, so using it to construct that field is
circular. Likewise the existing normalized degreewise comparison witness uses
zero maps in every positive degree; normalization alone does not establish
boundary compatibility. This delivery uses neither as an existence argument.

The existing parent node's single step hides construction, naturality,
normalization, and boundary compatibility. It has been expanded to match the
actual Lean reduction. The group item's blueprint unit has empty `realized`
statement/step lists; no realized unit node is bypassed.

Sources actually read: Stacks Tags 01EQ and 01FD, Tag 013T for horseshoe resolutions,
and Tag 0117 for the functorial homology sequence. The earlier draft used 015I
as a horseshoe citation; reading the source showed that it is the
Cartan-Eilenberg existence theorem, and the delivered docstring cites 013T.

Edge cases checked mathematically: the zero sheaf, the degree-zero boundary,
empty cover of the empty space, and infinite index sets. The constructions are
nonnegative with finite total diagonals. There is no added finiteness, nonempty
index, affine-intersection, or acyclicity hypothesis on arbitrary coefficients.
A representing Ext cocycle always determines a section cycle by the constant
adjunction, so the defining predicate is not vacuous. Since alpha is invertible,
its equation fixes the comparison; different representatives cannot give
incompatible constraints. The boundary lemma needs canonicity only at its two
endpoints, since horseshoe resolution naturality provides the middle map.

## New nodes

`def-pc-abelian-cech-comparison-construction` records the concrete section/double
complexes, augmentations, and their Ext-cocycle characterization, in
`AbelianCechComparisonConstruction`. It introduces no arbitrary witnesses or holes.

`lem-pc-abelian-cech-alpha-quasi-iso` records the proved restriction-augmentation
quasi-isomorphism in `AbelianCechAlphaQuasiIso`.

`lem-pc-abelian-cech-comparison-maps` records the remaining objectwise normalized
map construction under the explicit, supplied alpha quasi-isomorphism hypothesis.

`lem-pc-abelian-cech-comparison-naturality` records coefficient naturality for
canonical maps. It is independent of the existence and boundary statements.

`lem-pc-abelian-cech-comparison-boundary` records boundary compatibility for
canonical endpoint maps, with tuple-surjectivity exactly as in the original system.

`lem-pc-topological-injective-cech-positive-exact` and
`lem-pc-topological-cech-zero-gluing-iso` attach the two existing, proved source
library interfaces used by the alpha proof to the DAG. They deliver no new Lean
module and introduce no holes. Their original source declarations are unchanged.

No change record or forced adaptation is required: all existing signatures,
definitions, and public imports are unchanged.

## Second reading by K3

1. **Unchanged interface: PASS.** Compared every delivered module with the
   read-only repository. Only `CechComparisonSystemExistence` already exists;
   its full theorem signature, docstring, visibility and public import are
   byte-for-byte unchanged. Its changes are the proof and plain proof imports.
   The other five modules are new. No existing definition or target changes.
2. **Kernel proof and holes: PASS as decomposition.** Recompiled all six modules
   locally in import order without errors or warnings. Appended `#print axioms`
   in a scratch probe for the four construction definitions, canonicity predicate,
   augmentation theorem, three split statements and original theorem. The
   construction and `abelianCechAlpha_quasiIso` use only `propext`,
   `Classical.choice`, `Quot.sound`; the three split statements and packaging
   theorem additionally use `sorryAx`, exactly as reported. Source scan found
   exactly the three named whole-proof holes and no forbidden declaration or
   holed definition. The choice in the packaging proof is local to a theorem;
   the public definitions use real complexes, restrictions and augmentations.
3. **Split statements: PASS.** Read the three signatures and docstring arguments
   against Stacks 01EQ, 01FD, 013T and 0117 and the actual Ext API. The canonicity
   predicate is not vacuous: `InjectiveResolution.extMk_surjective` supplies a
   representing cocycle for every output, and the constant-sheaf adjunction
   followed by evaluation at 1 identifies that cocycle with a section cycle.
   Monicity of `iCycles` fixes the cycle. The proved alpha quasi-isomorphism and
   the Ext/section identification therefore fix the comparison uniquely, without
   assuming naturality or boundaries in its definition. Resolution lifts give
   the naturality statement; split horseshoe rows and the two augmentation
   squares give the boundary statement at its two endpoints. Checked degree
   zero (both augmentations meet in (0,0)), zero coefficients, empty covers
   (the covering equation forces X empty), and infinite index sets (finite
   total diagonals, arbitrary products preserve the specified splittings).
   Each statement is strictly one part of the original system, has its own
   node, and carries a sourced proof in words. Independent LeanFinder search
   for the Ext/section identification, Loogle search for `extMk_surjective`,
   Mathlib grep for connecting maps and Ext representatives, and source `rg`
   searches found reusable Ext infrastructure but no existing statement of
   any of these three comparison assertions. The proved normalized-zero family
   is weaker and cannot replace them. None of the remaining holes admits a
   short direct application of the found declarations.
4. **Route and pruning: PASS after import repair.** The original proof really
   assembles objectwise maps, naturality, normalization and the endpoint boundary
   identity; it does not move the original assertion to a renamed hole. The
   alpha proof uses existing injective Cech exactness, existing degree-zero
   gluing, and the proved first-quadrant criterion. All public imports support
   exposed statements or definition bodies; the first-quadrant criterion is
   imported only for the proof. Recomputed the old and new source import
   closures: exactly the seven removed modules listed above leave this item's
   closure. In particular the old sole DAG proof dependency
   `lem-sc-injective-cech-augmentation-quasi-iso` is fully listed. The unit
   `sk-thm-picard-rr` has empty realized statement and step lists, and the
   existing chapter/unit route is unchanged. Added plain proof imports of
   `AbelianCechAlphaQuasiIso` in both unproved naturality/boundary modules and
   `HorseshoePrescribedResolutions` in the boundary module: these are stated
   proof dependencies and must stay available while the holes remain open
   (stages/2-statements.md section 3, rule 7). Homology-sequence and gluing
   dependencies are already available through the public signature imports.
5. **DAG agreement: PASS.** Checked all eight delivered JSON records, the parent
   signature against Lean, the new records' source/creation/blueprint/Lean
   fields, and the exact union of step uses against every `proof_deps` list.
   The parent records the four statements its proof applies; the augmentation
   node records the source exactness/gluing interfaces and first-quadrant
   criterion it applies. The three open nodes record their sourced remaining
   proof plans. No existing node's statement or statement dependencies change.

Second-reading changes: restored three plain proof-import lines in two new
statement modules and added this independent review and its search/axiom evidence.
No proof or signature was rewritten, no extra hole was added, and no hole was
closed by this reading. The direct accounting remains one original hole closed
and three smaller holes added (decomposition); the ledger, rather than this
local count, decides progress in the targets' complete import closure.
