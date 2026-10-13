## What changed

Proved `AlgebraicGeometry.properFlatImage_globalHomBaseChange_isIso` with its entire
signature and visibility unchanged. Constructed the structure sheaf in degree zero,
verified its boundedness, finite presentation, relative flatness and proper supports,
and applied `properSupport_perfect_directImage`. The right tensor unitor identifies
its output with Rf_*M. Localization transport preserves the given open-site family on X.

Used the perfect dual and the existing proved generic `monoidal_adjunct_isIso` helper
from `PerfectInternalHomPullbackIsIso` to prove the internal-Hom evaluation mate
invertible. A new private, proved helper `tensorHom_adjunction` constructs the
normalized tensor-Hom adjunction in sheaf universe w alone; the existing public
canonical adjunction unnecessarily ties the module universe to w for this application.
Reuse of private localization and zero-finite-presentation helpers is by proof-only
`import all PerfectDirectImageBaseChange`, without copying those helpers.

Added `MixedAffineSectionsPullbackMate`, with one strictly smaller affine transport
statement, and used its equation to identify the displayed global map with an
isomorphism followed by global sections of the internal-Hom mate. Updated the assigned
node's route and added the new node. All added imports are proof-only in the assigned
module; no existing statement, definition, public import or other module was changed.

## Proved and sorry left

Closed `AlgebraicGeometry.properFlatImage_globalHomBaseChange_isIso`
(node `lem-sc-proper-flat-image-global-hom-base-change-isIso`): 1 of 1 original holes.
The assigned module has no remaining sorry, and its new private helper is proved.

Added exactly one hole: `AlgebraicGeometry.exists_mixedAffineSectionsPullbackMate`
(node `lem-sc-mixed-affine-sections-pullback-mate`), in its own new module. This is a
**decomposition**, with holes closed 1 and holes added 1; net holes 0. The remaining
lemma concerns affine scalar extension of any quasi-coherent derived object and
adjunction mates. It neither mentions f nor assumes properness, flatness or perfectness,
and it does not assert invertibility of internal Hom. Perfectness and invertibility
are proved separately and combined in the assigned theorem.

Existing imported statements may still depend on sorry; these are existing work,
not holes introduced by this delivery.

## No longer needed

Removed proof import `Sheaf.Algebra.Homology.BaseChangeRHomPerfect` and removed
`lem-pc-base-change-rhom-perfect` from this node's proof dependencies. The explicit
bounded projective module RHom scalar-extension calculation and its dependencies
are not needed by this proof: perfect duality and strong monoidal pullback give
internal-Hom invertibility before taking affine sections.

The new route does not need `Sheaf.AlgebraicGeometry.MixedPerfectInternalHomPullbackIsIso`
(node `lem-sc-mixed-perfect-internal-hom-pullback-isIso`); its conclusion is proved here
using the generic categorical helper already proved in
`Sheaf.AlgebraicGeometry.PerfectInternalHomPullbackIsIso`.

The FlatAffineGlobalHomComparison public import remains because it supplies the
mixed comparison definition. Its scalar-square theorem is not used by this proof.
MixedHomTensorPullbackIso and MixedGlobalSectionsDirectImageIso remain used through
that definition and the new mate equation. ProperSupportPerfectDirectImage stays used.
These are local pruning claims, not claims that another target never needs the nodes.
The unit record has no realized nodes for its statement or step; the chapter and unit
route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan mixes a ring-site RHom model with independently chosen ModuleCat
and sheaf localization universes; its named interfaces do not directly provide the
normalized transport equality. The new affine mate lemma isolates that equality,
without repeating the assigned theorem. The perfect internal-Hom map is handled by
existing rigid-category infrastructure rather than another algebraic comparison.

The checkout contains only literature indexes, not the cited Stacks TeX files. Read
the official Stacks pages for 0AA8, 0A1H and 08DW instead. Tag 0AA8 explicitly uses
perfectness of Rf_*M and the affine scalar-extension identification. The new lemma
is the adjunction-compatible affine formula, not a new geometric claim.

Initial compilation found the new mixed-perfect module absent from the shared cache.
Temporary unchanged sandbox copies used during diagnosis were removed, including
all their compiled artifacts. The final route compiles against the shared cache and
does not import that absent module.

## New nodes

`lem-sc-mixed-affine-sections-pullback-mate`, module
`Sheaf.AlgebraicGeometry.MixedAffineSectionsPullbackMate`: derived scalar extension
of affine sections agrees with pullback, including the equation for every sheaf
adjunction mate. Source: Stacks 06Z0, 08DW(2), 08HY, 0D5T, and the identification of beta
in 0AA8. Its complete proof in words explains the K-flat affine formula, compatibility
of adjunction units and normalized Leray, and independent localization universes.
Searches ran through msearch: LeanFinder returned unrelated affine-space/Ext facts,
Loogle returned only Kan-extension adjunction facts, Mathlib grep returned no match,
and LeanSearch returned HTTP 500. Repository and blueprint searches found the related
scalar-square mate but no statement of this pullback-only equation.

Edge cases: E=0 or an empty affine scheme give the unique zero map. For g the identity,
unit and triangle equations give the identity comparison. Nonflat g is permitted since
scalar extension and pullback are derived; unbounded E is resolved by K-flat complexes.
The isomorphism is never used as an arbitrary witness in a definition: it is obtained
inside the theorem proof, together with its characterizing mate equation. No new data
definition or change record is required.

## Second reading by U4

1. **Signatures unchanged.** Compared the delivered target module with the repository version; the target theorem signature and all existing declarations are byte-for-byte unchanged. The only added declaration is the separately named split-off mate theorem, with its node and change-free interface recorded above.
2. **Compilation and proof hygiene.** Compiled both delivered modules with `lcompile.py`; both pass with no errors or warnings. The target proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; the sole remaining `sorry` is the named public split-off theorem. The proof uses only the permitted existing infrastructure and the split theorem.
3. **Split-off statement.** `exists_mixedAffineSectionsPullbackMate` is a genuine affine transport/mate equation, strictly smaller than the target: it has no properness, flatness, perfectness, or invertibility assumptions and does not assert the target isomorphism. Its statement is mathematically true in the stated derived setting, has a complete source-based proof docstring, and has the matching DAG node.
4. **Route and pruning.** The target proof follows the realized unit route: proper-support perfect direct image, perfect internal-Hom pullback, then affine sections mate transport. The removed RHom base-change import and dependency are unused by the final proof; the updated node records the remaining dependencies and the new split node.
5. **Definitions and imports.** No definitions or public interfaces were changed. Added imports are proof-only except for the new mate module's public statement dependencies; imports compile in the declared order and no existing declaration is duplicated.

Changed during second reading: no Lean statements or definitions; added this review section only.
