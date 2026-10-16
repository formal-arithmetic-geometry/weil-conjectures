## What changed

Moved the unchanged explicit restriction, restriction/pullback isomorphism, inverse mate,
and mate-counit theorem to `IntegralResiduePullSquareData`, publicly re-exported by the
original module. Added two explicit typed wrappers for the existing derived counits;
these prevent elaboration from unfolding the large derived-functor construction.
All existing names, signatures, visibility and defining terms are preserved.

The original theorem now follows from two fully written arguments. Invertibility uses
an actual functorial flat resolution, the scalar counit on a K-flat complex, invertible
exact-pullback counits, localization of the ordinary pull isomorphism, cancellation,
and naturality along the resolution isomorphism. Composition uses a proved generic
inverse-mate pasting theorem. Its restriction-square hypothesis is derived from the
ordinary composition equation using the existing proved exact-derived square-pasting API.

New proof-only imports of the main module are `IntegralResiduePullSquareIsIso` and
`IntegralResiduePullSquareComp`; their obligations are ordinary composition and a
flat-resolution computation. The coherence proof keeps the existing derived-functor and comparison constructors
locally irreducible, so simplification uses their API without unfolding their large
constructions. No other existing module is adapted. The change record is
`coord/changes/B2-integral-residue-pull-square-data.md`.

Validation: all eight delivery modules compile cleanly, each within the 60-second
single-file limit. The unchanged downstream consumers `IntegralResidueTensorPresentation`,
`IntegralResidueTensorGeometry`, `IntegralResidueTensorSquare`, and
`IntegralResidueProjectionNormalization` also compile against the delivered overlay.
The four moved declaration bodies and all existing signatures are unchanged.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_pullSquare`
(1 of 1). This is a decomposition, not a net hole reduction: two new holes remain, so
closed minus added is -1. The original module has zero remaining holes.

The following new theorems have complete Lean proofs:

- `CategoryTheory.inverseMate_pasting`.
- `AlgebraicGeometry.ProEtale.CondensedRing.residueExchangeRestrictPullIso_comp`.
- `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_pullSquare_isIso`.
- `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_pullSquare_comp`.

The only two added holes are:

- `AlgebraicGeometry.ProEtale.CondensedRing.residueExchangePull_flatModel`, node
  `new-integral-residue-pull-flat-model`. It still needs flat preservation for ordinary
  pullback on internal coefficient modules, the resulting K-flatness of the image of
  the specified colimit presentation, and the derived mate/counit normalization of
  ordinary `pullIso`. The statement is restricted to the flat-resolution presentation
  used by the caller. It does not assert invertibility on all derived objects or any
  composition law. The caller performs the resolution, cancellation and transport steps.
- `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_ordinaryRestrictPull_comp`,
  node `new-integral-residue-ordinary-restrict-pull-comp`. It still needs the ordinary
  coefficient-action calculation identifying the two paths with the specified
  `upperStarComp` (defined by conjugating `lowerStarComp`). It contains no derived
  categories, derived scalar extension or mate invertibility claim. Derived transport
  and the subsequent mate-pasting argument are proved by the delivery.

Both residual statements retain arbitrary scheme morphisms and arbitrary normed
coefficient fields as in the original. Zero complexes/modules, identity morphisms,
and empty schemes introduce no extra hypothesis. Reduction is never assumed flat.
No definitions contain holes and no arbitrary data are extracted to define a comparison.

## No longer needed

No existing node or module is pruned. Removed the exploratory proof import
`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`; the construction uses
the basic flat-resolution API directly. The original direct public import of
`IntegralResidueComparisonInterface` is replaced by the public data module, which
publicly imports the same interface; this is a relocation, not a pruning claim.

The proof does not need `IntegralResidueTensorGeometry`, `IntegralResidueTensorSquare`,
or `IntegralResidueProjectionNormalization` (they are downstream and would create a cycle).
It does not import `ContinuousIntegralPullComposition`: that module's relevant scalar
argument requires flat coefficient extension, which is unavailable for residue reduction.
Temporary experiments are excluded from the delivered Lean files.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt could not acquire a shared delivery worktree. This session reran
its proof experiments and the required dry run. The ordinary finite-coefficient
`upperStarRestrictScalarsIso_comp_hom` theorem does not apply directly: its objects are
sheaves valued in `ModuleCat`, whereas this item uses internal `Mod` objects with the
specified coefficient-pullback isomorphisms. Expanding the ordinary comparison leaves
the unit/counit compatibility with `upperStarComp`; the flat-model experiment leaves
K-flat preservation and the scalar counit normalization. Neither experiment closes an
additional hole, and no further split was added.

The dry run completed successfully at 21:33 on 2026-10-16: all eight delivery modules
compiled and preflight passed, except for the second reading reserved for the next
worker. Nothing was pushed. The original coherence-file timeout had already been
repaired by keeping the large derived comparison constructors locally irreducible.
The prior report's worktree-blocker status is therefore superseded.

An isomorphism of restriction/pullback squares does not in general have an invertible
inverse mate. The coefficient-specific flat-resolution argument is essential. The
initial decomposition into just invertibility and coherence has been carried further:
both are proved from the two strictly lower computations described above.

The library already contains `Functor.mapDerivedCategorySquareIso_hom_app_comp` in
`WeilConjectures.SixFunctors.ProEtale.Derived.RestrictScalars`; it supplies the derived
composition transport without rebuilding localization coherence. No unit statement or
unit proof step is bypassed, and no target statement or meaning changes.

## New nodes

`new-integral-residue-pull-square-data` records the unchanged explicit constructions and
new typed counit wrappers; its proof has no holes.

`new-integral-residue-pull-flat-model` records the residual scalar computation on the
specified flat-resolution complexes, with source and proof in its docstring.

`new-integral-residue-ordinary-restrict-pull-comp` records the residual ordinary
restriction/pullback composition calculation, with source and proof in its docstring.

`new-integral-residue-restrict-pull-comp` records the proved exact-derived transport
from ordinary composition to the restriction comparison used by the original module.

`new-integral-residue-mate-pasting` records the proved generic inverse-mate pasting
identity, using the adjunction hom equivalence and unit identities.

`new-integral-residue-derived-pull-square-isIso` records the proved resolution,
cancellation and naturality argument for mate invertibility.

`new-integral-residue-derived-pull-square-comp` records the proved application of mate
pasting to the three scalar adjunctions. The existing parent node is updated to follow
these actual proof dependencies. Change record:
`coord/changes/B2-integral-residue-pull-square-data.md`.

## Second reading by B2

1. Compared the delivered `IntegralResiduePullSquare` module with the repository version. The target theorem's signature and the signatures of all existing declarations are unchanged; the four moved declarations are byte-for-byte unchanged in their bodies and interfaces, and the relocation is declared by `B2-integral-residue-pull-square-data.md`. Verdict: pass.

2. Compiled all eight delivered modules with `lcompile.py --all`; each compiled without errors or warnings and within the single-file limit. Searched the delivery for forbidden constructs and found only the two named `sorry` declarations, each with a matching split node; no definition contains a hole. Verdict: pass.

3. Reviewed every split statement and searched the repository for duplicate declarations. The two residual statements are strictly lower computations than the parent and retain the original generality; the proved helper statements are needed by the actual proof and are not restatements of the item. Their docstrings give sources and complete proof plans, and each has a matching DAG node. Verdict: pass.

4. Read the proofs top-down. The route uses the explicit data construction, the flat-resolution cancellation argument, exact derived square transport, and generic inverse-mate pasting. The unit route and realized steps remain represented; no target statement or definition was weakened. Removed proof-only exploratory imports are recorded above. Verdict: pass.

5. Checked the DAG metadata against the Lean declarations: proof steps and `proof_deps` match imports and theorem applications, and the parent node records the delivered route. Verdict: pass.

Changed after this reading: appended this review only; no Lean proof, statement, definition, import, or node metadata required repair.
