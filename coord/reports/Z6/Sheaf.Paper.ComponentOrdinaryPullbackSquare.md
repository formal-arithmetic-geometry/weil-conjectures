## What changed

Proved `component_ordinary_pullback_square` from three strictly smaller geometric
obligations. Its proof constructs the internal-module comparison rather than
assuming it: the coefficient equation is inverted by cancellation, the action of
a twice-transported module is computed explicitly, monoidality and naturality
prove linearity, and `Mod.isoMk` lifts the abelian isomorphism. Composing with
`Mod.extendScalarsIsoComapInv` gives the actual scheme module pullback, with the
required underlying-map equation by definition. The final structure assembly
uses the separately stated coherence equations.

New modules are `ComponentOrdinaryEdges`, `ComponentOrdinaryAbelianSquare`, and
`ComponentOrdinarySquareCoherence`. They retain the original construction (4.1)
route, separate existence from transport and coherence, and contain full proof
instructions with the original literature source. The chosen edge data are
normalized by their actual inverse functors, specified adjunctions, canonical
oplax maps, coordinate-preserving test maps and mate formulas. These uniquely
determine the objects up to the equality used here. No arbitrary witness of an
unconstrained existence theorem is used to define the module transport.

`ComponentDerivedSquareData` needs a compile-performance repair before the item
can be imported. Its ordinary module functors, derived functors and derived comparisons have explicit result types.
The two derived functors and five comparison bodies are marked irreducible, and its
tensor-square equations are factored through a generic predicate with the same
tensor and unit equations. The large System and OrdinarySystem coherence fields
refer to generic squareIdentity and squareComposition definitions, whose bodies
are the original equations verbatim with functor parameters. The definition change is recorded
in `coord/changes/component-ordinary-derived-folding.md`. The proved derived-coherence consumer explicitly unfolds those comparisons and the two derived functors where its original proof used definitional equality. No target or
ordinary data requirement is changed; target meaning is preserved, and the definition
repair is submitted for independent review.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.ProEtale.ComponentDerivedSquare.component_ordinary_pullback_square`
(node `lem-zl-component-ordinary-pullback-square`). Its proof compiles without
`sorry`. The private action, linearity, isomorphism and scalar-cancellation
helpers are proved directly.

Added three holes, each exactly `:= by sorry` in its own module:

- `AlgebraicGeometry.ProEtale.ComponentDerivedSquare.component_ordinary_edges`
  (`lem-zl-component-ordinary-edges`): actual edge and intrinsic slice construction.
- `AlgebraicGeometry.ProEtale.ComponentDerivedSquare.component_ordinary_abelian_square`
  (`lem-zl-component-ordinary-abelian-square`): one normalized monoidal abelian
  square and its coefficient equation, without any module transport or coherence.
- `AlgebraicGeometry.ProEtale.ComponentDerivedSquare.component_ordinary_square_coherence`
  (`lem-zl-component-ordinary-square-coherence`): identity and composition for
  already supplied normalized squares; constructs no edges or squares.

This is a decomposition: one upper hole closed and three strictly smaller holes
added, net minus two. It is not a claim that the geometric obligations are proved.
The shared data module has zero holes before and after its definition repair.
The complete ordinary-module assembly was compiled successfully (9.4 seconds).
The repaired data module compiled in 41.4 seconds with its profiling trace,
and the generic monoidal predicate was independently checked equivalent to the
original tensor and unit conjunction (1.6 seconds).

## No longer needed

Removed proof imports from the item:
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
`Sheaf.CategoryTheory.SiteInverseImageTensor`,
`WeilConjectures.CategoryTheory.SiteMorphismComposition`,
`Sheaf.CategoryTheory.GeometricModuleTransport`, and
`Sheaf.CategoryTheory.Sites.GeometricInverseImageExact`.

The old direct proof dependencies are now cited only by the appropriate smaller
geometric obligations. In particular the generic geometric-module-transport and
geometric-inverse-image-exactness nodes (`lem-weil-pbc-geometric-module-transport`,
`lem-trf-geometric-inverse-image-exact`) are not used by the module lift here:
its exactness is already part of Corner/Slice, and its linearity is proved for
the existing internal-module encoding. They may still be needed elsewhere; no
module is withdrawn. The source-library declarations and their imports remain.

The normalized edge lemma does not import
`Sheaf.AlgebraicGeometry.ComponentPointMonoidalFactorization`: its existing
existence statement does not prescribe the absolute test coordinates or beta
mate required by Corner. The normalized geometric edge obligation supplies those
extra equations, rather than choosing an arbitrary unnormalized factorization.

No unit statement or realized unit step is bypassed. No module is pruned in this
packet; unnecessary private imports are removed.

## Where the brief, the DAG or earlier work was wrong

The stated geometric-module transport theorem uses another module-sheaf encoding
and does not directly construct the internal `Mod` comparisons required by the
item. The direct action calculation in this delivery supplies that missing glue.
The original data module also repeatedly exceeded the compiler limit before the
worker's proof was checked. Profiling identified expensive derived comparison
types and tensor-instance elaboration; the recorded repair avoids recomputing
those definitions without changing the mathematical equations.

The previously split ordinary obligation bundles substantial independent site
constructions and coherence. This delivery separates those tasks and proves the
nontrivial internal-module transport between them. The new statements include
empty affine schemes and zero coefficients: they require no nonemptiness,
nonzero-ring, connectedness, or finiteness hypothesis.

## New nodes

`lem-zl-component-ordinary-edges` owns `OrdinaryEdges` and its existence theorem.
It is Step 1 and the intrinsic slice part of Step 5 of the old argument, and
contains no component square. It cites the proved exact monoidal component
inverse-image theorem rather than reproving it.

`lem-zl-component-ordinary-abelian-square` owns `NormalizedAbelianSquare` and
its existence theorem. It is the test-object mate and coefficient comparison of
Steps 2–3, before the internal-module lift actually proved in this packet.

`lem-zl-component-ordinary-square-coherence` is Step 5 for already constructed
normalized squares. Its proof instructions reduce to test-object projections,
coherent adjunction mates and faithfulness of the forgetful functor.

Each node records actual LeanSearch, LeanFinder and source-grep searches, and the
blueprint searches found no duplicate of the component-specific obligations.
The existing item node now records exactly this three-part reduction and the
proved module-action calculation. The existing definition node owns the generic
tensor-square and coherence helpers. Change record:
`coord/changes/component-ordinary-derived-folding.md`.

## Forced adaptations

`Sheaf.Paper.ComponentDerivedSquareCoherence` is unclaimed. The original file
fails with a type mismatch at both calls to `derived_identity` and
`derived_composition`: their conclusions contain
`Functor.mapDerivedCategorySquareIso` and `mapDerivedCategoryTriangleIso`,
where the goal contains the now irreducible `Square.theta`,
`SliceIdentity.derived` / `SliceComposition.derived`, and
`schemeIdentity` / `schemeComposition`. Added one `unfold` command in each
branch, naming those comparisons, their path abbreviations and the two derived functors, and the original proof compiles.
Its statement and all signatures and visibility are identical.

`Sheaf.Paper.ComponentDerivedPullbackSquare` is unclaimed. Its original two
monoidal-instance assignments fail because `(t.corner X).monoidal` and
`(t.slice f).monoidal` have type `(Corner.modules ...).mapDerivedCategory.Monoidal`
and `(Slice.modules ...).mapDerivedCategory.Monoidal`, while the expected types
contain the folded `Corner.derived` and `Slice.derived`. Each assignment now
unfolds the corresponding derived functor before applying the original term.
All signatures and visibility stay identical.

`Sheaf.AlgebraicGeometry.CondensedGenericScalarModelData` is unclaimed. Its
original `cornerScalarComparison`, `SectionComparison.identityDerived` and
`SectionComparison.scalarDerived` bodies fail type matching between
`Corner.derived` / `Slice.derived` and `modules.mapDerivedCategory`. Each body now
unfolds only the appropriate derived functor and applies the original localization
term. Their signatures, scalar comparisons and normalization data are unchanged.

`Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity` is unclaimed. The
original corner-equivalence proof fails at `hd.symm` because its comparison targets
`componentDerived` rather than the folded `Corner.derived`; explicitly unfold the
corner functor in the hypothesis and goal before the original proof. The slice
equivalence instance no longer unfolds through `dsimp only`; use `unfold` instead.
Its two monoidal instance assignments have the same type mismatch as the derived
assembly consumer; explicitly unfold the slice derived functor in those assignments.
The original equivalence and tensor terms are retained, with no signature changes.

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
