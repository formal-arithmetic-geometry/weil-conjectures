## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceSingleComplexBaseChange` states
`AlgebraicGeometry.AlgebraicSpace.singleComplexBaseChange_isIso`, with `sorry` as its
only proof. It renders exactly Stacks `spaces-perfect.tex`, Tag 0DKH, using condition (1)
of 0DKG and equation-bc immediately preceding it. Those passages and the full five-step
DAG proof were read. The statement, proof, and source of the item are unchanged.
Five already landed definition nodes are added to `stmt_deps`; no new notions or
modules for dependencies are necessary.

Clause-by-clause correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`. All four spaces are
  `{X X' Y Y' : AlgebraicSpace S}`; their morphisms are the natural transformations
  supplied by that full subcategory. These use the recorded scheme and space notions.
- The size convention is the explicit universes `u w` and the common localization
  instances `[∀ Z : AlgebraicSpace S, HasDerivedCategory.{w} Z.SmallModules]`.
  This is the already published stalk-condition interface's ambient instance binder,
  recording the chosen derived localizations, rather than a geometric assumption.
  There is no equality imposed between `u` and `w`. The small affine ringed model is
  equivalent to the original small etale module topos, so it represents the same
  unbounded D(O). No nonemptiness or boundedness is imposed.
- `f`, `f'`, `g`, `g'` have precisely the four types in the node's square;
  `sq : IsPullback g' f' f g` says that X' with these projections is its fibre product.
  Using an arbitrary cartesian square allows every choice of that fibre product.
- `hqc : MapIsQuasiCompact f.hom.hom` tests compactness of the point space of every
  affine scheme base change, with the existing atlas topology. This is the published
  quasi-compactness notion, invariant under etale chart tests.
  `hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom)` is quasi-compactness of the
  relative diagonal, hence quasi-separatedness. No separatedness is imposed.
- `K : X.DerivedModules`, `hK : X.derivedQCohProperty K` and the corresponding
  `K'`, `hK'` say that the two objects have quasi-coherent cohomology in every integer
  degree, using the recorded module equivalence and `IsQuasicoherent` predicate.
- `φ : (spaceDerivedPullback g').obj K ⟶ K'` is the specified arbitrary coefficient
  map, without assuming that it is invertible.
- `h_stalk : SingleComplex.StalkCondition f f' g g' sq K K' φ` is the existing exact
  geometric-stalk condition. Its `R`, `leftAlgebra`, `rightAlgebra`, and `tensorMap`
  give R=O_Y,y, A=O_X,x, B=O_Y',y', and the projection-induced D=A tensor_R B to C.
  `stalkModel` constructs actual colimits over pointed affine etale neighbourhoods;
  affine neighbourhoods are a cofinal basis of the pointed etale scheme site.
  `cohomologyModel` uses the canonical base-derived tensor cohomology model and
  its D-action. `comparison` then applies the normalized pullback-stalk isomorphism
  and the stalk of the coefficient map, exactly giving beta after C-linear extension.
  `StalkCondition` quantifies over all algebraically closed fields in the big-site
  universe, all their geometric points and all `i : ℤ`. It also quantifies over
  flat-term K-flat coordinates of φ; their counit equation fixes the same canonical
  arrow, and `coordinates_nonempty` ensures this is not a vacuous condition.
- The conclusion is `IsIso` of `moduleDerivedExchange ... sq.w K ≫
  (derivedDirectImage f').map φ`. The first map is the existing exchange under
  L(f')* ⊣ Rf'_*, whose transpose is the normalized pullback-square isomorphism
  followed by L(g')* of the counit for f. The second map is exactly Rf'_*(φ).
  This is invertibility in D(O_Y'), not merely isomorphic individual cohomology
  objects or the existence of an unspecified isomorphism. All functors are their
  fixed K-flat/K-injective total derived functors. No Tor-independence, properness,
  flatness, or boundedness hypothesis has been introduced.

Recorded declarations used (full signatures and docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, and localization `Q`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `EtaleSite`, `structureSheaf`, `Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, using
  `SheafOfModules.IsQuasicoherent` and the existing slice instances.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `ModuleDirectImageModel`,
  `moduleDirectImage`, `moduleTensorPullback`, and `moduleTensorAdjunction`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `derivedQCohProperty`, `smallModuleDirectImage`, `derivedDirectImage`.
- `Sheaf.AlgebraicGeometry.SpaceDerivedPullback`: `spaceDerivedPullback` and its
  tensor-normalized composition comparisons.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSingleComplexStalkCondition`:
  `SingleComplex.StalkCondition` and the ring/stalk/comparison declarations above.
  Its `SingleComplex.derivedPullback` abbreviation and `spaceDerivedPullback` both
  reduce to `derivedTensorPullback.{u,w,w}`; there is no transport of φ to a different map.
- `Sheaf.AlgebraicGeometry.SpaceModuleDerivedExchange`: `moduleDerivedExchange`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact`, specialized also
  to the relative diagonal; no curve-family assumptions are used.

The size-convention node is explicitly a convention, not a declaration to import.
The public imports expose the statement dependencies. Recorded proof modules are
plain imports: `SpaceDerivedEtaleChartCalculus`, `AlgebraicSpaceFibreProductsEtaleCovers`,
`SpaceQcqsDistinguishedSquareInduction`, `DerivedEtaleZariskiEquivalence`, and upstream
`WeilConjectures.AlgebraicGeometry.SingleComplexQcqsInduction`; the triangle
isomorphism leaf is `Mathlib.CategoryTheory.Triangulated.Pretriangulated`.
The stalk-chart and relative-MV proof nodes have no Lean attachment, so their imports
are deferred; no statement dependency is missing. There is no import of the downstream
`SpaceFlatComplexBaseChange`, which uses this theorem in its proof plan.

Edge cases checked against the statement and definitions: K=K'=0; empty X or X'
(the geometric-point quantifier may then be empty, as it should); g and g' identities
with φ the identity; an arbitrary noninvertible φ satisfying the stalk comparison;
all four spaces representable by schemes; arbitrary unbounded degrees, arbitrary
characteristic, and non-Tor-independent squares. The latter are allowed: the hypothesis
is the specified cohomological comparison, not flatness of the square or invertibility
of the bare derived pullback coefficient comparison. No mathematical fault was found.

Searches performed on 2026-10-24 with the prescribed `msearch.py` wrapper:

- LeanFinder: `Geometric stalk single complex base change for quasi compact quasi
  separated morphisms of algebraic spaces`. Eight hits on scheme stalk maps and
  spreading out; none is this theorem.
- Loogle: `IsIso, DerivedCategory`. No hits; service reports unknown identifier
  `IsIso`. This unsuccessful query is recorded without claiming a positive search.
- Mathlib grep: `singleComplex|StalkCondition|AlgebraicSpace`, subdirectory
  `AlgebraicGeometry`. Zero hits.
- LeanSearch: `single complex derived base change under geometric stalk condition
  for algebraic spaces`. Eight hits on ring-hom stalk surjectivity and stability
  of scheme morphism properties; no derived algebraic-space theorem.
- `rg` of `singleComplex|SingleComplex|baseChangeQcqs|single_complex` in the project
  `lean/WeilConjectures` and `lean/Sheaf/AlgebraicGeometry` found the scheme
  single-complex theorem, scheme criterion, and the already landed geometric stalk
  condition/tensor-inheritance modules. The scheme theorem is not this statement.
  The geometric condition and exchange definitions are reused, not restated.
- `rg` for the exact item id in `lean/WeilConjectures` found no declaration.
  Searches for `SpaceSingleComplexBaseChange|singleComplexBaseChange` in Sheaf found
  no existing algebraic-space theorem. Searches for quasi-compactness and relative
  diagonal found the existing `MapIsQuasiCompact` used by related space modules.

Validation: prescribed `scompile.py Q07 lem-sfb-space-single-complex-base-change`
compiled this file in both sandbox and library module modes successfully. No errors
or warnings were emitted. Every variable and universe is explicitly bound, and
`autoImplicit` is false. The only postponed theorem is the item's theorem.

## Second reading by Q07

Self-review with the node and final module open checked the square orientations,
that quasi-separated means a quasi-compact diagonal rather than a closed diagonal,
that both QCoh hypotheses are present, and that h_stalk concerns the actual coefficient
map and every integer degree. The conclusion uses the existing mate and the image of
that same φ. The common pullback abbreviations reduce to the identical total-derived
functor, confirmed by compilation. The five added statement dependencies are already
landed definition owners; all original dependencies and proof steps are retained.
No correction was needed. This is the dispatcher's single-worker delivery; the
maintainer supplies the independent review, and no independent worker reading is claimed.
