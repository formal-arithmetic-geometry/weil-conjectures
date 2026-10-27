## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceInverseModuleAffineBaseChange` states
`AlgebraicGeometry.AlgebraicSpace.inverseModuleAffineBaseChange`. It states the exact
projection-induced derived base-change isomorphism on all qcqs etale scheme charts,
its chart restriction square, and its transition square. All theorems have `sorry`
proofs. Definitions contain actual composites of previously recorded canonical maps.
There is no statement correction, disputed assertion, new definition node, or dependency
repair. The item's `stmt_deps` additionally names already-recorded constructions used
in its canonical maps: affine Hom/sections comparison, the derived module calculus,
derived pullback, ordinary derived scalar extension, the D_QCoh triangulation, and
derived limit triangles. These are existing interfaces,
not copies of their notions.

The source was read in `literature/stacks-project/spaces-flat.tex`: the situation of
existence and Tags 0CX5, 0CX6, 0CX8 (especially `lemma-compute-over-affine`). The current
blueprint unit `_section.md` under `literature/blueprint/latest/blueprint/
sec-six-functors-basics/sk-thm-sf-ctf-stability/` was also consulted. The source really
allows every qcqs etale chart, not merely affine charts despite the lemma label.

Hypothesis-by-hypothesis rendering:

- Schemes and spaces over Spec Z: `X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))`.
  `u` is the scheme and coefficient universe, `w` is the common localization universe.
  The two quantified `HasDerivedCategory.{w}` instances fix localizations for all
  relevant spaces and coefficient rings. They are categorical size/construction data,
  not geometric restrictions; site morphism/coefficient universes are not collapsed.
- The inverse sequence indexed by positive integers: `A : ℕ → CommRingCat.{u}` and
  `r : ∀ n, A (n+1) ⟶ A n`. Code index `n` is paper level `n+1`; no first level is lost.
- Surjective transitions: `hsurj : ∀ n, Function.Surjective (r n)`.
- Locally nilpotent kernels: `hnil : ∀ n a, (r n) a = 0 → IsNilpotent a`. This is
  elementwise nilpotence, without a uniform exponent or nilpotent-ideal assumption.
- The actual inverse limit A: `c : Cone (Functor.ofOpSequence r)` and `hc : IsLimit c`.
  Its vertex `c.pt` is the base ring, and `c.π.app (op n)` is its specified projection.
- The map X to Spec A: `f : X ⟶ schemeSpace (inverseModuleSpec c.pt)`.
- Separatedness: `hsep : MapIsSeparated f` (representably closed relative diagonal).
- Finite presentation: `hfp : ProperQuotFinitePresentation f`, expanding to chartwise
  local finite presentation, quasi-compactness, and quasi-compactness of the diagonal.
- Actual infinitesimal fibres X_n: `properQuotFibre f (inverseModuleTest c n)`.
  These are the existing sheaf fibre products, with `properQuotFst` and `properQuotSnd`.
- The modules: `M : ∀ n, (properQuotFibre f (inverseModuleTest c n)).Modules` on the
  small etale structure-ring sites. `hqc` uses `SheafOfModules.IsQuasicoherent`;
  `hfin` uses `SheafOfModules.IsFinitePresentation`, namely local finite free
  presentations of the prescribed ranks.
- Flatness over A_n: `hflat` tests the recorded scheme `Modules.IsFlatOver` after
  `schemeRestriction` on every etale chart, through its actual map to Spec A_n.
  For quasi-coherent modules this is exactly the equivalent stalkwise condition.
- Proper support: `hsupp` explicitly gives a space Z, a representable closed immersion
  `i`, proper composite `i ≫ properQuotSnd ...`, and a quasi-coherent finite type G
  with `Nonempty ((moduleDirectImage i).obj G ≅ M n)`. No properness of all of X is added.
- Specified ordinary reductions: `e n` is the isomorphism from the existing tensor
  pullback along `properQuotFibreMap f (inverseModuleTestMap c n)` to `M n`.
  This is the O-module form of tensoring over A_(n+1) with A_n.
- Direct images in degree zero: `inverseModuleDerivedTerm` is the recorded single
  complex of the direct image to X, transported by the fixed small-model equivalence.
- D_QCoh and product triangle: `hq` certifies the already-recorded pushed terms as
  quasi-coherent; `HasProduct` supplies their product in `X.DerivedQCoh`. Then `K`,
  `p`, `δ`, and `hK : IsDerivedLimitTriangle ... K p δ` specify precisely the triangle
  in the question. Existence of hq and such a triangle is the stated dependency
  `inverseModuleDerivedLimit`; the theorem is valid for every such presentation.
  The transitions in hK are `inverseModuleDerivedTransition`, using the specified e.

Clause-by-clause rendering and construction of the canonical map:

- `inverseModuleLimitProjections c f M hq K p n` is exactly inclusion of `p ≫ Pi.π _ n`
  in the ambient derived category, hence is q_n of the supplied triangle.
- `inverseModuleSingleDerivedImage` is the canonical arrow from `(j_*M)[0]` to
  `Rj_*(M[0])`. It uses the actual equivalence unit and the right-derived complex unit.
  It makes no arbitrary choice of an isomorphism or lift.
- `inverseModuleProjectionAdjunct` composes q_n with that arrow and transposes under
  the existing normalized geometric derived adjunction. It is `Lj_n^* K → M_n[0]`.
- `inverseModuleChartArrow U` is U's own map to X. `inverseModuleChartFibre j U` is
  the actual sheaf fibre product Y times_X U. For Y=X_n this is U_n, represented by
  the scheme base change of U. Using the existing algebraic-space representation
  retains this same object and all its projection maps, without choosing a new model.
- `inverseModuleLocalSections f v` is `Lv^*` followed by the existing canonical
  affine-base derived sections. For etale v it computes RΓ(U,K). For the etale
  projection U_n to X_n its value on M_n[0] computes RΓ(U_n,M_n|U_n); derived etale
  pullback is the exact ordinary restriction, by the recorded chart calculus.
- `inverseModuleChartProjection` pulls sections through the actual geometric unit,
  the normalized section compositor, the canonical derived cartesian-square
  compositor, and the just-described projection adjunct. Its target retains the
  A_n-action via actual restriction of scalars. `inverseModuleAffineRingMap`
  transports only the ΓSpecIso equality, identifying the scalar map with c.π_n.
- `inverseModuleChartBaseChange` takes exactly that arrow's scalar adjunct under
  `Adjunction.ofIsRightAdjoint (moduleDerivedRestriction φ.hom)`. Thus its source
  is RΓ(U,K) tensor_A^L A_n and its target is RΓ(U_n,M_n|U_n). The selected extension
  is the existing `moduleDerivedExtension`, fixed by its adjunction to exact
  restriction. It is not a second definition of ordinary derived tensor.
- The first conjunct quantifies over every `n`, every `U : X.EtaleSite`, and the
  predicates `CompactSpace U.obj.left.left` and `QuasiSeparatedSpace U.obj.left.left`.
  It asserts `IsIso (inverseModuleLevelBaseChange ... n U)`, the specific map above.
- The second conjunct states the actual square in D(A_n), for every arrow `a : V ⟶ U`
  between qcqs charts: scalar extension of `inverseModuleSourceRestriction` followed
  by beta_V equals beta_U followed by `inverseModuleTargetRestriction`. Both
  restrictions are the canonical geometric-unit/sections comparisons; the target
  fibre map is the actual pullback map induced by a.
- The third conjunct is the level-transition square before scalar adjunction:
  alpha_(n+1) followed by restricted `inverseModuleTargetTransition` and the canonical
  exact-restriction compositor equals alpha_n. The target transition uses
  `inverseModuleDerivedReduction` applied to exactly e_n, on actual chart fibres.
  The compositor uses `ModuleCat.restrictScalarsComp'` with the actual ring-cone
  equation. Naturality and the two scalar Hom equivalences identify this equation
  with the requested square after derived tensor, with its canonical tensor
  associator. This formulation retains coefficient linearity, all maps, and the
  specified e_n; it does not replace compatibility by an existence of isomorphisms.

The helpers whose proofs are postponed are normalization/commutativity obligations of
these same canonical maps: Γ-Spec identification, identity-base restriction square,
chart pullback square, its affine-base square, the infinitesimal fibre square, chart
restriction projection and chart-arrow equations, the ring cone equation, and chart
transition projection/coefficient equations. Each is a named theorem in the owning
node's module, appears in `lean.declarations`, and has a source and complete elementary
proof docstring. No extra mathematical hypothesis, existence choice, or undetermined
comparison is used to define the maps.

Dependency declarations read and used (all imported through their recorded modules):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`. `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `HasDerivedCategory`, `DerivedCategory`, `DerivedCategory.Q`, `singleFunctor`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsEtale`, `EtaleSite`, `structureSheaf`, `Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, including its universal property.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, using the
  original `SheafOfModules.IsQuasicoherent`, not a private predicate.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `ModuleDirectImageModel`,
  `moduleDirectImage`, `moduleTensorPullback`, `moduleTensorAdjunction`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver`, with its affine-local/stalkwise equivalence convention.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsSeparated`,
  `MapIsLocallyOfFinitePresentation`, `MapIsProper`.
- `Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor`: `ProperQuotFinitePresentation`,
  `properQuotFibre`, its projections and `properQuotFibreMap`.
- `Sheaf.AlgebraicGeometry.SpaceInverseModuleDerivedLimit`: `inverseModuleSpec`,
  `inverseModuleSpecMap`, `inverseModuleTest`, `inverseModuleTestMap`,
  `inverseModuleDerivedTerm`, `inverseModuleQCohTerm`, `inverseModuleDerivedTransition`,
  `inverseModuleDerivedLimit`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `derivedQCohProperty`, `DerivedQCoh`, `smallModuleDirectImage`, `derivedDirectImage`.
- `Sheaf.AlgebraicGeometry.SpaceDerivedPullback`: `spaceDerivedPullback`, its universal
  counit, `spaceDerivedPullbackComp` and the underlying `smallModuleTensorPullback`.
- `Sheaf.AlgebraicGeometry.SpaceAffineHomComparison`: `spaceAffineDerivedSections`,
  `spaceAffineRingMap`, `spaceDerivedAdjunction`, `spaceDerivedSectionsComposition`,
  `spaceRightDerivedComplexUnit`; these retain their ordinary-unit/section formulas.
- The two pullback-square comparisons are the inline composite
  `(spaceDerivedPullbackComp f h).symm ≪≫ eqToIso (congrArg spaceDerivedPullback sq)
  ≪≫ spaceDerivedPullbackComp g f'`, using only the already-cited definition node
  `def-sfb-space-derived-pullback`. No declaration from the theorem module
  `SpaceDerivedEtaleChartCalculus` is used or imported.
- `Sheaf.AlgebraicGeometry.RingDerivedScalarExtension`: `moduleDerivedRestriction`,
  `moduleDerivedExtension`, and its right-adjoint instance.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQCohTriangulated`: inherited triangulation;
  `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`: `IsDerivedLimitTriangle`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `mapDerivedCategoryNatIso`, `mapDerivedCategoryCompIso`, `mapDerivedCategoryIdIso`;
  Mathlib supplies `mapCochainComplexSingleFunctor` and restriction composition.

All recorded proof-dependency modules are imported, including ordinary derived change
of rings, the coefficient adjunction, preservation of sequential homotopy colimits,
affine module higher-image vanishing and unbounded Leray. The derived chart calculus
remains a proof dependency in the DAG; its direct import is omitted as expressly
requested in the H2 return because its plain pullback-square definition has been inlined.
The Mathlib leaf `Adjunction.leftAdjoint_preservesColimits` is available through its
adjunction/limits import closure. Three proof-only nodes have no recorded Lean yet:
closed-immersion quasi-coherent modules, the perfect telescope, and perfect-test
reduction. Their proofs are named in the theorem docstring; their absence does not
prevent stating this item and adds no hypothesis to its signature.

Edge cases checked before writing and on rereading: n=0 is exactly paper n=1;
identity transitions and constant systems are included; zero rings, zero modules,
empty spaces and empty charts are admitted; charts need not be affine or surjective;
no uniform nilpotence exponent, Noetherianity, properness of X, or flatness of A→A_n
is imposed. Products are in the full D_QCoh subcategory, not ambient sheaf-derived
products or the derived category of QCoh. Every triangle presentation and its actual
projections are retained. Universes and implicit variables are explicitly bound,
`autoImplicit` and `relaxedAutoImplicit` are disabled, and no let/show binder occurs
in the theorem statement.

Searches for an exact existing statement:

- `msearch.py ... leanfinder "Derived sections of the homotopy inverse limit of flat
  proper support modules commute with nilpotent base ring reduction on etale charts"`:
  eight etale algebra/infinitesimal-lifting results; no derived limit comparison.
- `msearch.py ... leansearch "derived scalar extension commutes with homotopy limits
  infinitesimal modules"`: eight ordinary scalar restriction/extension results, such
  as preservation of limits by restriction and extension under flatness. No match.
- `msearch.py ... loogle "ModuleCat.ordinaryDerivedExtendScalars,
  Functor.rightDerivedFunctor"`: zero matches; unknown project-specific identifier.
- `msearch.py ... grep "inverseModule.*BaseChange|derived.*[Ss]ections"
  AlgebraicGeometry`: zero matches in Mathlib. Direct rg for the node id and
  `inverseModule.*[Bb]aseChange` in both `lean/WeilConjectures` and `lean/Sheaf` found
  no existing statement. Broader derived-section/chart searches located the existing
  canonical sections and scalar interfaces used here. No notion is duplicated.

Validation: the entire module compiled through the prescribed server `scompile.py`
in sandbox mode and at its final library name, with no errors or warnings (8.0 and
7.8 seconds on the first complete run). All subsequent final changes are checked
by the delivery dry run as well.

## Second reading by Q50

This is the worker's explicit second pass over the node and the complete Lean file;
the dispatch brief prohibits starting another agent. The maintainer's independent
review remains the independent reading of this delivery. This section does not claim
that a second worker reviewed the file.

The rereading matched every hypothesis and all three conclusions as detailed above.
In particular it checked the direction of geometric and coefficient adjunctions, the
ordinary-to-derived direct-image arrow, the direction of the cartesian-square inverse,
the Spec contravariance, first-level indexing, use of the supplied triangle projection,
and use of e_n in the level transition. It checked that the final equation is equality
of the scalar preadjoints, hence is equivalent to tensor-transition compatibility,
not a new arbitrary relation. An initial pullback.map coherence equation was reversed;
it was corrected to the symmetric first-projection equation and the module recompiled.
The final file has no unbound variables, no data sorry, no local instances/notations,
and no substitute functor or arbitrary comparison hypothesis. No source-statement
mismatch or correction remains.


## Repair of returned head 80304df37cbe

H2: followed correction (b). In `inverseModuleChartProjection` and
`inverseModuleLocalPull`, replaced `spaceDerivedChartPullbackSquare` by its exact
three-isomorphism composite of `spaceDerivedPullbackComp`, `eqToIso` on the given
commuting-square equality, and `spaceDerivedPullbackComp`. Removed
`lem-sfb-space-derived-etale-chart-calculus` from `stmt_deps` and replaced the
`SpaceDerivedEtaleChartCalculus` import by the already-cited definition module
`SpaceDerivedPullback`. The theorem remains in `proof_deps` as the original proof
plan requires. The main theorem signature, all hypotheses, all three conclusions,
all declarations and all proof placeholders are unchanged. This is a substantive
source repair of both offending uses, not an unchanged re-push. Compared the sandbox
node against the current shared-main node: outside `lean` and the authorized added
statement dependencies, all fields agree. The delivery wrapper rebases onto the
current shared-main base.

Repair second pass: read the source definition at live
`SpaceDerivedEtaleChartCalculus.lean:158` and the compositor signature in
`SpaceDerivedPullback.lean`. Both inlined expressions have exactly the same order
and inverse as that definition. Checked that no occurrence of the removed helper
or theorem-module import remains in the Lean source, and that the removed dependency
is absent from `stmt_deps` while remaining in its original proof uses.

Repair validation: `scompile.py Q50 lem-sfb-space-inverse-module-affine-base-change`
compiled the repaired file both as `Sheaf.Stage2.Sandbox0` and at its final library
module name with exit code 0 and no compiler errors or warnings. The compiler wrapper
reported 60.7 seconds and 36.9 seconds respectively under its prescribed limits.
