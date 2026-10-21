## Worker report

The module `Sheaf.Paper.EtaleProEtaleScalarCounitTransposes` states
`AlgebraicGeometry.ProEtale.etaleProEtale_scalar_counit_transposes` with proof `sorry`.
It constructs the node's U, V, arbitrary-map counit transpose, and specified common
normal form as four real composites. These are helpers of this node, all listed in
`lean.declarations`; no independent notion or definition node is needed. The node's
statement, dependencies, and seven-step proof plan are unchanged.

Source read: current blueprint main-20261015,
`sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-direct-image.proof.md`,
Formal properties and Finite rings paragraphs. These specify coefficient mates and
their transport through the site comparison. The node supplies the expanded
counit calculation and assumes its mixed-site cube at precisely the indicated object.

Hypothesis and clause correspondence:

- Any schemes X,Y and morphism f: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Any discrete commutative rings and homomorphism a:
  `{A B : Type (u + 1)} [CommRing A] [CommRing B] (a : A →+* B)`.
  The coefficient size is the recorded six-functor convention; smaller coefficients
  can be lifted to this universe. No topology, finiteness or flatness is imposed.
- The ordinary uncompleted unbounded categories are `Etale.DerivedCategoryModule A X`
  and `_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat B))`.
  They are the existing fixed-constant-coefficient module categories, with no
  completion, constructibility restriction, or bounded subcategory.
- C_Z^R is `(comparisonUpperStar (ModuleCat R) Z).mapDerivedCategory`.
  l_R and p_R are `L(Etale.upperStar (ModuleCat R) f)` and
  `L(ProEtale.upperStar (ModuleCat R) f)`; r_R and s_R are the corresponding
  `R(Etale.lowerStar ...)` and `R(ProEtale.lowerStar ...)`.
- The canonical geometric adjunctions, including their actual counits, are
  `Etale.derivedUpperStarLowerStarAdjunction` and
  `ProEtale.derivedUpperStarLowerStarAdjunction`.
- T_Z^e is `Etale.scalarExtension a Z`, which is the existing abbreviation for
  `pbcFixedScalarExtension Z.smallEtaleTopology a`. T_Z^p is
  `pbcFixedScalarExtension (Scheme.ProEt.topology Z) a`. These are ordinary
  derived extension of constant coefficients, adjoint to actual restriction.
- d_R is `directImageComparisonAmbientPullbackIso R f`; its implementation
  localizes the recorded `comparisonUpperStarCompUpperStarIso`, using the
  comparisons between left-derived and exact termwise inverse images.
- c^e is exactly the dependency declaration `Etale.scalarPullbackIso a f`.
  c^p is the existing `scalarPullbackProEtaleIso a f`, the canonical inverse
  scalar-adjunction mate of exact restriction/pullback. delta_Z is the existing
  `pbcComparisonReduction Z a`, the tensor/site comparison obtained from the
  restriction square by scalar adjunction. No arbitrary comparison is supplied.
- beta^R is `directImageComparisonAmbient R f`, whose definition is literally
  `mateEquiv` of d_R under the two geometric adjunctions.
  gamma^e is `Etale.scalarMate a f`, literally the mate of c^e.
  gamma^p is the displayed `mateEquiv ... (TwoSquare.mk ... c^p.hom)` in U.
  Hence their transpose normalizations are the node's, by the existing
  `CategoryTheory.mateEquiv_counit`.
- J is `(J : Etale.DerivedCategoryModule A X)`. P is written out everywhere
  as `R(Etale.lowerStar (ModuleCat A) f).obj J`, with no statement-local `let`.
- `_hCube` is exactly the assumed equality at P. In Lean's left-to-right
  composition order its left side is `c^p ≫ T_X^p.map d_A ≫ delta_X`, and
  its right side is `p_B.map delta_Y ≫ d_B ≫ C_X^B.map c^e`, at the node's
  specified arguments. It is not assumed at every object.
- `scalarSiteDirectImageU` is `T_Y^p.map beta_A ≫ gamma^p ≫ s_B.map delta_X`;
  `scalarSiteDirectImageV` is `delta_Y ≫ C_Y^B.map gamma^e ≫ beta_B`.
- `scalarSiteCounitTranspose a f J q` is `p_B.map q ≫ epsilon^p_B` for ANY
  q with exactly their source and target.
- `scalarSiteCounitNormalForm` is `p_B.map delta_Y ≫ d_B ≫
  C_X^B.map (c^e ≫ T_X^e.map epsilon^e_A)`, including the grouping inside
  C_X^B required by the displayed formula.
- The conclusion is the conjunction `U-flat = normalForm ∧ V-flat = normalForm`.
  This states both requested equalities, including the specified normal form,
  and is equivalent to the node's U-flat = V-flat = that form.
- The explicit return types of the transpose and normal form are morphisms
  `p_B T_Y^p C_Y^A(r_A J) ⟶ C_X^B T_X^e J` in the B-module derived category.
  Thus B-linearity is built into the Hom type, rather than a separate untyped assertion.
- There is no qcqs, boundedness, coefficient-flatness, or invertibility-of-beta
  binder. In particular `directImageComparisonAmbientIso` is never used.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme Hom.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`;
  fixed-coefficient sheaves are the existing encoding of constant-ring modules.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`, reexporting the six-functor
  coefficient module: `AlgebraicGeometry.Etale.DerivedCategoryModule`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection` and its
  `UpperLowerStar` dependency: `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`
  and the canonical `derivedUpperStarLowerStarAdjunction` used to define its counit.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`:
  `AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunction`; despite its
  directory name, the signature permits arbitrary commutative coefficient rings.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: the arbitrary-ring
  intrinsic presentation and its tensor-unit-normalized module adjunction were read;
  the fixed-module presentation already used throughout the comparison framework
  supplies the same ordinary constant-coefficient operations here.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: the actual site adjunction
  `Scheme.proEtaleSiteComparison`; its underlying fixed-module functors are
  `comparisonUpperStar` from the publicly imported upstream comparison framework.
- `Sheaf.Paper.PurEtaleScalarMateProjection`: `Etale.scalarPullbackIso` and
  `Etale.scalarMate`, with the unique K-flat representative normalization.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv` for the adjunction-mate
  definition; `mateEquiv_counit` is also precisely the recorded Mathlib declaration
  of the sole proof dependency `lem-amb-mate-unit-counit`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `nonempty_derivedChangeOfRingsCochainModel`; the constant-coefficient specialization
  is the existing `pbcFixedScalarExtension`, not a fresh arbitrary left adjoint.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`,
  the representative-normalized general tensor/pullback comparison.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`:
  `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons`, the
  normalized monoidal system. The node's cube is a hypothesis, so this theorem
  is not used to replace that hypothesis by an unconditional assertion.
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`:
  `AlgebraicGeometry.ProEtale.directImageComparison`; its pullback square is
  reused on unbounded categories through the existing ambient pullback helper.
- `Sheaf.Paper.EtaleProEtaleScalarMate`: the existing helper implementations
  `scalarPullbackProEtaleIso`, `directImageComparisonAmbientPullbackIso`, and
  `directImageComparisonAmbient` were read with their signatures and docstrings.
  Only these helpers are used, not the downstream scalar-mate theorem.
- `Sheaf.Paper.WitnessCompatibility`: `pbcFixedScalarExtension` and
  `pbcComparisonReduction`, publicly reexported by the preceding module.

Import-cycle bookkeeping: this delivery publicly imports the existing
`EtaleProEtaleScalarMate` module to reuse its canonical helpers without copying
any definition. That module's main theorem is a DAG consumer of this item.
Under stages/2-statements.md section 3.7, the maintainer must omit the reverse
proof import into that module, which would close an import cycle. This item has
no DAG dependency on that downstream theorem and uses none of its conclusions.
The current import graph compiles cleanly. Factoring the already published
helper declarations out of their consumer module would remove that future
proof-import restriction; no published source is modified by this delivery.

Edge cases checked by reading every map's type and construction: identity f,
identity a, zero object J, empty schemes, zero coefficient rings, non-flat B over A,
and objects with arbitrarily negative cohomology. All use the same composites and
canonical adjunctions, with no nonzero, nonempty, lower-bound or inverse-beta
requirement. P and T_Y^e(P) are completely unbounded. The cube is needed only
at P, as asserted. Object universe u+1 and Hom universe u of the sites are
retained by the existing framework; no site universe equality was imposed.

Searches actually run:

- `msearch.py leanfinder`: “The two etale proetale scalar direct image mate composites
  have equal counit transposes with a specified common normal form” returned
  `mateEquiv_counit`, its inverse, iterated mates and unit formulas; none states
  both composites' common normal form under this cube hypothesis.
- `msearch.py loogle`: `CategoryTheory.mateEquiv_counit` returned that exact
  declaration. Reading it shows it handles one mate; additional naturality
  and the mixed-site cube are needed here.
- `msearch.py grep`: `mateEquiv_counit|mateEquiv_vcomp` in `CategoryTheory/Adjunction`
  returned the existing counit and pasting formulas, no item statement.
- `msearch.py leansearch`: “Counit transposes of two composites of site comparison
  and scalar extension mates have the same specified normal form” returned
  generic adjunction/mate and ordinary module-scalar counits, no exact match.
- `rg` in the project's `WeilConjectures/SixFunctors` and `Sheaf/Paper` for scalar,
  counit, transpose and cube terms found the canonical helpers above and the
  downstream theorem. The latter assumes qcqs and boundedness and concludes a
  different cancelled equality, so it is not an existing match for this item.
- `grep -rn` for this node id in `lean/WeilConjectures` found no declaration.
  Searches for all five newly introduced names in Mathlib, `WeilConjectures`,
  and `Sheaf` found no collision.

Validation: `scompile.py NB lem-sfb-etale-proetale-scalar-counit-transposes` passed
both the sandbox and intended-library-module compilation, respectively in
12.7 s and 12.2 s. There were no errors or warnings. The one newly postponed
proof is the named item theorem, with the complete seven-step proof in its
docstring. All four helper definitions have real composite data.

No statement correction, new node, dependency module, or statement dispute.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
