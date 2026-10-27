## Worker report

The item is stated by `AlgebraicGeometry.AlgebraicSpace.relativeJacobian_theta_polarization`
in `Sheaf.AlgebraicGeometry.RelativeJacobianThetaPolarization`. Its only theorem proof is
`sorry`. The support module contains real definitions and a structure with specified data;
it contains no postponed theorem or hollow definition. The original statement and proof
are unchanged. The item gains only its Lean record and the new definition dependency.

The source read was Deligne, *Le lemme de Gabber*, Section 4.1, printed pp.141–142
(primary Numdam PDF, https://www.numdam.org/item/AST_1985__127__131_0.pdf), together with
Milne, *Abelian Varieties*, III Theorem 6.6, Summary 6.11 and Section 8
(https://www.jmilne.org/math/CourseNotes/AV.pdf). Milne's Theorem 6.6 is the theta
isomorphism; the relative assembly follows the item's seven accepted proof steps,
which the theorem docstring records. The source of the relative degree-zero part is
already available: `picardDegree` and `picardDegreeSubfunctor` in the upstream Degree
and DegreeMorphism modules. They are reused, not redefined. The support structure
provides the natural presentation across the existing universe conventions.

Hypotheses and clauses, in order:

* The base scheme of the node is `X.base.left`, denoted S in the paper. The extra
  ambient scheme `R` is the existing stable-family interface's ambient scheme; it
  restricts no family, since a family over S is in particular a family in that
  interface over S with base the identity S-scheme. All schemes are in universe u.
* Locally Noetherian S is `[IsLocallyNoetherian X.base.left]`.
* Genus g at least two and the stable unpointed genus-g family are
  `X : StablePointedModuli R genus 0`. The bound is `X.genus_at_least_two`; stability
  is `X.stable`, and the full geometric arithmetic genus condition is `X.genus`.
  The section index is `Fin 0`, so no section of C/S is assumed. Smoothness is
  `[Smooth X.projection]`. The scheme C is `X.curve`, and its map is `X.projection`.
* The represented degree-zero Picard fppf functor is `J : AlgebraicSpace X.base.left`
  with `e : JacobianTheta.Presentation ... X.projection J (groupSpaceProjection J)`.
  Its `classify` equivalences use all maps from represented schemes over the base
  and exactly the sections of the existing `picardFunctor` with `picardDegree = 0`
  at every point. Its `naturality` uses the actual Picard sheaf restriction.
  This avoids an equality between Type u space-values and Type (u+1) Picard-values.
* The canonical commutative group structure is the existential `gJ`, tied to
  tensor product by `TensorCompatible X.projection J e gJ`. TensorCompatible
  specifies multiplication on every local pair of line-module representatives.
* Proper, smooth, finite presentation and geometrically connected abelian fibres
  are `Poincare.IsAbelianFamily (groupSpaceProjection J)`. Its actual definition is
  `MapIsProper` plus chartwise `Smooth`, local finite presentation and
  `HasAbelianFibres`. Proper includes separatedness, finite type and universal
  closedness; in particular it supplies the quasi-compactness needed for finite
  presentation. `HasAbelianFibres` supplies scheme models with `IsAbelianVariety`,
  which includes properness, smoothness and connectedness. Over algebraically
  closed K these are the geometric fibres, hence geometrically connected fibres.
* An arbitrary dual `D`, its group `gD`, universal line `P` and normalized axes `r`
  are quantified. `IsAbelianFamily D` and `Represents ... P r` say precisely that
  it is a dual abelian space representing the identity-rigidified, geometrically
  algebraically trivial lines. Their existence is the recorded dependency
  `abelianSpace_poincare_calculus`, applied to the abelian-family conclusion.
  The result applies to every such dual, not a private chosen replacement.
* `∃! lam : J ⟶ D` with `IsHom gJ gD lam` and `IsIso lam` is the canonical group
  isomorphism. The conjunction also specifies its theta characterization,
  its arbitrary base change and its curve-isomorphism compatibility.
* `GeometricTheta` quantifies every algebraically closed K and every point
  `t : Spec K ⟶ S`. It provides a field Picard representative `Z`, its group,
  a degree-zero representing equivalence `eZ` with `IsPicardZeroMul`, and a map
  `j : Z ⟶ J`. The all-scheme-test equality with
  `picardFunctorIsoOfIsPullback` pins j to the original presentation e; it does
  not replace the fibre by an unrelated abelian variety.
* For every geometric curve point p, `GeometricTheta` takes a Picard class N
  isomorphic to `p.ker.toModules`, the actual ideal of p. The Hilbert representative
  eH and Abel map a are characterized on every U-valued divisor by the class of
  its dual ideal, tensored with the pullback of `N ^ (genus - 1)`. This is exactly
  `D ↦ O(D - (g-1)p)`. The ideal `a.left.ker` cuts out the scheme-theoretic image,
  not only its set of points. Its invertibility and the isomorphism
  `Ltheta ≅ a.left.ker.toModulesᵛ` pin the line to that effective theta divisor.
* `_hL : Ltheta.IsInvertible` and `Scheme.Modules.IsAmple Z.left Ltheta` are the
  recorded invertibility and absolute ampleness notions. No global line on J is
  asserted, and no global point or theta characteristic is assumed.
* `FibreDifference` identifies the restriction of P under `(j,j ≫ lam)` with the
  existing four-factor `abelianNormalizedDifference Z Ltheta`. Its auxiliary map
  v is specified by both projections to the actual sheaf fibre product, so it
  is the canonical map rather than an arbitrary comparison. This is
  `(lambda_C)_K = phi_L`, including the identity-line normalization. The
  difference represents the class `t_x^*L tensor L^{-1}` on every test.
* Independence of p is the universal quantifier over p in GeometricTheta, with
  the same lam. Independence of translating theta is its final clause for every
  translation `b = lift (id Z) (toUnit Z ≫ x) ≫ mu[Z]`, which requires the same
  `FibreDifference` for `b^*Ltheta` and the same lam.
* `UniversalThetaBaseChange` quantifies every `T : Over S` with locally Noetherian
  source, with no flatness, smoothness, reducedness or finite-type assumption on
  its structure map. It provides the Picard presentation eT and the dual for the
  actual pulled-back spaces and line. `PicardBaseChange` identifies eT with e on
  all scheme tests by the existing canonical Picard base-change isomorphism.
  `IsBaseChangedAxes` retains the literal pulled-back rigidifications. The unique
  lamT is fixed by both projection equations, is an isomorphism, and has the
  geometric theta characterization for the actual curve pullback. Characterizing
  these identifications on all tests and fixing both projections also fixes
  identity and iterated-pullback identifications, rather than leaving a choice
  of arbitrary isomorphisms.
* `CurveIsomorphismNaturality` quantifies all S-isomorphic curves and their
  Picard/dual presentations. `CurveTransport` uses the canonical Picard
  identification for the square with `u.inv`, so a is `(u^{-1})^*`. `Dualizes`
  requires the normalized universal-line pullback comparison, so aDual is
  pullback on rigidified line modules. Its conclusion is
  `a.hom ≫ lam' ≫ aDual = lam`, i.e. the node's equation. The quantification
  includes identities and composites; both transports are characterized on all
  tests by the canonical Picard and universal-line comparisons.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`; its locally
  affine locally ringed space definition supplies the scheme category.
* `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
* `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `AlgebraicGeometry.StablePointedModuli` and its full family fields; the Smooth
  full subcategory uses the same `Smooth X.projection` condition used here.
* `WeilConjectures.AlgebraicGeometry.Picard.Defs`: `picardFunctor`,
  `toPicardFunctor`, `picardFunctorIsoOfIsPullback`, the fppf sheafification and
  the canonical cartesian pullback comparison.
* `WeilConjectures.AlgebraicGeometry.Picard.Degree` / `DegreeMorphism`:
  `picardDegree`, `picardDegreeSubfunctor`; no private degree definition.
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, with its scheme
  tests, representable diagonal and etale atlas; `schemeSpace` is the recorded
  represented-space construction from EnlargedEtaleRingedSite.
* `Sheaf.AlgebraicGeometry.AbelianSpacePoincareCalculus`:
  `abelianSpace_poincare_calculus`, and its owning
  `Sheaf.AlgebraicGeometry.AbelianSpacePoincareData`: `Pointed`, `pointedGroup`,
  `IsAbelianFamily`, `HasAbelianFibres`, `Axes`, `Represents`, `IsHom`, `Dualizes`,
  `IsBaseChangedAxes`, `product` and the canonical pullback/projection constructions.
* `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`; `WeilConjectures.AlgebraicGeometry.Ample`:
  `Scheme.Modules.IsAmple`, with its quasi-compactness and affine nonvanishing loci.
* `Sheaf.AlgebraicGeometry.AbelianVariety.DualPoincareDatum`:
  `abelianNormalizedDifference`, used literally for the fibre equation.
* `WeilConjectures.AlgebraicGeometry.Picard.Jacobian`:
  `picardFunctorDegree`, `picardSubfunctorDegree`, `picardFunctorDegreeι`,
  `IsPicardZeroMul` for geometric field models only. The relative definition is
  the actual degree-zero subset of picardFunctor, not this field-only functor.
* `WeilConjectures.AlgebraicGeometry.Hilbert.Defs`: `hilbertPresheaf`; scheme
  ideal data, `Scheme.Hom.ker` and the existing scheme module dual give theta's
  actual Cartier image line.

Proof imports are the published modules of the listed proof dependencies:
ConnectedProperFibresProper, SymmetricAbelImageGeometry, AbelianVariety.PolarizationCalculus,
AlgebraicSpaceUniversalIsomorphismOpen, Picard.Jacobian and Picard.Degree, together with
AbelianSpacePoincareCalculus. The proof nodes nodal-picard-etale-schematic,
relative-degree-gminusone-theta, theta-poincare-pullback and equal-dimension-abelian-retract
have no recorded module in the read base, so none is invented as a proof import.

Edge cases checked: empty base (all geometric assertions are vacuous and the unique map
between empty pullbacks is retained); the empty marking set `Fin 0`; genus two, where the
Abel degree is one; arbitrary characteristic, especially two (no division by two);
nonreduced bases and test schemes (all functorial comparisons use scheme tests, not
geometric-point equality); disconnected bases (degree is zero at every point, not one
chosen component); arbitrary locally Noetherian base maps, including identities and
successive maps. No restriction equating Picard-value and space-value universes is used.

Searches actually run:

* msearch leanfinder, `Relative Jacobian theta polarization isomorphism dual abelian space`:
  eight unrelated root-pairing and number-field polarization hits; no match.
* msearch loogle, `"Picard", "theta"`: zero hits.
* msearch grep, `Poincare|polarization|autodual|[Tt]heta`, Mathlib/AlgebraicGeometry:
  zero hits.
* msearch leansearch, `The Jacobian of a smooth proper curve has a canonical theta principal
  polarization compatible with base change`: eight Weierstrass coordinate/base-change,
  quadratic form and algebra presentation hits; no match.
* For the new definition node, both leansearch and leanfinder with
  `Relative degree zero Picard functor natural representation and geometric theta divisor
  Abel image`: eight hits each, in ring Picard groups, derived functors and Weierstrass
  point classes; none gives the required natural relative presentation or theta condition.
* msearch grep, `picardDegreeSubfunctor|ThetaPolarization|GeometricTheta`,
  Mathlib/AlgebraicGeometry: zero hits. Project rg located the upstream degree subfunctor,
  the field degree functor and the normalized difference, all reused here.
* rg of WeilConjectures by item id found no declaration. rg of WeilConjectures and Sheaf
  for Jacobian/theta/presentation names found no exact theorem or support interface.
  dag/lean_names_upstream.json has no JacobianTheta or new helper name.
* DAG and blueprint searches for Picard/theta and relative/Jacobian found the field
  Jacobian nodes and Picard-degree nodes but no relative theta presentation interface.
  `blueprint_refs.py ancestor` returns None for this item's existing ancestry; the new
  node preserves that result and prefixes the existing via chain with this item.

No statement correction and no STATEMENT-DISPUTED claim is made.

## New nodes

`def-sfb-relative-jacobian-theta-data` owns RelativeJacobianThetaData and its ten declarations:
`test`, `testProjection`, `Presentation`, `TensorCompatible`, `FibreDifference`,
`GeometricTheta`, `PicardBaseChange`, `UniversalThetaBaseChange`, `CurveTransport`,
`CurveIsomorphismNaturality`. These are the scheme-test presentations and canonical
compatibility conditions needed to state the item. The field functor cannot be used for a
relative base, and equating its size with the existing algebraic-space value size would
restrict the theorem. Existing picardFunctor, picardDegree, degree subfunctors over fields,
Hilbert functor, actual ideal/dual/ample constructions and Poincare data are all reused.
The new node asserts no existence and no theorem. Its source is the same relative Picard
and geometric theta construction in Milne III Sections 6 and 8 and Deligne 4.1. The three
logged kinds of searches and the project/DAG searches above found no duplicate.

## Second reading by Q135

This is the worker's second reading, not an independent review; the maintainer's review
is independent as specified in the assignment. I reopened the node, the dependency
signatures and both delivered files. The genus bound and unpointed condition are retained
in X; smoothness and locally Noetherian base are explicit; the presentation is the exact
relative Picard degree-zero subfunctor. The first conclusion uses the existing full
abelian-family predicate, not just field smoothness. The dual is arbitrary representing
data, and the result is an isomorphism and homomorphism with a fixed theta normalization.
The theta field model is tied on all tests to e, every p is included, the Abel image is
scheme-theoretic via its kernel ideal, and every translate has the same difference map.
The base-change line is literally the pullback of P with matching axes. Picard and curve
transports are pinned by canonical pullback, and the curve equation has the correct
contravariant order `a ≫ lam' ≫ aDual = lam`.

The first compiler reading caught an ambiguous base inferred from the ambient stable-family
scheme R; the final theorem explicitly supplies B as the identity scheme over X.base.left.
The support file also needed the fully qualified scheme `Limits.pullback` (the space
module has an etale restriction called pullback). These were elaboration repairs, not
changes to the informal statement. An implicitly used existential group binder was renamed
`_zGroup` to remove the unused-name warning. No other warning is retained. A final second reading also made the comparison dual
and its source explicitly abelian families, and required its candidate polarization
to be a homomorphism. These conditions are part of "such families" and their dual
polarizations in the node; they avoid quantifying the comparison equation over
unrelated group laws or non-abelian targets. The initial dry run passed before this
clarification; the final dry run recompiles and checks the clarified version.
