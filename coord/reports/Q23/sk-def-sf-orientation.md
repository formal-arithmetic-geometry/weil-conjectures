## Worker report

This delivery defines `WeilConjectures.SixFunctorOrientation` in
`Sheaf.Paper.SixFunctorOrientation`: evaluation of a full coherent orientation
datum at a smooth separated finite-type morphism. Integral, rational and
common-stage evaluations, and the reverse structure-morphism isomorphisms at all
four stages, are public declarations in the same module. The unit statement is
unchanged. No existence theorem for an orientation is assumed or asserted.

The source read is the current
`literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-def-sf-orientation/`
unit and its `def-sf-orientation.md` child. I also read the three statement
dependencies and their recorded declarations, including the current server
version of the old orientation module with `scompile.py --source`.

The hypothesis and clause correspondence is as follows.

- The fixed finite field, its algebraic closure, the prime distinct from its
  characteristic, and coefficient extension are `D : FiniteFieldDatum`,
  `C : D.CoefficientDatum`, `E`, its field/algebra/finite-dimensional instances,
  and the supplied `S : SixFunctorDatum`. `SixFunctorSpace D` is the actual full
  subcategory of finite-type schemes over `Spec D.k`; no separatedness condition
  is imposed on its objects. The morphism binder is `f : X ⟶ Y`.
- A positive finite quotient index is written `m + 1`. This covers every `n ≥ 1`,
  including the first, ramified quotient, without choosing a smaller class of
  coefficient extensions. There is no equality imposed between site object and
  morphism universes. The coefficient modules have the prescribed `u + 1` carrier
  universe on the actual small pro-etale and etale sites.
- Smoothness of pure nonnegative dimension is exactly
  `[SmoothOfRelativeDimension d f.hom.left]`, with `d : ℕ`;
  `[IsSeparated f.hom.left]` is the separatedness hypothesis. Compactifications
  are coordinates for the already supplied operations, and the `compactification`
  fields make evaluation independent of these coordinates. Auxiliary
  compactifiability, quasi-compactness and Noetherian instances in the etale
  formulas are the properties of these finite-type schemes and separated
  finite-type maps, not additional geometric restrictions.
- The coefficient/twist object is the actual root line. The complex
  `sfOrientationIntegralComplex` is a single complex in degree `-2*d`, hence
  `Lambda(d)[2d]`; `sfOrientationIntegralShiftIso` gives the canonical comparison
  with the dependency's existing `sfIntegralTwistingObject` and shift. Its
  integral membership theorem asserts uniform finite Tor amplitude as well as
  completed constructibility. Finite lines are the actual
  `sixFunctorIntegralReduction` of this object, with the uniquely normalized
  quotient comparison to the existing finite root line. Rational lines are its
  image under the existing raw localization. Common-stage lines are represented
  at the least finite coefficient field, with explicit comparison from every
  other field. No Karoubi completion or replacement coefficient category appears.
- The displayed gamma is the `component` iso of the relevant family. Its source
  is written in the coefficient-unit/pullback coordinates `T X d`, as explicitly
  permitted by the detailed definition. The native iso is in the existing
  bounded-constructible category. Its source is finite Tor, so the iso also
  represents an iso of the full finite-Tor subcategory; no finite-Tor assumption
  on the exceptional image is added to define a component.
- A component is evaluated from `O : SfOrientationDatum S`, never from an isolated
  unnormalized iso. The full record retains the higher family at `E`, the higher
  family at every finite coefficient field, the common-stage family, every
  positive finite quotient, and the primary finite stage of the supplied datum.
- Base naturality and etale base change are `SfGeometricOrientation.baseChange`
  and `SfFiniteEtaleOrientation.baseChange`. The former uses
  `sfOrientationBeta`, literally the adjoint transpose of inverse compact-support
  exchange, the pulled-back counit and the pullback-unit comparison. The latter
  uses the published `Etale.dualizingComplexBaseChangeMap`. The square's base map
  is separated finite type, with neither properness nor smoothness imposed.
- Composition is the `composition` equation in these same records. The generic
  formula uses `sfOrientationTheta`, the transpose of inverse projection followed
  by counit tensor identity and the coefficient unitor, and
  `sixFunctorExceptionalComposition`, the mate of support composition. The
  formula is written with omega first; the first inverse twist-product map and
  tensor symmetry give exactly the source's pullback-first formula. The finite
  etale formula uses `Etale.dualizingComplexTensorMap` and
  `PurityFiniteSetting.finiteExceptionalComposition`, the actual same mates.
  Comparison coordinates are normalized by equality/HEq to the supplied A2/A3
  maps; smooth-purity isomorphisms are not arbitrary comparison parameters.
- Coefficient compatibility is
  `SfOrientationCoefficientCompatible`, whose equation is literally
  `C.map gamma ≫ w ≫ f!.map(t_unit) = t ≫ gamma'`.
  `SfHigherOrientation.rationalization`, the higher family's
  `scalarCompatibility` using `SfStageOrientationCompatible`, the full datum's `commonCompatibility`, and the two
  `finiteCompatibility` fields impose it at their supplied domains. The finite
  presentation retains all integral reductions together. Since the actual
  quotient maps on all root powers and the A5 support maps are used, applying a
  smaller quotient to these equations gives finite-to-finite reduction
  compatibility. No field-to-finite reduction is introduced. Field transitions
  and common-stage comparisons use the actual coefficient inclusion, including
  identity and composite inclusions, rather than an arbitrary line iso.
- The finite `etale` field retains companions for every exponent killing the
  coefficient ring. `realization` compares them to the native finite components.
  `sfOrientationFiniteSiteLine` is the tensor-power root comparison from
  `finite_tate_site_descent`, with its root/scalar normalization retained, the
  actual intrinsic realization equivalence and the canonical quotient comparison.
  `sfOrientationFiniteOmegaRealization` is the image of the actual unit of
  `derivedComparisonAdjunction` under `nu* f^times`, followed by its coefficient
  unit comparison and the specified finite-exceptional realization. Thus its
  `w_nu` is not an arbitrary iso. Checking finite geometry through the ordinary
  etale family is an equivalent presentation: the comparison unit is invertible
  on these bounded torsion objects, the intrinsic realization is an equivalence,
  and the prescribed support, open, tensor and pullback comparisons identify the
  displayed equations. `primaryEtale` identifies the primary finite stage's
  companions with the same quotient family's companions.
- Affine-line normalization is `SfFiniteEtaleOrientation.affineLine`.
  `sfOrientationAffineTrace` first compares the chosen compactification with the
  standard `affineTraceLineCompactification`, applies `Rq_*` to the open counit
  with the root-normalized pullback of the shifted line, and then applies
  `Etale.projectiveLineTrace`. This is the required integration map; the field
  says it is the counit transpose of gamma. No separatedness of the Noetherian
  base is imposed. The realization equation transports this exact integration
  to the pro-etale trace of the source; integral normalization is its system of
  finite reductions, and rational/common normalization is their scalar image.
- At a smooth separated structure morphism `sixFunctorStructure X`, the four
  `*Structure` definitions are precisely the corresponding component `.symm`.
  Thus omega is identified with `Lambda_X(d)[2d]`, without an extra duality or
  existence assertion.

Dependency declarations used include:

- `Sheaf.Paper.SixFunctorDatum`: `SixFunctorDatum`, its actual operation stages,
  coefficient comparisons, support adjunctions, A2/A3 exchange data and
  `sixFunctorExceptionalComposition`.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`:
  `sfIntegralTwistingObject`, `sfIntegralTwistingCoefficient`,
  `sfRationalTwistingFunctor`, `sfQbarTwistingFunctor`, and the publicly imported
  signed powers and exact integral/finite twisting functors. This recorded
  dependency remains unchanged. Its resolved maintenance repair note was read;
  this delivery uses its actual functors and does not restore the withdrawn
  object-only interface.
- `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical`: the existing positive line,
  all local root-tensor generators, ordinary module inverse image and its
  augmentation. Only the missing arbitrary-base-map normalization is supplied.
- `Sheaf.Paper.IntegralAmbientOperationModels` and
  `Sheaf.Paper.PuritySourceTransports`: the actual completed tensor/pullback,
  completion/scalar augmentations and ordinary root-normalized scalar maps.
- `Sheaf.Paper.FiniteTateSiteDescent`: `finite_tate_site_descent`, whose predicate
  fixes every comparison on roots and coefficients. Its existence is not used
  as a choice of an unnormalized map.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `sfIntrinsicDerivedEquivalence` and `sfIntrinsicRealizationUnit`;
  `ProEtale.sfFiniteExceptionalFixed` and the supplied `finiteExceptional`
  comparisons are the existing exceptional-image models.
- The published etale canonical maps, finite exceptional composition, ordinary
  root-line pullback/product, standard projective compactification, open counit,
  and projective-line trace are used directly.

Edge cases read against the definitions: `d=0`, identity morphisms and dimension
zero composition; empty schemes; `m=0` (quotient exponent one), including ramified
`E`; all killing root exponents and changes of exponent; even shifts with the
correct sign `-2*d`; arbitrary separated finite-type base change; a nonseparated
Noetherian base for the affine line; signed twists in the unchanged dependency;
identity and composite field inclusions; and the absence of field-to-finite maps.
The local root normalization includes the scalar at degree zero and every pure
root tensor, so it does not rely on a global generator or a nonempty scheme.

Searches made: msearch LeanSearch on shifted Tate coefficient lines with completed
tensor/pullback/quotient/scalar comparisons (eight algebra/tensor/shift hits, no
orientation interface); msearch LeanFinder on the full coherent orientation
(eight generic adjunction/category hits), completed shifted integral root lines
(eight period-ring/differential hits), scalar comparisons (eight integral-model
and integral-closure hits), geometric families (eight affine-limit/gluing hits),
and finite realization (eight standard-etale-presentation hits); Loogle on
`CategoryTheory.Iso, CategoryTheory.Functor` and on adjunction/mate names; msearch
grep on orientation, Tate, dualizing, projection and scalar-comparison patterns
(zero exact Mathlib matches). Ripgrep of `lean/WeilConjectures`, `lean/Sheaf` and
`dag/nodes`, including the item id and each new declaration name, found no full
interface. `tools/blueprint_refs.py search orientation` gave 51 related nodes;
none is one of the comparison-coordinate helpers. Exact queries/results are in
the new nodes' `mathlib_searches` and in the launcher search log.

All definition data are explicit constructions, projections of supplied data, or
choices uniquely pinned by all local root/scalar formulas. Every postponed
property is a named theorem, with its source and a complete mathematical proof
in its docstring; these are listed in the owning node's Lean declarations. No
axiom or unnormalized Nonempty choice is added. There is no statement dispute or
statement correction.

## Dependency modules

`def-sf-orientation` is repaired under section 1(B) by
`Sheaf.Paper.SixFunctorOrientationFamily`, declaring `SfOrientationDatum`.
The recorded upstream `OrientationDatum` is restricted to one finite ring with
`HasTateTwist`; coefficient and realization compatibilities are separate
predicates rather than required fields. Its comparison data accept arbitrary
exceptional-base-change, tensor, composition and affine-line isomorphisms, and
its implementation note explicitly leaves their canonical construction pending.
It therefore cannot express the full dependency statement. The repair supplies
the actual four-stage family, canonical comparison normalizations and all
geometric, coefficient, realization and affine-line conditions. Only its `lean`
record changes. The original coefficient-twist record is usable and is reused,
not repaired or silently replaced.

## New nodes

`def-sf-orientation-geometric-comparisons` owns
`OrientationGeometricComparisons`: the generic twist/exchange coordinate
interfaces, counit-transpose theta and beta, geometric equations and A5
compatibility equation. Its source is the displayed comparison conventions and
clauses 1-3. Searches found generic adjunction lemmas but no such interface.

`def-sf-orientation-integral-line-comparisons` owns
`OrientationIntegralCoefficientTwists`: one-term shifted actual root complexes,
all-root-normalized arbitrary pullback and completed product comparisons. The
Frobenius-only inverse-image interface does not cover an arbitrary base map.
The source is twist multiplicativity and the base-naturality convention; period
rings and differential base-change search hits are not this construction.

`def-sf-orientation-scalar-line-comparisons` owns
`OrientationCoefficientTwists`: finite-Tor membership of these shifted root
complexes, their canonical shift comparison, and completed/rational scalar
comparison fixed on the actual ordinary scalar representative. The source is
clause 3 and the coefficient conventions. The geometric invertibility wrappers
and the actual finite-field stage transition on these lines are in this module
too. Existing integral-closure scalar maps are unrelated; the existing signed twisting functors remain in use.

`def-sf-orientation-finite-line-comparisons` owns
`OrientationFiniteCoefficientTwists`: the ordinary-etale/pro-etale/intrinsic
realization of the actual derived quotient of every shifted positive power.
The source is the finite root normalization and realization convention in clause
3. Existing site descent is used, not copied; the helper adds its canonical
comparison with the actual derived reduction complex.

`def-sf-orientation-etale-family` owns `OrientationEtaleFamily`: ordinary-etale
geometric orientation families using the actual projection and exchange mates,
with the actual open-counit/projective-trace affine normalization. The source is
the finite-etale family and clauses 1, 2 and 4. It is a constrained family, not
the upstream record with arbitrary smooth comparison inputs.

`def-sf-orientation-geometric-family` owns `SixFunctorOrientationDatum`: the
common-stage bundle, the assembled higher family and its common-component
projection, retaining every finite field and its prescribed A2/A3/A5 coordinates. The source is the higher-stage
part of clauses 1-3. It uses the generic comparison and etale-family helpers and
has no existence field.

`def-sf-orientation-finite-realization` owns
`SixFunctorOrientationFiniteFamily`: native finite components, every ordinary
etale companion and the actual comparison-unit realization equation, together
with the integral-to-finite A5 equation. The source is clause 3, with clause 4
retained in its etale component. Standard etale algebra presentations do not
supply this derived family or comparison.

`def-sf-orientation-etale-line-comparisons` owns
`OrientationEtaleCoefficientTwists`: ordinary etale root powers with their even
shifts, canonical pullback, rank-one flatness and derived tensor multiplication.
The source is the root-line convention of clause 3. It reuses the existing
ordinary root sheaf and its maps; algebraic etale presentation and differential
search hits supply no shifted derived comparison. This separate module keeps
its elaboration within the prescribed per-file limit.

`def-sf-orientation-finite-reduction-comparisons` owns
`OrientationFiniteReductionTwists`: finite shifted root complexes and the unique
derived quotient family characterized by scalar-adjunction transposes and all
ordinary pure root tensors. The source is the finite coefficient comparison
convention of clause 3. Period rings and Fontaine quotient search hits do not
supply this sheaf construction. Separating this comparison from site realization
keeps both files within the compile limit.

`def-sf-orientation-higher-pair` owns `SixFunctorOrientationHigherPair`:
the integral/rational pair with the root-normalized integral coordinates and
actual rationalization equation. Its source is the integral and rational part
of clauses 1-3; the generic geometric-family searches found no such pair.

`def-sf-orientation-stage-compatibility` owns
`SixFunctorOrientationStageCompatibility`: the A5 orientation equation at the
actual finite-field stage transition, using its root-normalized scalar line.
The source is the finite-field part of clause 3, including identity and composite
inclusions. Existing scalar maps alone do not impose this orientation equation.
Separating these notions from the common family makes kernel checking fit the
per-file limit.

All eleven are new definition nodes with their own modules and sources, are
cited by the item, and carry the required searches, blueprint ancestry and
creation records.

## Second reading by Q23

This is the author's separate second pass; the dispatcher explicitly forbids
starting another agent. The maintainer supplies the independent review. I read
the unit, the detailed dependency, the new helper nodes and the Lean declarations
together. The unit statement does not need correction. I checked each hypothesis
and clause in the correspondence above.

Mismatches found and corrected in this pass: an isolated finite-ring orientation
would omit the integral/rational/common family; arbitrary comparison parameters
would not specify theta, beta or the affine trace; the integral Frobenius pullback
would add an IsIso hypothesis on the base map; finite realization needed the
actual comparison unit rather than a chosen exceptional iso; the common stage
needed comparison from every finite field, not only the least one; and affine
normalization had to allow a nonseparated base. The delivered records and
normalizations address these points. Auxiliary projection and exchange
coordinates were also restricted to the smooth maps used by the family, so they
do not require invertibility for arbitrary nonsmooth dualizing objects. The
positive quotient index is a successor presentation of every positive integer, not a restriction to unramified rings.
The source's pullback-first composition formula is the omega-first formula after
the specified tensor symmetry, not a different theta map.

Validation: `scompile.py Q23 sk-def-sf-orientation` compiled all thirteen
submitted files separately, in dependency order, with no errors or warnings.
Every invocation retained the 60-second limit and two threads. The final module
compiled in 7.8 seconds in the library check and 9.2 seconds in the temporary
module check; the largest final temporary-module check was 50.3 seconds.

A separate public module-mode consumer probe also compiled cleanly (7.7 seconds).
It evaluates the finite, integral, rational and common components, accesses the
native realization, finite-reduction and common-stage equations, and checks
integral/common base change and rational composition. It also applies the
unchanged rational and Qbar twisting functors to objects and morphisms at a
symbolic signed exponent and at 0, 1 and -1, using the actual small pro-etale site.
The probe is scratch material and is not part of the delivery.

`deliver2.py Q23 sk-def-sf-orientation --no-push` returned OK: all thirteen
modules compile and server preflight accepts the main item, the dependency
repair, all eleven new nodes, their records, docstrings and report. The initial
ancestry-path metadata fault was repaired to the unit's empty ancestry path;
no source statement was changed.
