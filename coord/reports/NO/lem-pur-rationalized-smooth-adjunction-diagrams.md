## Worker report

Item: lem-pur-rationalized-smooth-adjunction-diagrams. Group NO.

The delivery states the raw scalar-localized smooth adjunction, both coefficient
comparison equations, coefficient cocycles and identity normalization, and the
three-Hom-bijection comparison with the continuous condensed realization. The
main theorem is `WeilConjectures.RationalizedSmoothAdjunction.rationalized_smooth_adjunction_diagrams`.
All postponed proofs are named theorems with source and natural-language proof.
Definitions have actual data; the only selections are of uniquely characterized
linear equivalences, whose underlying equivalence is prescribed.

Hypotheses and clauses:

* `D : FiniteFieldDatum`, `Fact l.Prime`, and `hl : l ≠ D.p` retain the finite
  base, its algebraic closure, and the distinct coefficient prime. `Ω` is a fixed
  algebraic closure of the p-adic field and `Padic.FiniteCoefficientFields l Ω`
  indexes its finite coefficient subfields.
* Scheme `Over`, structure-morphism `LocallyOfFiniteType`, `QuasiCompact`, and
  `IsSeparated` are exactly separated finite type over D.k. `IsOver` for j≫p
  makes the map a k-morphism. `SmoothOfRelativeDimension d (j≫p)` with `d : ℕ`
  expresses smoothness and pure nonnegative relative dimension. The open/proper
  factorization is the supplied compactification, not an extra restriction on f.
* `Presentation` bundles the dependency's strict tower data and its already
  constructed `SpIntegralAdjunction.Realization`. Its fields include the actual
  source comparison, purity orientation, reconstruction normalization and tower
  adjunction; they do not assume the conclusions of this item.
* `P` is the dependency's completed proper/open composite, restricted to the
  integral constructible full subcategory. `J` is its tower right adjoint after
  the specified total derived limit. `H` uses `SpTwistedPullback.source`, hence
  the actual completed derived pullback, degree-zero Tate line d and shift 2d.
* `gammaComponent` is the dependency's displayed realized purity map, including
  the reconstruction unit and the entire-system gamma. `gamma_laws` assembles
  its naturality and invertibility; `gamma` is that natural isomorphism.
  `adjunction` is `ofNatIsoRight gamma.symm` on the supplied adjunction.
* `integral_linear` states P-linearity, H-linearity, and both transported formulas:
  etaJ followed by gamma.inv, and P(gamma.hom) followed by epsilonJ. `hom_linear`
  gives a linear equivalence with exactly the ordinary transported Hom equivalence
  as underlying Equiv, so its inverse is linear too. `tower_hom_linear` records
  the same statement for the original P–J adjunction before transport.
* The categories and Q are the existing `sfRationalConstructibleCategory` and
  `sfRationalConstructibleLocalization`: raw localization, unchanged objects,
  scalar-first tensor Hom. `sfRationalCoefficientEquiv` identifies the localized
  uniformizer ring with B. `rationalP` and `rationalH` use the existing semilinear
  scalar extension specialized to the identity ring homomorphism.
* `Raw.hom_tmul` and `Raw.inv_tmul` state the two tensor formulas; `hom_add` and
  `hom_smul` state linearity. Its `Adjunction` includes naturality on all rational
  arrows and both triangles. `Raw.unit`/`counit` are Q of the specified integral
  unit/counit. Thus finite sums and rational isomorphisms need no integral inverse.
* `IntegralComparisons.b` and `.a` are the given natural isomorphisms using the
  published completed coefficient functors. `.unit` and `.counit` render each
  factor of the two node equations in Lean's left-to-right composition order.
* `RationalComparisons` uses the actual `sfRationalScalarExtension`; its four
  component fields identify both comparisons and their inverses with Q of the
  integral components. HEq is used only for the published coefficient functor's
  propositionally equal object representatives; the unit/counit equations are
  ordinary typed equalities. Natural isomorphisms have naturality on every arrow.
* `IntegralCocycles`/`RationalCocycles` use the actual integral/rational scalar
  associators and state both P and H equations. `IntegralIdentity` and
  `RationalIdentity` use the actual scalar unitors. `coefficient_comparisons`
  retains exactly the conditional cocycle and identity claims.
* `internalization` transports completed coefficients through the recorded
  coefficient isomorphism, then the existing section/internal module equivalence.
  `rationalRing` is the actual continuous-function field ring in the scheme
  universe. `invertMap` is postcomposition by the valuation-ring inclusion;
  `invert` is its actual total derived scalar extension. `realize` composes these
  with the full-subcategory inclusion. No raw category is equated to a condensed
  one, and no idempotent completion is taken.
* `condensedP` is the separately derived compactification composite.
  `rationalLine` is the existing integral Tate line transported to internal
  coefficients and inverted. `condensedH` is the actual rational derived
  pullback, relative derived tensor by that line, and shift. `Endpoints` records
  the two endpoint identifications used by the source: compact-support clause
  (2) of integral-direct-image-tower and ordinary-line/derived tensor/shift
  comparison. The comparison theorem is valid for every such endpoint pair,
  hence in particular for the specified canonical pair; it does not choose an
  arbitrary map to define a functor or an adjunction.
* `fieldScalarSections`, `fieldEncoding`, `fieldHomModule`, and
  `localizedHomModule` retain the constant continuous B action, using the existing
  universe-polymorphic encoding instead of restricting coefficients to Type 0.
  `HomComparisons` consists of the normalized linear rho maps at X and Y; integral
  normalization and linearity give rho(a tensor h)=a h[1/ell]. Its existence is a
  conclusion of the final theorem, using the localized-Hom dependency.
* `tensorHom` tensors the uniquely fixed integral linear equivalence. `threeHom`
  explicitly composes endpoint conjugation, rhoY inverse, tensorHom, rhoX and the
  final endpoint conjugation. `realization_agreement` and the final clause compare
  this with the independently specified raw adjunction on every rational arrow.
  Applying the equality to identity is the rational-purity unit normalization.

Dependency declarations read and used (module : declarations):

* Sheaf.Paper.PurityFiniteSetting : PurityFiniteSetting; its imported
  Sheaf.Paper.FiniteFieldFiber : FiniteFieldDatum, CoefficientDatum.
* Mathlib.AlgebraicGeometry.Morphisms.Smooth : SmoothOfRelativeDimension.
  Scheme-morphism dependency is the existing Over, IsOver, IsSeparated,
  LocallyOfFiniteType and QuasiCompact classes, not a duplicate property.
* Sheaf.NumberTheory.Padics.CoefficientExtensionFinite :
  Padic.finite_coefficientExtensionRing, coefficientExtensionIntegers,
  coefficientExtensionUniformizer; these are used by the existing categories.
* Sheaf.Paper.SfIntegralConstructible : sfIntegralConstructible,
  sfIntegralConstructibleCategory.
* Sheaf.Paper.CompletedIntegralConstantMapOfUniverses :
  integralConstantToCompletionOfUniverses; retained through completed coefficients.
* Sheaf.Paper.QcqsCompactSupportRealization : sfQcqsCompactSupportRealization.
  P uses the same actual completed compactification composite identified there.
* Sheaf.Paper.IntegralAdjunctionBijection :
  AlgebraicGeometry.ProEtale.SpIntegralAdjunction.Realization,
  integral_adjunction_bijection, support, right; its full purity signature was read.
* Sheaf.Paper.DerivedPullbackTensorHom and
  Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted : completed integral pullback
  and integralTwistLine, as used in SpTwistedPullback.source.
* Sheaf.Paper.CompactSupportReductionTower : exists_compactSupportReductionTower;
  Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients :
  strict tower total limit; these provide the stipulated linear model in the proof.
* Sheaf.Paper.SfRationalizationKaroubi : sfRationalConstructibleCategory,
  sfRationalConstructibleLocalization, sfRationalCoefficientEquiv,
  sfRationalScalarExtension. Sheaf.CategoryTheory.ScalarLocalization :
  ScalarLocalization, localization, extension.
* Sheaf.Paper.IntegralScalarExtensionUniverses :
  sfConstructibleIntegralScalarExtension; Sheaf.Paper.SfScalarExtensionComposition :
  sfIntegralScalarComp, sfRationalScalarComp, sfIntegralScalarUnit,
  sfRationalScalarUnit.
* Sheaf.Paper.IntegralDirectImageTower : Integral, sectionEquivalence, shriek,
  integral_direct_image_tower (canonical reconstruction, clause 2).
* Sheaf.Paper.RationalLocalizedHom : rationalLocalizedHom, its exact pure-tensor
  signature and comparisons. The published Type-0 encoding is generalized using
  Sheaf.Paper.ContinuousModuleEncodingUniverses.continuousRingModuleEquivalenceUniverse
  and Sheaf.Topology.ContinuousMapCondensedRingMap's existing postcomposition map.
* Proof tools: KInjectiveTotalDerivedLinear, LinearRightAdjoint,
  SemilinearScalarLocalization, OrdinaryLineDerivedScalarComparison and
  DerivedTensorAdditiveConstraints, using their recorded interfaces.

Source reading: current literature/blueprint/latest, field-extension sole proof
paragraph, and rational-adjunction proof part (1), all three Hom bijections.
No SGA route was used.

Searches for an exact existing statement:

* msearch leanfinder, "scalar localization of a linear adjunction, unit counit and
  coefficient comparison cocycles": eight generic localization/unit/counit hits;
  none states this geometric functor's linearity, normalization and cocycles.
* msearch loogle, "CategoryTheory.Adjunction, CategoryTheory.Functor.Linear,
  Algebra.TensorProduct.map": no hits.
* msearch grep, "scalarLocalization|localiz.*[Aa]djunction|[Aa]djunction.*localiz",
  CategoryTheory: eleven generic localization hits, no exact statement.
* msearch leansearch, "localization of a linear adjunction preserves unit and
  counit": eight generic localization hits, no normalized geometric comparison.
* rg in lean/WeilConjectures and lean/Sheaf for rationalized smooth adjunction,
  linear Hom equivalence, scalar localization and coefficient cocycles: existing
  generic tools and the listed dependencies; no exact full statement. The exact
  item-id search in WeilConjectures returned no declaration.

Edge cases checked before writing: d=0 (no artificial positivity), empty schemes
(no nonemptiness/connectivity assumptions), zero objects and torsion Hom modules
(no flatness/freeness of Hom assumed), E=F and identity coefficient maps (actual
unitors), three equal fields (actual associators), ramified finite extensions
(the coefficient equivalence uses the chosen uniformizer, while the continuous
functor inverts ell), and rational isomorphisms with no integral inverse. Tensor
formulas and naturality concern every finite sum; no integral lifting is assumed.
All universes and variables are explicitly bound and autoImplicit is false.

No correction to the node statement is requested. No false edge case was found.

## Second reading by NO

This is a second pass by the same worker. The dispatcher explicitly prohibited
starting other agents and assigned independent delivery review to the maintainer;
no independent reader is claimed here. I re-read the source, node and signatures,
checking comparison orientation, the two adjunct equations, both cocycles, inverse
components and the distinction between raw localization and condensed realization.
The pass corrected an extra unused compact-support argument and made the coefficient
universe explicit. The scalar comparison uses the existing universe-polymorphic
continuous encoding, retaining the constant-section action.

## New nodes

`def-pur-integral-smooth-adjunction-presentation` defines only the bundle of the
already supplied tower inputs and the exact published integral Realization, plus
its P, J, H and specified gamma component. The source is the integral-adjunction
proof's Normalization/Bijections/Purity, used before field-extension rationalization.
Mathlib LeanFinder/LeanSearch returned generic test-function and condensed adjunction
hits, while CategoryTheory grep returned zero. Project grep found only the
parameterized Realization; the DAG reconstruction-data node packages a different
interface and blueprint_refs found no bundle. Thus this bundle is new, while every
mathematical operation in it remains an existing recorded declaration. It has no
sorry or existence assumption. Splitting it out followed the failed 69-second
consolidated compile, after making the large purity map irreducible.

The same definition node also owns the concrete continuous endpoint categories,
scalar extension, section encoding, constant-section Hom action, Endpoints and
HomComparisons data types used by the final clause. These data types assert no
existence and choose no arbitrary endpoint. This second separation reduced the
62.2-second theorem file while retaining one definition-node owner and actual
constructions; the main theorem still asserts the existence and comparison clauses.
