## Worker report

This delivery states `AlgebraicGeometry.SchemeDeformation.exists_classification` in
`Sheaf.AlgebraicGeometry.SchemeSquareZeroLiftTorsor`. Its proof is `sorry`.
`Classification` contains the simultaneous normalized classifications and their
compatibility equations. The six supporting modules define data and actual maps;
none contains a postponed theorem or data supplied by `sorry`.
The accepted statement and six-step proof remain unchanged.

Hypothesis and conclusion correspondence:

- Schemes and arrows are `Scheme.{u}`, `f : X ⟶ S`, and `i : S ⟶ S'`.
  `Flat f` and `IsFirstOrderThickening i` are the recorded notions. The latter
  includes closed immersion and square-zero ideal. They occur in the general
  torsor and realization fields. The universe `w` of the sheaf derived
  localization remains independent of `u`.
- A marked flat lift is `Lift f i`: the full subcategory of
  `Under (Over.mk (f ≫ i))` cut out by flat projection and
  `IsPullback marking f projection i`. This is equivalent to a lift with an
  identified special fibre, including its marking-preserving arrows. `Classes`
  quotients by actual categorical isomorphisms; `Aut Y` fixes the marking and base.
- The coefficient `coefficient f i` is the recorded tensor pullback along `f`
  of the tensor pullback along `i` of `i.ker.toModules`. For square-zero `i` this
  is precisely the ideal as an O_S-module, since I/I² = I. `LiftKernel.base`
  fixes the kernel identification on actual pulled-back local ideal sections.
- `cotangentComplex C D f` is the full standard polynomial sheaf complex of the
  actual inverse-image ring map. `Ext C D f G n` is literally derived Hom from
  its image under `DerivedCategory.Q` to the degree-zero module shifted by `n`.
  `C` and `D` are the recorded coherent standard-resolution and sheaf-comparison
  representation data, not assumptions of geometric smoothness or lci.
- If `Nonempty (Lift f i)`, `Classification.torsor` gives `LiftTorsor`.
  `zero`, `add`, and `unique` express an additive action and a unique translating
  Ext-one element between any two actual isomorphism classes. The assertion does
  not claim unobstructedness or choose a lift when none exists.
- `automorphisms` is a group equivalence `Aut Y ≃* Multiplicative (Ext ... 0)`.
  `derivation`, its `derived` and `generators` fields, and
  `automorphism_formula` fix its canonical meaning: on every local section the
  automorphism is e ↦ e + inclusion(d(p(e))). This excludes a sign change or an
  arbitrary group equivalence.
- `opens` uses a normalized ring square and standard-section formula.
  `OpenComparison.ext` applies actual exact restriction and the canonical derived
  shift/single comparisons. `restrict_exists` gives a genuine marked cartesian
  restriction, `restrict_class` fixes the map on classes, and
  `restrict_translate` / `restrict_automorphism` give the two required naturality
  equations. `coefficientRestriction` is constructed from the existing tensor
  comparison and pullback composition, rather than an arbitrary isomorphism.
- Coefficient naturality is stated on `SchemeProblem`, with a prescribed local
  base-ideal map. `problem_base`, `solution`, `solutions`, and `solution_class`
  identify the actual marked lifts with those extension solutions. The ring,
  quotient, kernel and base equations in `LiftSolution` all refer to actual local
  sections. `coefficient_exists` gives pushout solutions and
  `coefficient_translate` / `coefficient_derivation` give the Ext-one and
  Ext-zero coefficient equations. No assertion is made that an arbitrary new
  coefficient module still realizes flat lifts over the same thickened base.
- The torsor action is normalized, not merely existential: `sheaf` is the
  recorded polynomial-normalized sheaf extension classification.
  `translation_normalization` says that a genuine Baer diagram with the extension
  F translates by its recorded conormal class. `extensionClass` interprets that
  same explicitly normalized representative in the chosen universe-w derived
  localization. Its maps are Q(projection), inverse Q(quasi-isomorphism), and
  Q(conormal map), with the canonical single-object shift; it chooses no new map.
- Split bases use Mathlib's actual `TrivSqZeroExt k M`, with `directionReduction`,
  `directionProjection`, and `directionMap`. `FiniteDimensional k M` is present
  in `SplitClassification.classes`. `directionModule` is associated
  sheafification of M followed by the recorded tensor pullback, hence O_X ⊗_k M.
  `split_coefficient_sections` fixes the ideal-to-M comparison by (0,m) ↦ m.
- `SplitClassification.trivial_exists` supplies an actual trivial cartesian
  family; `trivial` identifies exactly its class with zero. `addition` identifies
  the actual two-direction product/pushout deformation operation with addition.
  `coefficients` handles every linear map M → N by actual marked base change;
  `scalar` specifies the k-action by the induced coefficient multiplication map.
  Transporting these operations through the equivalence gives the stated
  deformation vector structure and k-linearity.
- `split_extension` identifies each split lift's ring, quotient, kernel and
  original field action. `split_normalization` identifies its class with the
  recorded polynomial-conormal class. Thus zero and functoriality alone do not
  leave a scalar ambiguity. `split_translate` identifies the split classification
  with the same general torsor action; `split_restrict` gives its open naturality.
- The affine hypotheses are `[Field k] [CommRing A] [Algebra k A]` and
  `Algebra.EssFiniteType k A` (a localization of a finite-type algebra).
  `Naive.Presentation` includes an actual surjective ring presentation, and
  `Naive.IsLocalizedPolynomial P` is the localized-polynomial condition. The
  recorded `Naive.complex P` is exactly [J/J² → Ω_(P/k) ⊗_P A] in degrees -1,0.
- `AffineComparison` has an actual standard-section chain map, with its image
  in the derived category required to be the displayed isomorphism. A chain
  isomorphism of the full affine and sectionwise models is not assumed.
  `AffineComparison.naiveExt` precomposes with the existing canonical full-to-
  two-term projection and uses exact tilde plus the normalized coefficient map.
  `affine_bijective`, `affine_classes`, and `affine_agrees` express the stated
  identification through that particular map.
- `affine_localization` covers every submonoid and every further localization,
  with genuine marked cartesian restriction of lifts and arbitrary chosen
  localized polynomial presentations at source and target. The equation is in
  the full cotangent model after the canonical presentation projections, so it
  does not require a chosen lift between presentations. The coefficient map is
  fixed on all pure tensors. It requires the algebra square to fix k, as a
  k-algebra localization does. In particular identity localization is included.
- No properness, separatedness, Noetherian, dimension, finite-type hypothesis on
  general X, or regular-sequence condition on J occurs. Essential finite type
  appears only in the final affine two-term clause.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` / `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`;
  `WeilConjectures.AlgebraicGeometry.Thickening`: `IsFirstOrderThickening`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`;
  its cartesian formulation is `IsPullback`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackRingMap`,
  `tensorPullbackSection`, and `tensorPullbackSectionComp`.
- `Sheaf.Topology.SheafCotangentComparison`: `Comparison`, `sheafComplex`,
  `sectionArrow`, `sectionElement`; its coherent polynomial-resolution data are
  `Algebra.CotangentResolution.Coherence` and `standardComplex` / `standardComplexMap`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`; exact-functor and single/shift APIs
  supply the canonical comparison arrows. `Field` is Mathlib's field class.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  recorded sheafified tensor framework; `Mathlib.RingTheory.Kaehler.Basic`:
  `KaehlerDifferential` and its universal derivation, through the standard models.
- `Sheaf.AlgebraicGeometry.LciCotangentPresentation`:
  `CotangentPresentation.BaseSquare`, `inverseUnit`, `tildeComplexFunctor`.
  `Sheaf.RingTheory.NaiveCotangentComparison`: `Naive.Presentation`,
  `IsLocalizedPolynomial`, `complex`, `Comparison.comparison`.
- `WeilConjectures.AlgebraicGeometry.OpenRestrictedTensorComplexIso`:
  `SingleComplexBaseChange.openTensorRestrictionIso`;
  `WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris`:
  `moduleOverFunctor_limits`; these transport exact restriction into the
  recorded raw module category without redefining derived open restriction.
- `WeilConjectures.AlgebraicGeometry.TildePreservesFiniteLimits`:
  `tilde_preserves_finite_limits`; Mathlib's actual `tilde.functor` and adjunction.
- `Sheaf.Topology.SquareZeroSheafAlgebra`: `Extension`, `Hom`, `Iso`, `Baer`;
  `Sheaf.Topology.ZariskiSheafAlgebraExtensionExt`: `Classification`,
  `ConormalClass`, `ConormalProjection`, and their coordinate formulas. These
  landed during the work; the earlier duplicate extension structure was removed.
- `Mathlib.Algebra.TrivSqZeroExt.Basic`: `TrivSqZeroExt`, `fstHom`, `inlHom`,
  `map`; the existing DAG definition `def-sc-trivial-square-zero-extension`
  owns this construction. No private copy of the square-zero ring is made.

The main module imports the recorded available proof dependencies for conormal
flat base change, nilpotent flatness, affine derived equivalence, tensor pullback
on affine sections, t-structure orthogonality and triangle exactness. Its proof
docstring follows the accepted six steps, including Baer cancellation and the
truncation argument. The Zariski extension and realization prerequisites are
used at their actual Zariski scheme/sheaf level, rather than an etale-space or
abstract deformation-category substitute.

Edge cases examined: empty X and empty opens (all sheaf formulas and the quotient
still apply); zero base ideal and identity thickening (a unique marked class and
zero kernel); M=0 and the zero linear map (trivial class and zero coefficient
map); characteristic two (no division by 2 or sign-dependent cancellation);
non-affine/non-separated X (only local surjectivity of ring sheaves is required);
non-lci affine singularities (only Ext-one of the two-term truncation is used,
not an assertion that the whole cotangent complex is two-term); identity and
arbitrary further localizations, including ones that are not open immersions.
A coefficient square with a nonidentity field endomorphism is deliberately not
asserted to induce the pure-tensor k-linear restriction map: the localization
square fixes k. No statement dispute or source correction is needed.

Searches: the launcher-recorded LeanFinder query on flat marked scheme
cotangent-Ext torsors returned ring cotangent homology and formal smoothness;
LeanSearch on marked flat square-zero lifts returned `TrivSqZeroExt.liftEquiv`
and derivations lifting ring maps. Loogle on `AlgebraicGeometry.MarkedDeformation,
TrivSqZeroExt` returned unknown identifier; Loogle on `TrivSqZeroExt, LinearMap`
returned the actual ring-map API which is used. Mathlib grep for
`MarkedDeformation|squareZero.*[Tt]orsor|[Cc]otangent.*[Dd]eformation` returned
zero hits. The later LeanSearch and LeanFinder queries for prescribed base
ideals, opens and affine comparisons likewise returned cotangent ideals,
formal unramifiedness and ideal-sheaf gluing. Full wrapper outputs are recorded
in each new node's `mathlib_searches` as logged by msearch.
`rg` on WeilConjectures and Sheaf for the new namespace and comparison names
returned no matches. Literal item-id search in WeilConjectures found no theorem.
The DAG/blueprint search was also checked: the abstract Artin (RS) marked-lift
torsor is different; proper-curve and etale algebraic-space deformation data are
different specializations/sites. The newly landed generic Zariski extension data
and their canonical classification are used directly. The existing scheme
Zariski extension realization uses a scheme base map and is a proof input, not a
replacement for arbitrary coefficient extension problems.

Validation: every delivered module is compiled separately in dependency order
by the prescribed `scompile.py`; all binders and universes are explicit and
`autoImplicit` is false. The final dry-run and delivery are performed with
`deliver2.py`. Only the main existence theorem has `sorry`.

## New nodes

`def-sfb-marked-scheme-lifts` owns `MarkedSchemeLifts`: the full category of actual
flat marked cartesian scheme lifts, its classes, base/restriction predicates,
coefficient and cotangent notation, and genuine split-base deformation
operations. Source: Stacks 0D14 and 0GPZ--0GQ2. Searches above found no general
scheme version; existing trivial-square-zero rings and tensor pullbacks are
reused, not copied.

`def-sfb-zariski-square-zero-extension-problems` owns
`ZariskiSquareZeroExtensions`: a prescribed natural map on the base ideal,
its solutions and their actual extension-isomorphism classes, and compatible
coefficient maps. Source: Stacks 08UC and 0GQ1. The existing generic sheaf
extension definition is imported directly; this node adds the prescribed
base-ideal problem, absent from the searched interfaces.

`def-sfb-scheme-lift-classification-data` owns `SchemeLiftClassificationData`:
normalized local kernel inclusions, degree-zero representatives, the torsor and
split vector-operation interfaces. Source: 0D14, 08U8 and 0GQ0--0GQ2. The searched
ring-map derivation equivalences do not encode marked scheme kernels or their
local normalization. The actual inverse-image and tensor APIs are reused.

`def-sfb-scheme-cotangent-open-restriction` owns
`SchemeCotangentOpenRestriction`: standard-section-normalized cotangent open
comparison and actual Ext restriction with canonical coefficient identifications.
Source: 08SV and 0GQ1. It uses the existing exact restriction functor and tensor
comparison. No new derived restriction functor is defined; the helper only
composes its canonical maps on this specified cotangent Ext group.

`def-sfb-affine-scheme-deformation-comparison` owns
`AffineSchemeDeformationComparison`: affine derived cotangent and coefficient
comparisons fixed on local sections, the actual full-to-naive Ext map, and the
localization compatibility relation fixed on pure tensors. Source: 0D0I and
08UW. Existing cotangent presentation, naive projection, exact tilde and
restriction-of-scalars constructions are used. No searched declaration supplies
this combination of normalized affine deformation comparison data.

`def-sfb-scheme-coefficient-extension-problems` owns
`SchemeCoefficientExtensionProblems`: the inverse-image scheme extension
problem, its solution torsor, actual lift realization data, scalar restriction,
and the recorded conormal representative interpreted in the chosen derived
localization. Source: 08UC, 0D14 and 0GQ0. The generic extension and its normalized
conormal data are imported from the landed nodes; no new sheaf extension,
polynomial presentation or class construction is invented. The added data
connect those existing objects to the marked scheme lift and its base sections.

## Second reading by Q70

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
