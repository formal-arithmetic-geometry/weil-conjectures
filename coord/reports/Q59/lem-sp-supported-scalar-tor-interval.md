## Worker report

The module `Sheaf.SecSmoothPurity.SupportedScalarTorInterval` states
`AlgebraicGeometry.ProEtale.SupportedScalarTorInterval.supported_scalar_tor_interval`.
Its only theorem has proof `sorry`. All five helpers have real definition bodies,
using published functors and canonical maps. No assertion is proved here.
The mathematical statement, proof, and proof dependencies are unchanged.
The two already-landed definition nodes `def-sp-open-coefficient-adjunction-data`
and `def-sp-proetale-scalar-mate-identifications` are added to statement dependencies
because their existing canonical interfaces occur in the displayed maps.

Hypotheses and clauses, matched individually:

* Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`.
* Finite commutative rings: `{A B : Type u} [CommRing A] [CommRing B]
  [Finite A] [Finite B]`. The existential hypotheses `_hA` and `_hB` say that a
  power of ell annihilates every element, using natural-number repeated addition.
  `φ : A →+* B` is unital, including the zero-ring case.
* Schemes and open immersion: `{U Z : Scheme.{u}} (j : U ⟶ Z)
  [IsOpenImmersion j]`. There is no quasi-compactness or Noetherian condition.
* Ordered integers: `(a b : ℤ) (_hab : a ≤ b)`.
* Arbitrary pro-etale complex and Tor hypothesis: `(M : proEtaleDerivedCategory U A)`
  and `_hTor : HasProEtaleTorAmplitude U A M a b`, the original-site intrinsic
  predicate publicly retained in the recorded Tor dependency's declarations.
* `aU` and `aZ` are existing `ProEtaleTensorModel`s: presentations of the actual
  ordinary uncompleted K-flat derived tensor with their representative isomorphisms.
  They impose no condition on M, schemes, or rings. The theorem works for every
  such presentation. There is no new derived tensor definition.
* N is `((openExtension (A := A) j).obj M)`. This is the published
  `proEtaleRingDerivedOpenExtension` at the constant-ring comparison, exactly the
  extension used by the recorded generic open-adjunction and projection node.
  The other recorded finite intrinsic presentation `sfIntrinsicExtensionByZero`
  transports fixed-coefficient extension through realization equivalences; it is
  the same extension-by-zero construction, canonically identified by uniqueness
  of the left adjoint to restriction. We reuse the existing generic presentation,
  rather than define an extension functor or choose an arbitrary map.
* Q is `tensor φ U aU M`, namely `aU.tensor.obj
  (M, DerivedCategory.Q.obj (scalarMateCoefficientComplex φ U))`.
  The existing coefficient complex restricts the B-module unit along the actual
  map A_U to B_U and puts it in degree zero. It retains only the A-action.
* M_B is `((scalarExtensionFunctor φ U).obj M)`, with its genuine B-action.
* Ambient restriction is the existing `scalarRestriction φ Z`, whose definition
  is exact `mapDerivedCategory` of `proEtaleRingRestrictScalars`, ultimately
  Mathlib `SheafOfModules.restrictScalars`. No arbitrary coefficient action occurs.
* First canonical isomorphism: `IsIso (projection φ j aU aZ M)`.
  `projection` is the hom of `openProjectionIso` for the constant A coefficient
  family, followed by j_! of identity tensor the hom of
  `scalarMateDerivedCoefficientPullback φ j`. Thus it is precisely the forward
  open projection, with j inverse B_Z identified with B_U. The first factor is
  the inverse of the recorded open-unit tensor adjunct.
* Second canonical isomorphism: `IsIso (restrictionComparison φ j aU M)`.
  Its first factor is j_! of the inverse of `scalarMateDerivedTensorIso`.
  That published isomorphism is uniquely fixed by the common K-flat tensor
  representative and ordinary balancing identification. Its second factor is
  `openRestriction (change φ) j`, the exact derived restriction-of-scalars
  extension-by-zero comparison. These are specified maps before invertibility.
  `IsIso` supplies actual derived isomorphisms via `asIso`, rather than just
  degreewise homology isomorphisms or an existence claim about arbitrary maps.
* Four vanishing clauses: for every `q : ℤ` with `q < a ∨ b < q`, four `IsZero`
  statements apply `DerivedCategory.homologyFunctor` to Q, N tensor B_Z,
  j_!Q, and Res(j_! M_B), respectively, in exactly that order.
  These are the three A_Z objects in the isomorphism display and Q on U.
* Every etale origin: quantify over all
  `E : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) Z`, then every
  `_r : (finiteCoefficientIntrinsicDerivedComparison Z A).obj E ≅
  tensor φ Z aZ ((openExtension (A := A) j).obj M)`.
  The conclusion is `IsZero ((DerivedCategory.homologyFunctor _ q).obj E)`
  for all q outside the same interval. E has no initial boundedness assumption.
  ULift is the existing common u+1 coefficient convention for the small sites;
  site objects have universe u+1 and morphisms universe u throughout.
* There is no constructibility, etale origin for M, completion, flatness, or
  projective-dimension hypothesis. No nontriviality assumption is imposed on A or B.

Dependency interfaces read and used:

* `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: the finite coefficient category,
  ordinary derived localization, and etale category presentation; and its
  constant-ring realization interface in
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`, specifically
  `finiteCoefficientIntrinsicDerivedComparison` (exact module comparison termwise).
* `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` and
  `DerivedCategory.homologyFunctor`, using ordinary unbounded localizations.
* `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `sfIntrinsicExtensionByZero`, its transported finite intrinsic presentation;
  `Sheaf.SecSmoothPurity.OpenScalarExchange.openExtension` is the existing generic
  ringed presentation used in the recorded open-adjunction interface.
* `Sheaf.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses` publicly retains
  `AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude`, used for the precise Tor test.
* `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`:
  `AlgebraicGeometry.ProEtale.derivedTensor` is the ordinary fixed-coefficient
  derived tensor; its intrinsic K-flat presentations are the recorded
  `ProEtaleTensorModel` interface of
  `Sheaf.Paper.ProEtaleCanonicalTensorPullback`, used here through the comparison node.
* `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`:
  `AlgebraicGeometry.ProEtale.scalarExtensionFunctor`, K-flat computation with B-action.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, used by scalarRestriction and coefficient sheaves.
* `Sheaf.Paper.IntegralCompactSupportCoefficientData`:
  `WeilConjectures.PurCompactSupport.Coefficients`, `Change`,
  `openProjectionIso`, `openProjectionInverse_isIso`, and `openRestriction`.
* `Sheaf.Paper.ProEtaleScalarMateNormalization`:
  `scalarMateCoefficientComplex`, `scalarMateDerivedTensorIso` and
  `scalarMateDerivedCoefficientPullback`; all have the published unique tensor,
  section and inverse-image normalization, which was read in full.
* Proof imports: recorded `ProEtaleConstantRingMap`, `ProEtaleExtensionZero`,
  `ComparisonPullbackExact`, and `ProEtaleClassicalSheavesModules`, supplying
  constant-coefficient identification, exact extension and scalar compatibility,
  degreewise comparison of homology, and faithful module comparison. The generic
  open projection proof module is already public because its definitions are used.

Sources opened: Stacks sites-cohomology.tex, definition-tor-amplitude (08FZ),
lemma-j-shriek-and-tensor (0GL1), lemma-derived-base-change (06YY);
proetale.tex lemma-fully-faithful (099T); current blueprint
`sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-direct-image.proof.md`, Step 1.
The theorem docstring contains all five DAG proof steps with dependency names.

Edge cases checked mathematically before writing:

* Empty U or empty Z: open extension and the supported tensor are zero;
  exact faithful comparison reflects zero cohomology of any stated E.
* Zero M: all displayed tensors and extensions vanish.
* Zero ring B, and the unique permissible zero-ring A maps: restriction and tensor
  still have the stated actions; the category is trivial when its ring is zero.
* Identity immersion and identity coefficient map: the comparisons reduce to the
  published tensor unitor and restriction identities, not arbitrary automorphisms.
* a=b, negative bounds, and arbitrary shifts: strict outside inequalities express
  exactly the integer complement of the closed interval, including its endpoints.
* Nonflat Z/4 to Z/2 at ell=2: allowed. A shifted free A-sheaf has its asserted Tor
  interval after testing B; no finite projective-dimension assumption was introduced.
* An unbounded E is allowed as an input. Its cohomology is reflected degree by degree,
  without using unbounded derived full faithfulness.

Searches for an existing exact statement:

* msearch leanfinder, query "Extension by zero of a proetale finite Tor amplitude
  complex after derived coefficient tensor has the same cohomology interval reflected
  through etale comparison": eight hits, including DerivedCategory.isGE_Q_obj_iff,
  isLE_Q_obj_iff and Tor-projective vanishing; none states this comparison and reflection.
* msearch loogle, query `"DerivedCategory", "torAmplitudeIn"`: zero hits.
* msearch grep, `torAmplitude|openProjection|extensionByZero`, subdirectory
  CategoryTheory: zero hits.
* rg on upstream WeilConjectures and project Sheaf, exact node id and names
  `supportedScalarTorInterval|supported_scalar_tor_interval`: no existing statement.
  Broader searches for `HasProEtaleTorAmplitude`, `openProjection`, scalar restriction,
  and supported tensor found existing constituent interfaces, all reused above.
  `SupportedEtaleTensorOrigin` assumes constructible cohomology and finite Tor amplitude;
  its conclusion does not supply this hypothesis-free arbitrary-origin interval theorem.

Validation: scompile.py Q59 lem-sp-supported-scalar-tor-interval compiled the module
in sandbox mode (5.7 s) and library mode (5.9 s), with no errors or warnings.
No new nodes, dependency replacements, disputed statements, or statement corrections.

## Second reading by Q59

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
