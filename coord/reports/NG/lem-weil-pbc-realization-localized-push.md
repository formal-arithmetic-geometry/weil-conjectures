## Worker report

The module Sheaf.Paper.RealizationLocalizedPush states the unchanged node as
WeilConjectures.realization_localized_push, with its conclusions packaged in
RealizationLocalizedPushData. There is exactly one postponed theorem, whose proof
is sorry and whose docstring reproduces all seven steps of the DAG proof.
The helper abbreviations compose existing coefficient transports; none constructs
a new coefficient ring, integral category, localization, or derived operation.

Hypotheses and clauses, with the node and Lean file both open:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite normed extension E/Q_l: `(E : Type u) [NormedField E]`,
  `[NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  The valuation ring, chosen uniformizer and positive quotient tower are exactly
  `PbcIntegralRing`, `pbcUniformizer`, and `pbcIntegralDatum` already used by the
  scalar-functor dependency. The uniformizer is the dependency's fixed choice;
  it is not a new scalar parameter or a different localization.
- Positive prime characteristic unequal to ell: `(k : Type u) [Field k]`,
  `[Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]`.
- T and U over k, separated and finite type: the two `Scheme.Over` instances,
  and `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on each structure map.
- Noetherian, finite dimension, local ell-invertibility: `[IsNoetherian T]`,
  `[IsNoetherian U]`, and the two `Fact` instances for each scheme, respectively
  `∃ n : ℕ, topologicalKrullDim T ≤ n` and
  `∀ t : T, IsUnit (l : T.presheaf.stalk t)` (likewise U).
- Every k-morphism: `(h : T ⟶ U) [h.IsOver (Spec (.of k))]`.
  There is no `IsProper h`, no immersion condition, and no algebraically closed k.
- Small-site completed coefficients A_T: `pbcAdicCompletion T (pbcIntegralDatum l E)`.
  Its site retains object universe u+1 and morphism universe u; coefficient modules
  are in u+1. Indices n : ℕ denote positive powers n+1 as in the dependencies.
- E_T and the inclusion A_T → E_T: `rationalCoefficientSheaf l T E` and
  `sT.scalarMap l E T = sT.integralIso.hom ≫ sT.inclusion`.
  `sT` and `sU` are arbitrary data of the recorded scalar-functor theorem, whose
  fields already require the finite-coordinate and continuous-inclusion
  normalizations. Quantifying these witnesses makes the statement usable with
  the same scalar functor elsewhere; their existence is the imported theorem.
- Integral and raw rational categories: `PbcBoundedConstructibleComplete` and the
  unchanged scalar-functor data's `J` on `PbcRationalCategory`. This lemma concerns
  actual ambient F on integral objects, so it requires no further localization J.
- F is actual derived scalar extension: `pbcDerivedExtend (sT.scalarMap l E T)`.
  Restriction and unit are `pbcDerivedRestrict` and `pbcDerivedScalarAdjunction`.
  The scalar-functor dependency retains its pure tensor unit normalization.
- Ordinary ambient integral image: `proEtaleRingDerivedDirectImage h` at the
  completed coefficient rings and `integralPullback`. Its equality with the
  actual canonical coefficient map is `integralPullback_normalization`.
- Integral constructibility for every M: `integral`, quantified over the existing
  full subcategory, states `PbcIsBoundedConstructibleComplete` of that ambient image.
- Agreement with the specified completed image: `completed` states existence of
  the product and `SfIntegralDirectImage` for the input in the detailed coefficient
  coordinates, and an isomorphism from the ordinary ambient image to its object
  transported back. This is the existing Roos-triangle definition, including its
  actual `sfDirectImageTerm` and `sfDirectImageTransition`, not arbitrary finite
  images or an unspecified tower. `realizationDetailedEncoding` is the existing
  coefficient equivalence at `integralDetailedCoefficientComparison` derived
  termwise; its forward direction is detailed → Pbc.
- Actual continuous E direct image: the rational `proEtaleRingDerivedDirectImage`
  uses `rationalPullback_normalization`, which characterizes precomposition on
  continuous sections. `continuous_direct_image` also explicitly identifies this
  functor with the archived internal `CondensedRing.lowerStar.rightDerivedFunctor`
  conjugated by the exact published internal-to-sectionwise module encodings.
- Canonical beta and naturality: `beta` is a natural transformation on the full
  integral subcategory from Rh_A ⋙ F_U to F_T ⋙ Rh_E. `beta_isIso` requires every
  component to be an isomorphism. Thus naturality includes all ambient morphisms
  between integral objects, not just chosen lattice presentations.
- Unit normalization: `beta_normalization` asserts that the scalar-adjunction
  transpose of beta is Rh_A(eta_T) followed by d inverse. The named d is exactly
  `proEtaleRingRestrictionDerivedDirectImage`, applied to `coefficient_square`.
  This Hom equivalence is bijective, so the equation uniquely specifies beta;
  no arbitrary map or arbitrary isomorphism replaces the canonical comparison.
- The coefficient square is a conclusion, not an extra assumption; both its
  coefficient inverse-image maps are normalized. No extra coefficient compatibility
  hypothesis is imposed on h or M.

Dependency declarations used:

- Sheaf.Paper.IntegralUniformCoefficient publicly reexports the owning definition
  in Sheaf.Paper.BoundedConstructibleComplete: `PbcBoundedConstructibleComplete`,
  `PbcIsBoundedConstructibleComplete`, `pbcIntegralDatum`, and `pbcUniformizer`.
  The already published E : Type u specialization is the one used by the scalar
  dependency; the E : Type (u+1) convenience wrapper is not a replacement category.
- Sheaf.Paper.PbcRationalCategory: `PbcRationalCategory`, `pbcRationalization`.
- Sheaf.Paper.RealizationScalarFunctor: `RealizationScalarFunctorData` and
  `realization_scalar_functor`, including all coefficient normalizations and
  exact derived extension/restriction adjunction data.
- Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction:
  `continuousCoefficientImmersionRestriction`, `rationalCoefficientSheaf`,
  `rationalCoefficientRestrictionNormalized`; no immersion restriction is used
  for the arbitrary h of the present theorem.
- Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing and its framework exports:
  `Profinite.continuousCoefficientRingObj`, `condensedRingObj`, and the ordinary
  internal `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar`.
- Sheaf.Paper.ContinuousCoefficientModuleEncoding: `ringModuleEquivalenceOfIso`;
  the existing `InternalAbelianSheafModule.sectionModuleEquivalence`.
- Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations reexports the ordinary
  arbitrary-ring operations and canonical adjunction interface:
  `proEtaleRingDerivedDirectImage` and `proEtaleRingDerivedAdjunction`.
- Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction:
  `proEtaleRingRestrictionDerivedDirectImage`, with its unique derived-unit
  normalization, and the exact restriction comparison.
- Sheaf.Paper.SfDerivedDirectImage: `SfIntegralDirectImage`,
  `sfDirectImageTerm`, `sfDirectImageTransition`.
- Sheaf.Paper.IntegralStratifiedPerfectCharacterization (publicly imported by the
  scalar-functor module): `integralDetailedCoefficientComparison` and
  `integralStratifiedPerfectDetailed`.
- Sheaf.Paper.CompletedTowerDirectImage/CompletedTowerPullback:
  `completedCoefficientMap` and ordinary completed direct-image constructions.

All available proof-dependency modules are imported for the seven-step future
proof, including localization homology and push continuity, chart naturality,
profinite pullback, completed direct-image limits, ringed derived composition,
K-injective resolutions and valuation-ring finiteness. None is reproved here.

Source checked: pdftotext of literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf,
Lemma 6.7.2 (p.54 in printed numbering) and Remark 6.8.15 (p.62).
Lemma 6.7.2 permits a finitely presented qcqs map with quasi-excellent ell-coprime
base, without properness; finite type over a field gives this case. Remark 6.8.15
uses ordinary ambient continuous-coefficient derived operations. The node's
coefficient identifications additionally follow its cited DAG proof and scalar
functor interface.

Edge cases checked: T empty; U empty (then any T mapping to it is empty); M=0;
h=id; h an open immersion that is not proper; non-algebraically-closed k; ramified
E with ell a unit times a uniformizer power e>1; and uniformizer-torsion integral
M. No binder drops these cases. Empty-scheme dimension uses an upper bound,
not equality to a natural dimension. The beta normalization also makes sense when
both localized vertices are zero. The statement requires neither invertibility
of the integral localization unit nor an isomorphism for arbitrary unbounded M.

Searches for an existing statement:

- msearch.py leanfinder: "Derived direct image of bounded constructible adic sheaves
  commutes with scalar localization through the extension restriction adjunction unit".
  Eight hits, including localCohomology.diagram and ordinary restriction-adjunction
  facts; no matching constructible adic localization theorem.
- msearch.py loogle: `"DerivedCategory", "localization"`. Six hits are instances
  describing the derived-category localization at quasi-isomorphisms, not this claim.
- msearch.py grep: `(localiz|scalar).*(DirectImage|directImage|pushforward)|
  (DirectImage|directImage|pushforward).*(localiz|scalar)`. Twelve hits are ordinary
  module pushforward, localizing modules, and algebraic-geometric stalk localization.
- msearch.py leansearch: "Derived direct image commutes with l adic scalar
  localization on bounded constructible sheaves". Eight hits on exact-functor
  derived factorization and ordinary module localization; none match.
- rg on lean/WeilConjectures and lean/Sheaf for the same concept and for the item id,
  `realization_localized`, `RealizationLocalized`: no existing declaration of this
  item. Existing PbcScalarExtension comparisons concern finite extensions of
  integral coefficient rings, not integral → field localization. Reused their
  scalar infrastructure via the recorded scalar dependency.

Validation: scompile.py NG lem-weil-pbc-realization-localized-push on the final
module passed both sandbox and library module checks (13.0 s and 14.3 s), with
no errors or warnings. No global build or direct shared-repository write was run.
There is no statement correction, disputed statement, new node, or dependency repair.

## Second reading by NG

A separate agent is forbidden by the dispatch brief; this is an explicit worker
cross-reading, with the maintainer's independent delivery review still required.
I reopened the original JSON and the final Lean file and matched each hypothesis
and clause above. Two elaboration defects were repaired during compilation: the
coefficient equivalence must point detailed → Pbc, and the existing equivalence's
additivity is supplied from preservation of binary products in the helper's real
construction. I then added the explicit archived-internal/sectionwise direct-image
isomorphism, so the E-coefficient target cannot be read as an unrelated operation.
The coefficient square and beta adjunction equation are conclusions of the theorem.
They are not arbitrary input maps or compatibility assumptions. The integral
subcategories, scalar localization and normalized finite-image tower are reused,
including the actual transition maps. No mathematical statement field was changed.
