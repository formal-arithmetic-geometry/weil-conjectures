## Worker report

The delivery states lem-per-rational-realization-finite-cone-models in
`Sheaf.Paper.RationalRealizationFiniteConeModels`, namespace
`AlgebraicGeometry.Scheme.RationalConeModels`. All six theorems have proof `sorry`.
The helper abbreviations reuse the published categories and functor, the shift
instance is the supplied `s.shift`, and the two witness definitions contain actual
data and propositions. There is no new coefficient construction, completion,
rationalization, derived category, or tensor product.

The source was read directly in Bhatt--Scholze, *The pro-etale topology for schemes*,
PDF pp. 61--62: Lemma 6.8.13 supplies integral structures and Proposition 6.8.14(2)
reduces essential surjectivity to local systems using full faithfulness. The node's
seven-step expansion specifies finite filtrations, common denominators, two signed
rotations, rescaling and successive standard truncations. The declaration docstrings
carry those steps and their dependency names. No statement correction is needed.

Hypotheses and objects, clause by clause:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite E over Q_ell: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. Its valuation ring and uniformizer are the existing
  `pbcIntegralDatum l E` and `pbcUniformizer l E`, with the standard harmless ULift.
- Noetherian finite-dimensional X with ell invertible: `(X : Scheme.{u})
  [IsNoetherian X] [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]`. Facts bind exactly these
  hypotheses; no separate dimension witness is fixed.
- Small pro-etale site and completed coefficient B_X: the existing `pbcModules`,
  `pbcAdicCompletion X (pbcIntegralDatum l E)` and `PbcCompletedDerived` use
  `Scheme.ProEt.topology X`. Site objects are in u+1, site morphisms in u; module
  sections are in u+1 and ambient derived Hom sizes in u+2. No site universes are
  equated.
- Rational E_X is the existing `rationalCoefficientSheaf l X E`. The input
  `s : RationalModuleRealization l E X` includes the normalized integral-limit and
  sheaf-localization identifications. Thus this is the stipulated E_X, rather than
  a constant field sheaf or an arbitrary coefficient map.
- C_X is `Integral l E X`, an abbreviation for the existing
  `PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)`. Its membership includes
  intrinsic completeness, uniform constructible reductions and compatible etale
  origins. All integral morphisms remain the actual ambient morphisms.
- Q is `pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)`; the helper
  `realize l E X s` is exactly `Q ⋙ s.J`. The input record's `objects`, `fractions`,
  `derived_exact`, and `cohomology` fields fix F_X, J_X and their required formulas.
- Full faithfulness is an assumption, as the two explicit binders `_full : s.J.Full`
  and `_faithful : s.J.Faithful`. This delivery does not assert their existence.
- A supplied filtration is packaged as `Filtration l E X s F`. Its `H`, `inclusion`,
  `step`, `mono`, `start`, `finish`, `commutes`, `step_mono` encode precisely a finite
  filtration from zero to F. Its `model` consists of actual C_X objects;
  `degreeZero` says they are integral sheaves in degree zero, and `quotient` is the
  supplied realization comparison with each cokernel. These are the integral
  degree-zero quotient models of the dependency, after applying its normalized
  scalar comparisons. The additional stratum geometry is not needed by the cone
  construction. Any supplied filtration and models of this form are allowed.
- In `sheaf_model` and `bounded_model`, `_models` explicitly assumes such supplied
  filtrations for every constructible rational sheaf. This is the conditional
  integral-model input from lem-per-rational-stratum-integral-models, not a fresh
  assumption that the desired bounded derived objects already have models.
- Constructible rational sheaves are expressed literally as existence of
  `FiniteLocallyClosedStratification X` with `IsFiniteLocallyFree` after the existing
  `proEtaleModuleInverseImage` to every stratum. Over field coefficients this is
  pro-etale local finite freeness, as in the statement and the realization record.
  Constructibility of cohomology uses the same predicate on every value of the
  recorded `DerivedCategory.homologyFunctor`.

Conclusions, clause by clause:

- `image_closed` says `s.J.essImage.IsClosedUnderIsomorphisms`, `.ContainsZero`,
  `.IsStableUnderShift ℤ`, and `.IsTriangulatedClosed₂`. Mathlib's essential image
  already closes the image under isomorphisms. Its second-vertex triangle closure
  is exactly distinguished extension closure with endpoints merely isomorphic to
  image objects.
- `extension_cone` takes the actual three arrows of
  `J(QK₁) -> C -> J(QK₂) -> J(QK₁)[1]` and its distinguishedness.
  The `∃! α` is the unique lift, with its image followed by the existing composite
  shift comparison equal to δ. The next `∃ (n : ℕ) (f : K₂ ⟶ K₁⟦1⟧)` states the
  integral fraction formula, using the recorded coefficient equivalence
  `pbcRationalCoefficientEquiv`. Numerator and denominator are not claimed unique.
- The same conclusion supplies integral D and K, an integral distinguished cone
  `Triangle.mk f g h`, `Nonempty (K.obj ≅ D.obj⟦-1⟧)`, and
  `Nonempty ((realize ...).obj K ≅ C)`. Thus a shifted integral cone represents C.
- The supplied triangle morphism φ has source `(Triangle.mk i p δ).rotate.rotate`
  and target the realization of that integral cone. Its first component is the
  identity; its second is the inverse shift comparison followed by realization
  of `varpi^n • 𝟙 (K₁⟦1⟧)`. Under the shift identification this is exactly the
  scalar rescaling varpi^n. `IsIso φ.hom₁`, `IsIso φ.hom₂`, `IsIso φ.hom₃` retain
  the invertibility used for cone comparison; the triangle-morphism equations
  retain its commuting rescaling square and the signed rotated arrows.
- `filtration_model` quantifies over *every supplied* finite filtration and its
  supplied quotient models. The resulting K has a `FiniteConstruction` from
  exactly those models and realizes F in degree zero. It also supplies integral
  models W_j for every filtration term, starts at integral zero, ends at K up to
  isomorphism, and displays each W_(j+1) as a negative shift of an integral cone
  from the supplied quotient model to W_j[1]. Every W_j has a finite construction
  from that same supplied finite list.
- `sheaf_model` applies the stated conditional models assumption to every
  constructible F, returning both a supplied filtration and a finite integral
  model for F[0]. It is a separate explicit degree-zero conclusion.
- `bounded_model` quantifies over arbitrary C and integers a,b. `_bounded` is
  vanishing of H^r(C) whenever r<a or b<r, and `_constructible` applies to each
  cohomology sheaf. It returns the supplied filtrations indexed by `Set.Icc a b`,
  integral K, its finite construction solely from their quotient models, and
  `J(QK) ≅ C`.
- Its W has exactly `(b-a+1).toNat + 1` vertices, with the jth vertex realizing
  standard `tau_le(a-1+j) C`, the first integral vertex zero, and the last
  isomorphic to K. Each W_j is finitely constructed from the same quotient models.
  Every step supplies an integral model L for H^(a+j)(C)[-(a+j)], an integral
  distinguished cone of L -> W_j[1], and a comparison of its negative shift to
  W_(j+1). L itself has a finite construction from those same models. This is the
  specified finite standard truncation construction, including negative degrees.
- `FiniteConstruction` is a literal finite list ending at K. Each entry is zero,
  a shift of one supplied generator up to isomorphism, or a shifted distinguished
  cone between two strictly earlier entries. There is no retract or idempotent
  constructor and no infinite operation. These helper witness declarations belong
  to this node's own finite-cone assertion, under the permitted same-notion helper
  rule; they do not introduce an independent mathematical notion.
- `acyclic_model` gives an integral zero object realizing C when all its
  cohomology vanishes. It requires neither an interval nor a nonempty filtration.
  Full faithfulness is not needed for this special zero case.

Dependency declarations read and used (the first column is the DAG dependency):

| Node | Module and declarations |
| --- | --- |
| def-constructible-stratification | `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`: `Topology.FiniteLocallyClosedStratification`, `Scheme.FiniteLocallyClosedStratification` |
| def-pur-sheaf-tensor-product | `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: `SheafOfModules.cochainModulesMonoidal` and its existing sheafified tensor |
| def-sbc-standard-tstructure-derived-category | `Mathlib.Algebra.Homology.DerivedCategory.TStructure`: `DerivedCategory.TStructure.t`; `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT`: `TStructure.truncLE` |
| def-weil-abstract-derived-category | `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q` |
| def-weil-derived-cohomology-sheaves | `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`: `DerivedCategory.homologyFunctor`, `homologyFunctorFactors` |
| def-weil-l-adic-coefficient-extension | `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`; imported `coefficientExtensionIntegers`, `coefficientExtensionUniformizer` |
| def-weil-pbc-adic-coefficient-datum | `Sheaf.Paper.AdicCoefficientDatum`: `Scheme.completedReductionTower`, the actual completed ring, quotient system and normalized reductions |
| def-weil-pbc-bounded-constructible-complete | `Sheaf.Paper.IntegralUniformCoefficient`: `Scheme.pbcBoundedConstructibleComplete`; its imported general `PbcBoundedConstructibleComplete` specialized by `pbcIntegralDatum` |
| def-weil-pbc-continuous-constructible-module | `Sheaf.Paper.ContinuousConstructibleModule`: `ProEtale.IsContinuousConstructible` and the continuous-module constructions; rational local freeness is stated in the field form used by the realization record |
| def-weil-pbc-proetale-site | `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology` |
| def-weil-pbc-rational-category | `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory`, `pbcRationalization`; unchanged object and Hom-tensor localization |
| def-weil-sheaf-of-modules-category | `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`; existing `SheafOfModules` used through `pbcModules` |
| lem-per-rational-module-realization-functor | `Sheaf.Paper.RationalModuleRealizationFunctor`: `Scheme.RationalModuleRealization` and `rationalModuleRealizationFunctor`; all input normalizations retained through the record |
| lem-per-rational-stratum-integral-models | `Sheaf.Paper.RationalStratumIntegralModels`: `ProEtale.RationalStratum.exists_filtration_integral_models`, `IsCompletedModel`, `piece`, `IsNormalizedComparison`; supplied integral degree-zero quotient models are the hypothesis packaged by `Filtration` |
| def-kun-truncations (proof) | `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`: existing complex and derived good truncations described by its module docstring |
| def-weil-triangulated-category (proof) | `Mathlib.CategoryTheory.Triangulated.Pretriangulated`: `Pretriangulated`, TR1/TR2/TR3 |
| lem-sf-derived-ses-triangle (proof) | `Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle`: `ShortComplex.ShortExact.singleTriangle_distinguished` |
| lem-sf-triangle-morphism-iso (proof) | `Mathlib.CategoryTheory.Triangulated.Pretriangulated`: `isIso₃_of_isIso₁₂` (the needed position of the recorded two-of-three result) |
| lem-weil-pbc-truncation-triangle (proof) | `WeilConjectures.CategoryTheory.TruncationTriangle`: `DerivedCategory.truncation_triangle` |
| lem-weil-pbc-uniform-complete-triangulated (proof) | `Sheaf.Paper.PbcUniformCompleteTriangulated`: `Scheme.pbcIntegralUniformComplete_isTriangulated` |

Every statement-dependency module is publicly imported; proof-only dependencies
are imported without `public`. The generic specialization of the integral
category is the one already used by the recorded realization and stratum models,
not a new definition. No dependency node record is changed.

Edge cases checked before writing and again against the signatures: empty X;
zero objects and zero sheaves; n=0 in a fraction; zero connecting arrow; filtration
length 0 (Fin 0 for quotients and one zero vertex) or 1; zero quotient models and
intermediate zero cohomology; a=b; negative a and b; intervals larger than the
cohomological support; and a>b, when the vanishing hypothesis forces C acyclic and
the tower has one zero vertex. Only α is unique, since f and n are not. The shifted
cone is D[-1], with the original triangle rotated twice. The field is a genuine
finite extension of Q_l, so varpi is nonzero and its rational image is invertible.
No reducedness, connectedness, positive rank or nonempty-support condition was added.

Searches for an existing statement:

- `msearch.py ... leansearch`, query "Full faithful scalar localization realizes
  finite extensions and bounded constructible complexes using integral mapping cones":
  eight hits on generic scalar localization, module finite presentation and linear
  extension, no match for the present compatible-integral and continuous-rational
  finite-cone assertion.
- `msearch.py ... leanfinder`, query "A fully faithful rational realization lifts
  connecting morphisms to integral fractions and constructs bounded constructible
  complexes by finite integral cones": eight hits on fully faithful condensed
  locally constant functors and extension of complexes, no exact statement.
- `msearch.py ... loogle`, query `CategoryTheory.Functor.essImage`: twelve hits;
  Mathlib's essential image and its isomorphism closure are reused.
- `msearch.py ... grep`, query `essImage.*(Extension|Triangulat)` in CategoryTheory:
  three hits, notably `Mathlib/CategoryTheory/Triangulated/Subcategory.lean:727`.
  Read the generic full triangulated functor image instance; it supplies image
  closure but none of the integral fraction, rescaling, finite supplied-filtration
  or bounded truncation witnesses, so it does not state the full node.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  for the item id and proposed names: no existing declaration. `grep -rn` for the
  item id in `lean/WeilConjectures`: no match. Concept searches for finite cones
  found `CoefficientHeartGeneration` and `CoefficientHeartSheafConeWitness`, which
  concern internal condensed-ring module categories and arbitrary coefficient-heart
  generation; their finite-witness helpers are private. Read these and the generic
  image theorem in `ContinuousConstructibleIntegralImage`: neither supplies the
  actual completed integral raw-rationalization models stated here. No notion from
  them was copied as a second coefficient construction.

No STATEMENT-DISPUTED flag, node fault, new node, or dependency repair is needed.
Validation uses only the prescribed scompile.py and deliver2.py wrappers. The module
has compiled cleanly as both the sandbox module and its final library module path;
all theorem proofs remain `sorry` as required at stage 2. The delivery dry run passed server preflight and compilation (dry-run commit
`bfb515cef53`). Only the item node, its single module and this worker report are
staged. The node differs from the read-only source only in its `lean` record.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
