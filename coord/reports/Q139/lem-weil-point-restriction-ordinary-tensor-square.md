## Worker report

Item: `lem-weil-point-restriction-ordinary-tensor-square`.
Module: `Sheaf.Paper.PointRestrictionOrdinaryTensorSquare`.
Main declaration: `WeilConjectures.point_restriction_ordinary_tensor_square`.
Its only postponed proof is the main theorem, with the four-step DAG proof in its
docstring. The two chain-composite abbreviations have actual data; the proposition
packages the assertion with an existing derived-descent specification.
No new notion node, dependency replacement, or statement correction is needed.

Source read: the current blueprint's
`sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/def-weil-global-geometric-frobenius.md`,
and the item's agent-written four-step extraction and reviewed restriction calculation.
The explicit ordinary calculation is not attributed as a theorem to Deligne or
Bhatt--Scholze. The tensor is the sheafified tensor of Stacks 03EK.

Hypotheses and clauses, matched individually:

- `D : FiniteFieldDatum.{t}` is precisely the global finite-field datum, including
  the prime, positive exponent, cardinality and chosen algebraic closure `D.k`.
- `l`, `[Fact l.Prime]`, and `_hl : l ≠ D.p` give the coefficient prime and its
  required inequality. `Ω` with `Field`, `Algebra ℚ_[l] Ω` and `IsAlgClosure`
  gives the fixed algebraic closure of the l-adic field.
- `E L : IntermediateField ℚ_[l] Ω`, their two `FiniteDimensional` instances,
  and `h : E ≤ L` are the two finite coefficient fields and their actual inclusion.
  Valuation rings, chosen uniformizers and completed coefficient sheaves are the
  dependency constructions. No alternate coefficient sheaf or completion is used.
- `g : Spec (.of D.k) ⟶ Spec (.of D.k)` with `[IsIso g]` is any automorphism;
  no compatibility with `D.k₀` is requested. Inverse image is
  `inverseImageIntegralModules` / `inverseImageIntegralDerived`, whose action
  uses the inverse of the canonical completed coefficient structure map.
- `d : PointFiniteFreeSectionsTensorData ...` supplies the recorded normalized
  coefficient identifications and ordinary comparison. This is presentation data
  supplied by the dependency theorem, not a restriction on a module or complex.
  Similarly, `b`, `β`, `_hb : CompletedFormula ... b` and
  `_hβ : DerivedModel ... b β` specify the very comparisons introduced by the
  K-flat-model dependency. They are not arbitrary maps substituted for them.
- Site objects remain in `Type (t+1)` with morphisms in universe `t`; module size
  is `max u (t+1)`. The two module-localization universes `wE` and `wL` are
  independent. `HasDerivedCategory` chooses presentations and adds no mathematical
  existence restriction (the standard presentation always exists).
- `pointRestrictionOrdinaryTensorSquare` takes the recorded
  `dd : PointDerivedSectionsTensorData d`. Its existing exactness assertions ensure
  sections are termwise sections localized at quasi-isomorphisms; its existing
  `theta`, `theta_eq`, `localized_representative`, `comparison_counit`, and
  `resolution` fields fix exactly the ordinary derived sections-tensor map.
  No new theta definition is introduced.
- The first two conjuncts prescribe every component of `sigmaE`, `sigmaL`
  as `pointRestrictionRaw ... none`, the restriction/coprojection of the
  dependency. They merely use the unlifted integral scalar convention of `d`,
  instead of the canonically equivalent ULift convention of the restriction module.
  The underlying functions and transported module actions are the same.
- The next two conjuncts prescribe the derived sigma
  transformations by localization of the termwise chain maps. They explicitly
  include the canonical inverse-image and sections factorization isomorphisms.
  As natural transformations they are natural on every derived morphism.
- The next conjunct is the displayed equality: Lean composition reads left to right, so
  `T.map (tauE.app H) ≫ theta.app (G_E H) ≫ Γ_L.map (β.app H)` equals
  `theta.app H ≫ tauL.app (C H)`. It quantifies over every object of the
  unbounded `DerivedCategory (integralTowerModules ...)`.
- `pointRestrictionTensorLeft` is sigma tensor one, theta on `G_E P`, then
  sections of `b_P`; `pointRestrictionTensorRight` is theta on P then sigma
  on its ordinary scalar extension. These are actual composed chain maps.
  The chain-equality conjunct equates them for every object of `integralOperationsGoodComplex`,
  exactly flat-term K-flat complexes, hence for every such resolution of H.
- The pure-tensor conjunct quantifies over every such P, every integer degree n, every
  `x ∈ P^n(U)` and `a ∈ O_L`. It sends the source tensor to
  `completedScalarTensorSection ... V (res_g (d.coefficientL a)) (res_g x)`.
  Here `V = (Scheme.proEtaleIsoPostcompose g).obj (ProEt.mk (𝟙 _))`,
  and `pointRestrictionArrow g : V ⟶ U` is the actual restriction arrow.
  The canonical sectionwise inverse-image coordinates identify this with the
  target section at U. Mathlib change of rings writes the scalar first, so
  `a ⊗ₜ x` represents the node's `x ⊗ a`; the tensor is the same balanced tensor.
  The explicit `@id ((sectionsE d).obj ...) x` fixes the existing constant scalar
  action on that tensor input; it does not cast to a new object or change x.
- The final conjunct is `res_g(a_s) = c_L⁻¹(a_s)` with precisely
  `inverseImageCompletedCoefficientMap`. Since `sigma_raw` is restriction in
  the canonical evaluation coordinates, this is the node's coefficient equation.
- Independence from the resolution is retained by the recorded `dd.resolution`
  equation, the two tau localization equations, and the assumed dependency's
  `DerivedModel` normalization of b. The chain square holds for every good P,
  and the derived square for every H using the same normalized transformations.
  No chosen resolution, boundedness, constructibility or derived completeness
  is a hypothesis. No target section is assumed to be a sectionwise tensor;
  `completedScalarTensorSection` explicitly passes through sheafification.

Dependency declarations read and reused (recorded modules, including reexports):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `def-weil-scheme-morphism-properties` is the recorded convention node with
  no declaration of its own; the automorphism uses Mathlib `Scheme` and `IsIso`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public
  `CoefficientExtension`: `Padic.finite_coefficientExtensionRing`,
  `coefficientExtensionIntegers`, `coefficientExtensionUniformizer` and quotients.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, reexporting the recorded
  `completedIntegralCoefficientSheafUnrestricted` and commutative version.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`, with its public
  `Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison`:
  `inverseImageIntegralModules`, `inverseImageIntegralDerived`, and
  `inverseImageCompletedCoefficientMap`.
- `Sheaf.Paper.PointProEtaleSectionsExact`: `pointModuleSections` and
  `point_proEtale_sections_exact` (proof dependency).
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, the transparent
  Mathlib `SheafOfModules` alias; the dependency APIs use that very module category.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and the localization functor `DerivedCategory.Q`.
- `Sheaf.Paper.IsomorphismScalarTensorKFlatModel`:
  `IsomorphismScalarTensor.leftComplex`, `rightComplex`, `inverseComplex`,
  `CompletedFormula`, `DerivedModel`, `isomorphism_scalar_tensor_kflat_model`.
- `Sheaf.Paper.PointDerivedSectionsTensorDescent`: `sectionsE`, `sectionsL`,
  `PointDerivedSectionsTensorData`, `point_derived_sections_tensor_descent`.
- `Sheaf.Paper.PointAutomorphismRestrictionNatural`: `pointRestrictionRaw`,
  `pointRestrictionArrow`, `pointRestrictionCoefficientMap`,
  `point_automorphism_restriction_natural`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients` (proof dependency).
- `Sheaf.Paper.PointFiniteFreeSectionsTensor`: `PointFiniteFreeSectionsTensorData`,
  `pointFiniteFreeFinal`, `pointFiniteFreeModuleTensor`, and the ordinary complex
  comparison; its `CompletedIntegralScalarData` reexports
  `completedScalarTensorSection`, `completedOrdinaryScalarExtension`, and
  `completedDerivedScalarExtension`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: existing
  `SheafOfModules.cochainModulesMonoidal` and tensor sheafification infrastructure.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`,
  `toSheafify`, and `sheafificationAdjunction` (proof dependency).

Edge cases checked before writing: E=L (identity inclusion remains allowed), g=id,
H=0, arbitrary integer degrees and unbounded H. There is no extra prime assumption
excluding l=2 or positive characteristic p. There is no nontriviality or resolution
surjectivity hypothesis on H. The full good-complex category includes every flat-term
K-flat resolution, not just a chosen one. All exactness data are in the result. The square predicate binds only the
existing proof instances from dd internally; its signature and the theorem have no
let-bound objects or hidden have-bound constructions.

Searches made:

- `msearch.py ... leanfinder`: “The global sections tensor comparison commutes
  with restriction along a scheme automorphism and the canonical inverse image
  tensor comparison”. Eight results: scheme pullback tensorCongr and Spec-global-
  sections naturality; none states this completed-coefficient ordinary derived square.
- `msearch.py ... loogle '"tensorObj_map_tmul"'`: one result,
  `PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul`. This is a presheaf
  ingredient, not the statement with sheafification, inverse-image action and descent.
- `msearch.py ... grep 'sectionsTensor|ΓRes_naturality' CategoryTheory`:
  `Sheaf.ΓRes_naturality` and its use in GlobalSections; neither gives the square.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for
  `point_restriction_ordinary_tensor|restriction.*tensor.*square|tensor.*restriction.*square`:
  only unrelated open-restriction, stalk, and other tensor squares. No exact match.
- `grep -rn` for the item id in `lean/WeilConjectures`: no declaration.

No statement dispute, source error, or DAG change beyond the `lean` record.

## Second reading by Q139

No second reading by a worker: the dispatcher brief forbids starting other agents;
the maintainer's independent review is the independent reading. The hypothesis and
clause mapping above is the author's check, not an independent review.
