## Worker report

Q49 states `lem-sf-locally-finite-adic-constructible-realization` in
`Sheaf.Paper.LocallyFiniteAdicConstructibleRealization`. The sole postponed theorem is
`WeilConjectures.LocallyFiniteAdicRealization.locally_finite_adic_constructible_realization`.
It asserts the existence of a normalized ordinary realization, with no proof supplied.
Its docstring gives the node's complete eight-step natural-language proof. All helper
definitions have actual data. The structures package the conclusion and its normalized
maps; they introduce no extra hypothesis on the scheme or coefficient field.

The previous dispatch result confused the reviewed Q48 stage-1 split with a Lean delivery.
The live item has `reviewed`, but no `lean` attachment. Q48's report concerns splitting.
Thus this is the first stage-2 attachment, not a duplicate delivery.

Clause-by-clause reading follows. `Realization` extends `RealizationCore` and additionally requires the explicitly defined
`commonField` equation. References to its data below include these inherited fields.
All names below without another namespace are in
`WeilConjectures.LocallyFiniteAdicRealization`.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A finite field k₀ and its specified algebraic closure k | `(k₀ k : Type u) [Field k₀] [Finite k₀] [Field k] [Algebra k₀ k] [IsAlgClosure k₀ k]` |
| A prime l different from the characteristic | `(l : ℕ) [Fact l.Prime] (hl : l ≠ ringChar k₀)` |
| Every finite-type k-scheme T | `T : Over (Spec (CommRingCat.of k))`, with `[LocallyOfFiniteType T.hom] [QuasiCompact T.hom]`; no separatedness binder |
| Ω = algebraic closure of Q_l | `PadicAlgCl l`, the native framework's coefficient field |
| The small pro-etale site | `Scheme.ProEt.topology T.left`, with the existing object and morphism universes retained |
| B_T consists of continuous functions whose values locally have finite Q_l-span | The actual published `ProEtale.adicConstantSheaf l X`. `abRing` forgets only the constant-field module structure; `ringSheaf` is its sectionwise commutative ring presentation, retaining the same underlying locally finite functions |
| Native internal B_T-module convention | The target ambient category is literally `DerivedCategory (ProEtale.AdicSheaf l X)`, not a newly defined module category. `sections` is the canonical forget-to-abelian-internal-modules functor followed by the published section-module equivalence |
| Bounded cohomology | First conjunct of `targetProperty`: `∃ a b : ℤ, K.IsGE a ∧ K.IsLE b` |
| Constructible cohomology in every degree | Second conjunct of `targetProperty`: `∀ n : ℤ, ProEtale.IsAdicConstructibleSheaf ((DerivedCategory.homologyFunctor _ n).obj K)` |
| Locally finite free on finite locally closed stratifications, locally on T | This is exactly the recorded native `IsAdicConstructibleSheaf`: open neighborhoods have `IsAdicStratifiedLisseSheaf`; its finite disjoint constructible immersion strata have `IsAdicLisseSheaf`, trivialized by pro-etale covers as finite sums of the native coefficient unit. Finite-type T is Noetherian, so the constructibility condition on strata adds no restriction |
| Full bounded constructible target category C_T | `(targetProperty l X).FullSubcategory`; the inclusion in the ambient derived category is full by construction |
| Ordinary common finite-field source and its Hom colimits | `generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X`, exactly the recorded literal pair category, its filtered common-field Hom groups and their published shifts and triangles |
| Bounded constructible finite Tor source at field coefficients | The dependency's `finiteTorFieldCoefficientCategory C := C` identifies this same field-coefficient source; no extra integral finite-Tor predicate is imposed |
| Raw rationalization at every finite E | The actual `sfRationalConstructibleCategory` in every `GeneralAlgebraicallyClosedCoefficients.Stage`, and `sfRationalConstructibleLocalization` in `Realization.integral`; no Karoubi envelope or new stage category |
| B_{T,E} is the inverse limit of constant finite quotient sheaves | `completedIntegralCommRingSheafUnrestricted l (Coefficient l Ω E) X`. `CoefficientPresentation.integral`, `.finite`, `.finite_constants`, and `.integral_residues` fix its identification with continuous integral functions by all quotient projections. The existing index n represents exponent n+1, cofinal among the positive powers |
| E_T = B_{T,E}[1/varpi_E] | `.localization` and `.localization_normalized` identify the published actual `integralCoefficientLocalization` with continuous rational coefficient functions, preserving the localization numerator and denominator formula |
| Canonical map E_T to B_T | `.integralInclusion` is normalized by `integralRationalCoefficientNormalized`; `.rationalInclusion` is fixed on every section and point by `.rationalInclusion_normalized`, using `embedding` to undo the published coefficient-size Shrink. Thus it is postcomposition with the specified finite subfield inclusion |
| Structural B_{T,E} to B_T map | `CoefficientPresentation.integralMap` is the actual composite of the inverse completion identification, integral inclusion and finite-field inclusion |
| Realization formula on integral representatives | `Realization.integral` is a natural isomorphism from localization, inclusion and J (read through the canonical `sections` functor) to `pbcDerivedExtend integralMap` on the intrinsic integral constructible category. This is the universal derived sheaf tensor extension with its fixed ordinary tensor objects/maps and K-flat counit |
| Scalar extension on integral morphisms | Naturality of `Realization.integral` holds for every integral derived arrow, not just maps of sheaves or chosen complexes |
| Same inverse uniformizer power on a fractional morphism | The source is the existing raw scalar localization. Multiplication by a uniformizer on an object is an integral arrow; its localized inverse is precisely the denominator arrow. Functoriality preserves that inverse, while integral naturality fixes its numerator and its uniformizer action. No arbitrary separate fraction operation is supplied |
| Common-field passage by balanced scalar extension | `coefficient_scalar` is the square for the actual quotient-normalized `completedCoefficientMap`. `common_field : commonField l X toRealizationCore` equates the realized canonical `StageSystem.isoToStage` with: the integral comparison, inverse canonical `pbcReductionNormalization`, derived extension of the specific `completedScalarComparison`, then inverse integral comparison at L. The concrete helper `completedTensorComparison` is exactly that published map with the canonical derived-tensor signature. The latter completion map is characterized on good complexes by the finite-quotient completion chain map. `pbcReductionNormalization` is fixed by the actual tensor units, flattens b tensor (s tensor k) to bs tensor k, and its inverse inserts one. HEq accommodates the recorded literal-object equalities of the opaque stage system; it does not choose an unspecified comparison |
| Ordinary triangulated equivalence | `Realization.J` is an ordinary category functor with additive and integer-shift structures and `J.IsTriangulated`. `fully_faithful` and `image` give a fully faithful, essentially surjective functor onto the full C_T. These are precisely the data asserting the claimed triangulated equivalence |
| Full faithfulness on derived morphisms | `fully_faithful` says `Function.Bijective J.map` for all pairs of source objects, with codomain the Hom in the full ambient derived category. Shifted objects are included |
| Exactly the desired essential image | `image : ∀ K, targetProperty l X K ↔ ∃ A, Nonempty (J.obj A ≅ K)`; both inclusions are required |
| Both categories essentially small in the common site/coefficient universe | `sourceSmall` and `targetSmall` both use `EssentiallySmall.{u+1}`. The source size transport uses the published finite-field `Coefficient.{u}`; the native site still has objects in u+1 and morphisms in u |
| No individual finite E is asserted equivalent to C_T | Full faithfulness and essential image are asserted for J on the complete common-field pair category; finite-stage functors occur only in its normalization |

Dependency declarations read and used:

- `def-sf-native-weil-derived-framework`, recorded entry module
  `WeilConjectures.WeilSheaf.LowerShriek`: `AlgebraicGeometry.ProEtale.AdicSheaf`,
  `adicConstantSheaf`, `IsAdicConstructibleSheaf`, `IsAdicStratifiedLisseSheaf`,
  `IsAdicLisseSheaf`, and `PadicAlgCl.locallyFiniteFunctions`. Their full definitions
  and docstrings were read in the imported native adic framework.
- `def-weil-algebraically-closed-coefficients`,
  `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `WeilConjectures.generalAlgebraicallyClosedConstructibleCategory` and namespace
  `GeneralAlgebraicallyClosedCoefficients`'s `Stage`, `inclusion`, `stageSystem`,
  `integralTransition`, and normalized scalar associators.
- `def-weil-finite-tor-amplitude`, `Sheaf.Paper.FiniteTorAmplitudeSites`, publicly
  importing `Sheaf.Paper.FiniteTorAmplitude`:
  `WeilConjectures.finiteTorFieldCoefficientCategory`, whose field specialization
  is the identity alias; its integral and torsion predicates were not substituted.
- `def-weil-rationalization-karoubi`, `Sheaf.Paper.SfRationalizationKaroubi`:
  `WeilConjectures.sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, and the normalized scalar-transition
  object and tensor-Hom specifications.
- `def-weil-size-convention` is the recorded convention, not a Lean declaration.
  All variables and universes are explicitly bound; `autoImplicit` is disabled.

Additional presentations use existing canonical interfaces, not duplicate notions:
`ProEtale.AdicSheaf.forgetAb` and `weilCoefficientsForgetAb` from
`WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafForgetAb`;
`InternalAbelianSheafModule.sectionRingSheaf` and `sectionModuleEquivalence` from
`Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`;
continuous coefficient constructions from
`Sheaf.AlgebraicGeometry.ContinuousCoefficientBasic`;
`pbcDerivedExtend` and `pbcReductionNormalization` from
`Sheaf.Paper.BoundedConstructibleTower`; and `completedCoefficientMap` and
`completedScalarComparison` from `Sheaf.Paper.FiniteFreeCompletedScalarComparison`.
The remaining plain imports are the recorded proof-dependency modules for the eight
steps of the future proof. No dependency node is restated or rebound.

Sources opened: the current blueprint's
`sec-six-functors/sk-thm-sf-package/cor-coef-verdier-weil-equivariance.proof.md`,
and the local Bhatt--Scholze PDF, especially Lemma 6.8.2, Definitions 6.8.3/6.8.6/6.8.8
and Proposition 6.8.14. The extracted PDF text is only scratch material in the sandbox.
The native locally finite specialization and essential-smallness addendum are the
node's explicitly agent-formulated obligation, as its source record states.

Edge cases checked before stating: empty T (constructibility and image have their
usual zero-category meaning); zero complexes and rank zero (empty finite sum is
allowed); arbitrary integer cohomological intervals; finite coefficient exponent
one (index zero means power one, not quotient by the zeroth power); identity and
repeated coefficient fields; ramified finite inclusions (the published completion
comparison uses the two cofinal uniformizer filtrations); morphisms between unequal
stages (canonical isoToStage and Hom-colimit representatives); non-separated T
(no separatedness condition enters the signature); and non-quasi-compact test objects
(the native coefficient remains locally finite, never globally bounded in one finite
field). Prime l excludes 0 and 1; the exact characteristic exclusion is retained.

Searches made for an existing exact statement or definition:

- `msearch.py ... leanfinder`, query: "Ordinary bounded constructible algebraic l adic
  complexes as common finite coefficient field category equivalent to derived modules
  over locally finite continuous algebraic l adic functions". Returned generic
  condensed-module results, none the ordinary native realization assertion.
- `msearch.py ... loogle`, query:
  `AlgebraicGeometry.ProEtale.AdicSheaf, WeilConjectures.generalAlgebraicallyClosedConstructibleCategory`.
  No matches; the service did not know the project's native identifier.
- `msearch.py ... grep`, query
  `locallyFiniteFunctions|AdicSheaf|rational.*realization`, subdirectory `CategoryTheory`.
  No Mathlib match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for native adic modules,
  locally-finite functions, rational realization and common-field scalar extension
  found the component interfaces listed above, not the entire assertion.
- `grep -rn` for the exact node ID in `lean/WeilConjectures` found no declaration.
  The related DAG node `lem-sf-adic-qbar-constructible-realization` has no Lean
  attachment and concerns separated T with additional monoidal conclusions; it
  does not already supply this statement.

No statement correction, disputed statement, new independent node or dependency
repair was necessary. All owning-node helper declarations are recorded in
`lean.declarations`. Only the item's `lean` field changes.

Validation: compile each delivered module through the prescribed `scompile.py`;
then run `deliver2.py --no-push` and repair its preflight and compilation findings
before the authorized delivery. The final delivery wrapper output records the
successful checks and commit.

## Second reading by Q49

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
