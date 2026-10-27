## Worker report

The module `Sheaf.Paper.CartesianScalarTensorSquare` states
`AlgebraicGeometry.Scheme.cartesianScalarTensorSquare`. Its proof is `sorry`.
The additional named theorem `cartesianScalarTensorRepresentative_naturality`
is the representative-naturality clause of this same node. It also has proof `sorry`.
Every other declaration is a complete definition of a comparison, a normalization
predicate, or a transparent specialization of a dependency. No object is chosen
from an undetermined existence assertion. There are no new nodes or dependency repairs,
and the mathematical statement is unchanged.

Hypothesis and clause correspondence:

- Arbitrary schemes and morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  There are no properness, separatedness, finiteness, or boundedness hypotheses.
- Small pro-etale sites: the original `X.ProEt`, `Y.ProEt` and `ProEt.topology`.
  Object universe is `u+1`, morphism universe is `u`; coefficients and module
  sections are in `u+1`. The standard derived localization has Hom universe `u+2`.
  The site Hom universe has not been identified with its object universe.
- Four coefficient sheaves and ring maps: `RY`, `SY`, `RX`, `SX`, `aY`, `aX`.
- Cartesian ring identifications: `cR` and `cS` use the actual
  `proEtaleSheafInverseImage`. The binder `comm` is exactly
  `cR.hom ≫ aX = inverseImage.map aY ≫ cS.hom`.
- Module categories and ordinary unbounded derived categories are the existing
  `proEtaleRingModules` and `DerivedCategory`; no completed or constructible
  subcategory is substituted.
- Scalar extension: `mY` and `mX` are the recorded universal
  `DerivedChangeOfRingsCochainModel`, with explicit site, coefficient, and
  localization universes. Their `E`, `T`, and `ε` are the actual ordinary
  extensions, their left derived functors, and their canonical cochain counits.
  Quantifying over presentations is independent of any choice of resolutions.
- Exact restriction: `cartesianScalarDerivedRestriction` is literally
  `proEtaleRingRestrictScalars.mapDerivedCategory`, with the existing exactness
  proofs supplied by `proEtaleRingRestrictScalars_preservesFiniteLimits` and
  `proEtaleRingRestrictScalars_preservesFiniteColimits`. No new exactness
  assumption is made. `cartesianScalarRestrictionFactors` is its existing
  canonical termwise factorization.
- The objects B are `cartesianScalarModule a`, restriction of the actual target
  regular module, placed in degree zero by `cartesianScalarComplex a` and Q.
- Derived tensor is the published `siteDerivedTensorIndependentCoefficients`,
  curried by the existing `KFlatFixedTensor.derivedTensor`.
  `cartesianScalarTensor` fixes its first input to QB. The definition
  `cartesianScalarTensorModel` packages precisely the existing representative
  isomorphisms; it does not choose another tensor or another normalization.
- The natural isomorphisms e are the existential witnesses `eY` and `eX`.
  Naturality for every derived arrow, including inverse quasi-isomorphisms,
  is part of their `NatIso` type. In diagrammatic order it reads
  `(T ⋙ U).map v ≫ e.hom.app A' = e.hom.app A ≫ tensor.map v`.
- Their representative normalization is explicit:
  `CartesianScalarOrdinaryNormalization` fixes j by `s ⊗ p ↦ s ⊗ p`, using
  the existing sheafification tensor pair. `CartesianScalarDerivedNormalization`
  says that e followed by the canonical tensor augmentation and the single-complex
  comparison is the scalar-model counit followed by termwise U and Q(j).
  The augmentation is from `ringedTensorAugmentation`; no K-flatness or
  flatness of B is presumed. On flat-term K-flat P that augmentation is
  invertible by the node's Step 1, so this is exactly its one-sided representative
  identification, with the prescribed direction.
- LR and LS are the existing exact `proEtaleRingDerivedPullback` for the two
  coefficient identifications. The b in the square is precisely
  `proEtaleRingRestrictionDerivedPullback`, and its inverse is used.
- The ordinary comparison chi is a natural isomorphism whose balanced generator
  formula is `CartesianScalarPullbackNormalization`. It uses the actual module
  adjunction units, the ring inverse-image unit, and cS. This formula fixes the
  inverse-image/scalar comparison on all unit generators and their restrictions;
  sheafification extends it to all sections. It does not assume every inverse-image
  tensor section is pure.
- The derived lambda is `lam`. `CartesianScalarLocalizedPullbackNormalization`
  identifies it with the localization of this same chi on every flat-term K-flat
  representative, via the actual model counits and exact pullback factors.
  This uniquely specifies the comparison with the normalization of
  `lem-sfb-kflat-scalar-comparison-normalization`; no arbitrary isomorphism
  of functors is used in its place.
- `CartesianScalarCoefficientNormalization` fixes the ordinary k on unit sections
  by cS; `cartesianScalarCoefficientIso` applies the exact termwise pullback factor,
  the existing pullback/single-complex isomorphism, and Q(single(k)). This is kappa.
- Mu is exactly `proEtaleCanonicalTensorComparison` applied to the two published
  tensor models. Its dependency fixes it by the ordinary total-tensor comparison.
- The final universally quantified equation, in Lean's left-to-right composition
  order, is
  `LR(eY⁻¹) ≫ b⁻¹ ≫ U_X(lam) ≫ eX = mu ≫ tensor(kappa,1)`.
  It holds for every `A` in `D(RY)`, so it is equality of the specified natural
  transformations on the entire derived category.
- `CartesianScalarOrdinarySquare` explicitly states equality of the two ordinary
  maps in each degree of every flat-term K-flat P. `cartesianScalarOrdinaryMap`
  is the exact composite `I(jY⁻¹) ≫ b0⁻¹ ≫ U(chi) ≫ jX`; the other map is the
  actual `proEtaleOrdinaryTensorPullback` followed by tensor(k,1). Their generator
  formula is `f⁻¹(s ⊗ p) ↦ cS(f⁻¹s) ⊗ f⁻¹p`, by the three normalization predicates.
  Every factor is a natural module comparison, hence the degreewise equalities are
  equality of cochain isomorphisms and commute with cochain maps. Localization
  also preserves those naturality equations and inverts quasi-isomorphisms.
- No flatness of aY or aX, no boundedness, and no projection-formula inversion
  is required anywhere in the signature or the normalization predicates.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`,
  its category, and `ProEt.topology`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction` (normalized adjunction
  of the existing universal extension).
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel`, its E, T, ε and computes fields.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`, through the recorded
  operations module: `proEtaleRingModules`, `proEtaleRingModulePullback`,
  `proEtaleRingDerivedPullback`, `proEtaleRingDerivedPullbackFactors`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`:
  `proEtaleRingRestrictScalars`, its two exactness theorems,
  `proEtaleRingRestrictionPullbackInv`, `proEtaleRingRestrictionDerivedPullback`.
- `Sheaf.Paper.KFlatScalarComparisonNormalization`:
  `SheafOfModules.ScalarPullback.kflat_scalar_comparison_normalization`;
  its generalized balanced normalization motivates the explicit scheme-specialized
  predicates. The main theorem is not forced through its equal-size site aliases.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, definition and specialization
  to `IsAcyclicTensorKFlat`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, through
  `Sheaf.Paper.ProEtaleCanonicalTensorPullback`: `ProEtaleTensorModel`,
  `proEtaleTensorPair`, `proEtaleOrdinaryTensorPullback`,
  `proEtaleCanonicalTensorPullback`, `proEtaleCanonicalTensorComparison`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` (the same sheafified tensor).
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `SheafOfModules.siteDerivedTensorIndependentCoefficients`.
- `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`:
  `ordinaryTensor`, `totalTensor`, `derivedTensor`, `representativeIso`.
- `Sheaf.Algebra.Homology.RingedDerivedTensorAugmentationNaturality`:
  `SheafOfModules.ringedTensorAugmentation`.
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle`:
  `CochainComplex.map₂HomologicalComplexObjSingleIso`.

The two convention-only nodes supply universe and scheme conventions and have no
object declaration. All stated proof dependencies are imported. The proof dependency
`lem-sfb-ringed-pullback-derived-ordinary-tensor` is not yet stated in the current DAG,
so there is no module to import for it; its natural-language proof obligation is
retained in the main docstring. Mathlib exact-functor factorization and localization
universal-property dependencies are imported directly as proof infrastructure.

Edge cases checked mathematically before writing: identity f and identity coefficient
maps give the unit normalized square; zero coefficient sheaves and the empty scheme
remain allowed; nonflat Z -> Z/2 (and a flat-term complex with multiplication by 2)
is permitted because B is never assumed flat; zero complexes and arbitrary unbounded
P are included; degree 0 and all integer degrees use the existing single-complex and
signed total constructions, so no positive-degree or boundedness restriction appears.
No disputed statement or source correction was needed.

Searches for an existing declaration:

- `msearch.py` LeanSearch query: "Restriction of derived extension of scalars of
  sheaves of rings equals tensor with the restricted target ring and commutes with
  cartesian inverse image". Eight results, including `SheafOfModules.restrictScalars`
  and ordinary module restriction constructions; no normalized derived square.

- `msearch.py` LeanFinder query: "Restriction of derived scalar extension is tensor
  with the restricted target ring, compatible with cartesian inverse image".
  Eight results: ring tensor restriction and ModuleCat scalar-adjunction formulas;
  none states the ring-sheaf unbounded cartesian square.
- `msearch.py` Loogle query:
  `SheafOfModules.restrictScalars, SheafOfModules.pullback`: zero hits.
- `msearch.py` Mathlib grep:
  `restrictScalars.*[Tt]ensor|[Cc]artesian.*[Ss]calar`: 25 hits in ordinary
  algebraic tensor restriction; no sheaf-derived square.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for cartesian/scalar/tensor-square
  names and this blueprint id. Related constant-coefficient or internal-module
  results are not the arbitrary four-ring-sheaf statement. In particular
  `ConstantScalarPullbackSquare`, `IntegralResidueOrdinaryTensorNormalization`
  and `ProEtaleScalarMateNormalization` have different coefficients or categories.
- The source for Tag 03EL and Tag 0FPH was read locally, as was the current blueprint
  ancestor `lem-sfb-dc-lower-star-preserves` in `literature/blueprint/latest`.

Compilation uses scompile.py exclusively. The full module passed both the sandbox
and library checks with no errors and no unexpected warnings. Every definition has
real data and every universe is explicitly bound. The final delivery dry run and
push are performed by the prescribed deliver2.py tool.

## Second reading by NU

This section records the worker's final self-check, not an invented independent reader.
The user assigns the independent review to the maintainer. No subagent was started.
I checked the two routes' endpoints and composition directions against the node,
verified the action comparison is b inverse, and checked that j is oriented from
restricted extension to B tensor -. I checked the augmentation normalization uses
B[0] even for nonflat B, and that the ordinary-square clause is present in addition
to the derived equation. The compiler required explicit scalar-model universes and
explicit existing restriction exactness proofs; both were supplied without mathematical
hypotheses or statement changes. The final representative comparison has its actual
published components, rather than an arbitrary natural isomorphism.

## Maintainer review fix (2026-10-24)

`CartesianScalarDerivedNormalization` used `SheafOfModules.ringedTensorAugmentation`, a
definition that is owned by the theorem node `lem-sfb-ringed-derived-tensor-augmentation-naturality`
(a proof dependency of this item, not a statement dependency). The predicate is now stated
inline. For every flat-term K-flat resolution `r : V ⟶ B[0]` and flat-term K-flat `P`:
`c(V,P)⁻¹ ≫ Q(total(r,1) ≫ single-iso) = D(Qr) ≫ e⁻¹ ≫ U(ε_P) ≫ factors ≫ Q(j_P)`.
Here `c` is the published `representativeIso` and `D` the derived tensor of `Q r`. By the ∃!
characterization of the augmentation (value `c⁻¹` on flat-term K-flat pairs, naturality along
resolutions), this is equivalent to the former equation, and it pins `e` on every `QP` in the same way.
The import of the augmentation module is now a plain proof-dependency import.
The main theorem's signature is unchanged.
