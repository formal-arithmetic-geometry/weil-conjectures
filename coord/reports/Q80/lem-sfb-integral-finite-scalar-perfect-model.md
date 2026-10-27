## Worker report

Delivered module: `Sheaf.Paper.IntegralFiniteScalarPerfectModel`.
Main declaration: `AlgebraicGeometry.ProEtale.IntegralFiniteScalar.integralFiniteScalarPerfectModel`.
It states the given integral-to-finite perfect-resolution assertion. The only postponed
proof is the main theorem (`sorry`); its docstring contains all nine DAG proof steps.
The helper definitions contain actual functors, complexes, morphisms, isomorphisms,
and transparent conditions. They do not choose data from a postponed existence proof.

The source read was the current
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-direct-image.proof.md`,
including both the integral-to-finite paragraph and the formal-properties paragraph.
There is no source-based statement correction and no STATEMENT-DISPUTED flag.

Hypotheses and clauses, in the namespace of the main declaration:

- Prime ell: `(ell : ℕ) [Fact ell.Prime]`.
- Finite extension E/Q_ell: `[Field E] [Algebra (Padic ell) E]`
  and `[FiniteDimensional (Padic ell) E]`.
- The specified integer ring and valuation topology:
  `Padic.coefficientExtensionIntegers ell E` and the explicit
  `Padic.coefficientExtensionIntegersTopology ell E`; the topological-ring instance is
  `spectralNorm.normedField (Padic ell) E` followed by
  `inferInstanceAs (IsTopologicalRing (Padic.coefficientExtensionIntegers ell E))`,
  inlined in the signature. No arbitrary topology is assumed.
- Finite discrete commutative A: `[CommRing A] [Finite A] [TopologicalSpace A]`
  `[DiscreteTopology A]`. The unital scalar homomorphism is a `RingHom`, and `ha` is
  continuity from precisely the integer-ring topology.
- Killed by a power of ell: `_hpow : ∃ n : ℕ, (ell : A) ^ n = 0`.
  In a unital ring this is equivalent to that scalar annihilating A.
- The canonical pullback/scalar comparison is supplied by
  `D : ScalarSixPullbackData`. This is the recorded, normalized interface of
  `det-prop-scalar-six-pullback`: `thetaNormalization` fixes its homomorphism to the
  scalar-adjunction mate. The theorem works for every such canonical data, whose
  existence is already stated by `scalarSixPullback`; no new geometric hypothesis is
  imposed and no arbitrary comparison is substituted.
- `condensed O`, `condensed A`, and `condensedMap a ha` bundle the existing continuous
  coefficient ring objects. The map uses the recorded definition
  `Profinite.continuousMapRingObjMapOfUniverse`, transported by definitional equality
  to these objects, with `isMonHom_continuousMapRingObjMapOfUniverse` certifying it
  preserves multiplication and the unit. `pointPull` is
  `(sfbPullbackFromPoint Z).mapMod`, and `coefficientMap` is the point-induced a_Z.
- The assertion `PerfectModel` installs `a.toAlgebra` and its continuous scalar action
  to give exactly the specified O-module structure on A. It existentially supplies
  `r : ℕ`, the continuous O-linear maps q and phi, surjectivity of q, injectivity of
  phi, and `Function.Exact phi q`. Its matrix clause gives
  `φ x = M.mulVec x` for an actual square `Matrix (Fin r) (Fin r) O`.
- The coordinate module is the existing `Profinite.continuousSectionsModule O
  (Fin r → O)`, with an isomorphism to the finite biproduct of r regular modules.
  The point arrows F and G are fixed by their formulas on every profinite S and
  every continuous section v, namely postcomposition by phi and q. The equation
  `h : F ≫ G = 0` builds the specified `ShortComplex`. Its quotient is identified
  with restricted regular A by `t`, whose underlying sheaf homomorphism is the
  identity. The sequence is asserted `ShortExact`.
- `complex` is degreewise point pullback of `CochainComplex.monoCokernelComplex S.f`.
  This is the standard cone of the degree-zero map, in degrees [-1,0], with
  differential +phi. `target` is point pullback of the degree-zero quotient complex.
  `augmentation` is the actual pulled-back `monoCokernelAugmentation S`, so it uses q.
  `targetZeroIso` uses t, the canonical single-complex identification, and the
  existing mapMod/comap and mapMod/unit comparisons; its target is restricted A_Z.
- `DerivedAssertions` asserts `QuasiIso (augmentation ... Z)` for every scheme Z.
  K-flatness is stated using the dependency's exact
  `CochainComplex.IsKFlatIndependentCoefficients` after the recorded termwise
  internal-to-section module equivalence, retaining the site universes u+1 and u.
- For every complex C, without any boundedness or flatness restriction, it asserts
  invertibility of `Functor.LaxMonoidal.μ DerivedCategory.Q P C`. Its codomain is
  the localization of `HomologicalComplex.tensorObj P C`, the existing signed
  direct-sum total tensor of the tensor-complex dependency. This is the canonical
  one-K-flat representative computation, also for a representative C equipped with
  any isomorphism `Q C ≅ K` by tensoring that isomorphism.
- The beta family is a natural isomorphism
  `tensorLeft (Q.obj P_Z) ≅ scalarSixChange a Z ⋙ restriction a Z`.
  `AugmentationNormalized` fixes its value on every K-flat representative C by a
  commuting equation involving the actual derived scalar counit, the localization
  comparison, `Q.map (tensorHom augmentation (𝟙 C))`, and the ordinary scalar-first
  tensor identification. The latter is fixed on underlying sheaves by
  `Mod.extendForgetTensorObjIso.inv`; the ordinary total comparison is fixed on
  each (0,n) summand by `HomologicalComplex.ιTensorObj`. Since the target complex
  has only degree zero, these summands determine the entire comparison. These
  equations specify the augmentation-induced beta, rather than a bare isomorphism.
- `pointModuleComp` uses the existing `mapModCompExtendScalarsIso` applied to the
  specified `upperStarFromPointComp`; `pointComplexComp` and `modelPull` are its
  degreewise and localized versions. Naturality of this same comparison applied
  to the point augmentation gives inverse-image compatibility of P, q and the
  augmentation. The first beta equation in `DerivedAssertions` explicitly asserts
  compatibility of beta with every scheme inverse image using `tensorPull`,
  `modelPull`, the exact restriction/pullback comparison, and `(D.theta a f).inv`.
- `geometricAdjunction` transports the recorded canonical derived module adjunction
  through `leftDerivedUpperStarIsoMapDerivedCategory`, retaining its counit.
  `gamma` is literally its A-adjunct of `(D.theta a f).inv` followed by
  `scalarSixChange.map` of the O-geometric counit. It is the actual map in the node.
- `restrictionPush` is the conjugate of the normalized theta under the scalar and
  geometric composite adjunctions. Thus it is the canonical restriction/direct-image
  comparison, for arbitrary a, without assuming that A is O-flat.
- `projection` is literally the O-adjunct of `tensorPull` followed by the model
  comparison tensored with the O-geometric counit, with the scalar factor first.
  The second beta equation in `DerivedAssertions` says
  `beta_Y; Res(gamma); d; Rf(beta_X.inv) = projection`, fixing the actual morphism.
- The final clause asserts `IsIso projection ∧ IsIso gamma` for every scheme
  morphism f and every object of the ordinary unbounded derived category.
  There are no properness, quasi-compactness, constructibility or coefficient
  flatness hypotheses. The zero-ring clause is `Subsingleton A → r = 0`.

The module uses the recorded dependency declarations, in particular:

| Module | Declarations used |
| --- | --- |
| `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (reexported) | `Padic.coefficientExtensionIntegers` and its finite-extension context |
| `Sheaf.NumberTheory.Padics.IntegersProfiniteTower` | `Padic.coefficientExtensionIntegersTopology` |
| `Sheaf.Topology.ProfiniteSectionsFiniteQuotient` (reexported) | `Profinite.continuousSectionsModule` |
| `Sheaf.Topology.ProfiniteCondensedRing` (reexported) | `Profinite.CondensedRing`, `continuousCoefficientRingObj` |
| `Sheaf.Topology.ContinuousMapCondensedRingMap` | `Profinite.continuousMapRingObjMapOfUniverse`, `Profinite.isMonHom_continuousMapRingObjMapOfUniverse` |
| `Sheaf.AlgebraicGeometry.ProEtalePointPullback` | `sfbPullbackFromPoint` |
| `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` (reexported) | ordinary `DerivedCategory`, localization conventions |
| `Sheaf.Algebra.Homology.KFlatIndependentCoefficients` (reexported) | `CochainComplex.IsKFlatIndependentCoefficients`, `MorphismProperty.kFlat` |
| `Mathlib.Algebra.Homology.BifunctorShift` (reexported) | the signed direct-sum total tensor underlying `HomologicalComplex.tensorObj` |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` (reexported) | `upperStarFromPointComp` and its monoidality |
| `Mathlib.AlgebraicGeometry.Sites.Proetale` (reexported) | `Scheme.ProEt`, its topology |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` (reexported) | `derivedUpperStarLowerStarAdjunction`, `leftDerivedUpperStarIsoMapDerivedCategory` |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients` (reexported) | `coefficientMap`, `derivedComapUpperStarIso` |
| `Sheaf.SixFunctors.ScalarSixPullback` | `ScalarSixPullbackData`, `scalarSixChange`, `scalarSixPull` |
| `Sheaf.Paper.SectionDerivedRealization` | `ModuleRingedComparison.internalModules`, `equivalence` |
| `Sheaf.Algebra.Homology.FiniteFreeMonoCokernelKFlat` | `monoCokernelComplex`, `monoCokernelAugmentation` |
| `Sheaf.Paper.ProjectionMateExact` (reexported) | canonical tensor/geometric-counit projection convention, `ringedProjectionMateExact` proof interface |
| `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction` | `proEtaleRingSheafChangeAdjunction` proof interface |
| `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars` (reexported) | `derivedExtendMapDerivedCategoryAdjunction`, `extendForgetTensorObjIso` |
| `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit` | `mapModCompExtendScalarsIso` |

The original statement-dependency records and full signatures/docstrings were read.
The four added statement dependencies are already landed definition nodes with usable
declarations: the coefficient topology, continuous-section module, section derived
realization, and continuous-map condensed-ring functoriality. They own constructions
actually appearing in this statement. No new node or dependency repair is introduced.
The stated proof dependencies are imported as proof imports (and those also used in the
statement are public imports); Mathlib proof leaves use their recorded declarations.

Edge cases checked: zero A admits r=0; ell-power exponent zero forces zero A;
A=O/ell^n is allowed despite nonflatness; a need not be surjective as a ring map;
rank zero uses the empty finite biproduct and its zero complex; f may be the identity,
have empty source or target, or be non-quasi-compact; C and K may be unbounded on both
sides. The statement carries no nonzero-ring, flatness, boundedness, or geometric
finiteness assumptions. Scheme object and morphism universes retain the existing
small pro-etale convention.

Searches performed using the prescribed launcher search wrapper:

- LeanFinder: “A finite torsion ring over the integers of a finite p adic field has a
  square two term free resolution and derived coefficient change commutes with
  arbitrary direct image”. Eight hits about BDeRham, untilts, residue fields and
  Witt vectors; none states the item.
- Loogle: `SheafOfModules, "extendScalars"`; zero hits.
- Mathlib grep: `integralFinite|integral_finite|perfectModel|twoTerm`; zero hits.
- Project `rg` searches in `lean/WeilConjectures` and `lean/Sheaf` for resolutions,
  scalar changes, K-flat tensor models, projection formulas, mapMod comparison and
  the exact item id found the finite arithmetic resolution and generic tensor/
  adjunction interfaces reused above, but no theorem stating this whole item.
- Exact item-id search in `lean/WeilConjectures` found no existing declaration.
- DAG searches located the already recorded continuous-section, valuation-topology,
  finite condensed resolution, and section realization nodes; none duplicates the
  actual perfect model and normalized geometric mate theorem.

## Second reading by Q80

I reread the node, current source and complete Lean statement clause by clause.
The dispatcher explicitly forbids starting other agents, so this is a separate
self-review, not an assertion that another worker independently reviewed it;
the maintainer's independent review remains the review specified by the brief.
The rereading checked the +phi cone sign, degrees [-1,0], the fixed quotient,
ordinary uncompleted derived categories, scalar-first factor order, beta's
augmentation normalization, and both geometric adjunct equations. In particular,
the inverse of `derivedComapUpperStarIso` is needed in the inverse-image equation:
its hom has the opposite orientation. This was corrected before delivery.
The beta and restriction/direct-image normalizations prevent replacing the actual
gamma by an arbitrary isomorphism. No mathematical mismatch remains identified.

## Returned delivery repair

H2 at returned head `5a4f436b2791` is repaired. The statement dependencies
`lem-sfb-finite-integral-condensed-resolution` and
`lem-sfb-normed-coefficient-realization` are removed, as are their direct imports.
`condensedMap` now bundles the actual map of
`def-sfb-continuous-map-condensed-ring-map`, using its monoid-homomorphism
certificate and the definitionally identical continuous coefficient objects.
The valuation-topology topological-ring instance is inlined using the existing
spectral norm normed-field construction and `inferInstanceAs`. No new node is
needed. The theorem's mathematical hypotheses, conclusion, canonical morphisms
and natural-language node statement are unchanged.

The repair review checks that both removed theorem conclusions are unused, the
replacement definition node owns the actual postcomposition map, and the inline
instance gives the prescribed valuation topology. The clause and edge-case
review above continues to apply.
