## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedSourceSiteTensorComparison` states
`AlgebraicGeometry.ClosedSourceSiteTensor.closedSourceSiteTensorComparison`.
Its only postponed proof is that named theorem. Every helper has real data from
published canonical constructions. There are no new nodes, dependency repairs,
or statement corrections.

Hypotheses and objects:

- The fixed finite datum A=A_{E,n}, including the primes, extension, positive
  level, finite field and algebraic closure, is `P : PurityFiniteSetting.{u}`
  from `Sheaf.Paper.PurityFiniteSetting`. The scalar ring is precisely
  `P.Coefficient`, the existing universe lift of the quotient `P.Ring`.
  `finiteRing` applies `Padic.finite_coefficientExtensionRing`; `finiteCoefficient`
  transports that existing finiteness through ULift. Neither is a new assumption.
- The k-scheme is `X : Scheme.{u}` with `[X.Over (Spec (.of P.field.k))]`.
  No finite type, separation, smoothness, or quasi-compactness assumption occurs.
- The two immersions are `i : C ⟶ X`, `j : D ⟶ X`, with exactly their
  `IsClosedImmersion` instances. `Etale.intersectionSupport i j` is the recorded
  `pullback.fst i j ≫ i`, hence the scheme-theoretic intersection, including its
  scheme structure. The existing fibre product is not replaced by a point set.
- The arbitrary map is `v : X' ⟶ X`. There is no condition on v or X'. Its pulled
  back supports are `pullback.fst v i`, `pullback.fst v j`.
- P_C^e and P_C^p are the recorded
  `SupportedConstantNormalization.supported P.Coefficient false/true i`.
  The étale object is definitionally `Etale.closedConstantModule P.Coefficient i`.
  The site inverse image is `ProEtale.comparisonUpperStar` from the recorded
  comparison geometric morphism, with its original Kan-extension/sheafification
  adjunction and unchanged site universes: objects u+1, arrows u, coefficients u+1.

Clause-by-clause conclusion:

1. For EVERY `Y : X.ProEt`, the first conjunction states that the second and
   third section identifications are isomorphisms and gives the equality
   `gamma.app Y ≫ proSupportSections.hom = comparisonSections.hom ≫
   etaleSupportSections ≫ constantComparisonSections` in ModuleCat.
   Thus the result is equality of actual linear section maps, not just
   existence of bijections or a comparison of ranks.
   `comparisonSections` is the module-valued Tag 0GLZ identification: transport
   evaluation at Y to terminal evaluation of the localization restriction,
   use `upperStarIsoLocalizationRestriction`, commute comparison with pullback
   by the prescribed `comparePullback`, and invert the comparison-adjunction
   unit evaluated at the identity étale object. This realizes the same
   comparison-section formula as `proEtaleComparisonPullbackSections`: both
   are adjunction-normalized, and carry the comparison unit to the usual
   terminal-section pullback. No arbitrary equivalence is chosen.
   `etaleSupportSections` applies precisely
   `Etale.closedConstantPullbackAdjoint` and evaluates the resulting direct
   image using the canonical second projection from pullback of an identity.
   `constantComparisonSections` is the comparison adjunction unit on terminal
   sections followed by `compareUnit`. This is exactly the i=0 map of
   `comparisonCohomologyMap`, expressed on sections rather than Ext^0, with
   the scalar-preserving constant identification.
   `proSupportSections` is the canonical constant pullback identification
   on C_Y. Its left side evaluates the actual pro-etale direct image at Y;
   its right side evaluates the constant sheaf at the identity on C_Y.
   The isomorphisms are in ModuleCat, so additivity and linearity of all
   identifications are part of their types.
2. The next conjunction quantifies over every morphism `g : Z ⟶ Y` of weakly
   étale tests and states the restriction square for the actual gamma.
   Since clause 1 identifies the composite with gamma, it also states the
   restriction compatibility of that composite. The following conjunction
   explicitly states `gamma_Y (a • s) = a • gamma_Y s` for every a and s.
   These natural module maps preserve the full constant-ring-sheaf action:
   its scalar sections are locally constant, so constant-scalar linearity
   and restriction compatibility glue to that action. This imposes no
   additional assumption on the scalar section or the test object.
3. The first displayed sheaf square is
   `compare.map (Etale.closedConstantTensorMap ...) ≫ gamma_I =
   δ_compare ≫ tensorHom gamma_C gamma_D ≫ multiplication P i j`.
   `multiplication` is EXACTLY `ProEtale.cupCoefficientMap`, conjugated by
   `cupSupportIso`, which itself is direct image of the existing
   `ProEtale.cupConstantIso`. These are the two coefficient presentations
   already present in the cited dependencies. This transports coefficients
   without changing the specified multiplication or the specified gamma.
4. The second displayed sheaf square uses the actual
   `exchange A true (baseSquare i v)`. Here `baseSquare` is the canonical
   chosen Cartesian square with projections and `pullbackSymmetry v i`.
   The target identifies v^*(C intersection D) with C' intersection D'
   by `baseSupportChange`, the adjunction-induced constant-support map
   for the universal lift `intersectionChange`. This is precisely the
   canonical support identification suppressed in the node's display.
   In particular no HEq, arbitrary support map, or independent isomorphism
   is a parameter of this statement.
5. The last two conjunctions are `DerivedSquare` for comparison and for
   arbitrary pro-etale pullback, respectively, with the SAME ordinary
   multiplications and the SAME exchanges as clauses 3 and 4.
   `DerivedSquare` spells out equality in the ordinary unbounded
   `DerivedCategory`. Derived multiplication is the existing
   `ProEtale.cupDerivedCoefficientMap μ`: canonical localization tensor
   comparison on the degree-zero complexes followed by `singleFunctor.map μ`.
   On the flat étale source it agrees with
   `Etale.closedConstantDerivedTensorMap` via
   `Etale.singleFunctorObjTensorIso`; on the pro-etale side it is exactly
   the degree-zero localization model used in SupportedCup, transported
   by `cupSupportIso`. The derived exchange is
   `singleFunctorCompLeftDerivedFunctorIso.hom.app` followed by single of
   the actual ordinary exchange. The tensor comparison is
   `Functor.leftDerivedTensorComparison`, the canonical derived comparison
   specified by its square on K-flat representatives. This is the
   fixed-coefficient realization of the recorded ringed-topos comparison,
   not an existential monoidal structure or an arbitrary natural isomorphism.
   Flatness is already provided by the two source dependencies; it is
   not assumed again. No monoidal, exactness, or Noetherian hypothesis
   is added to the main theorem: all instances are synthesized for the
   recorded finite coefficients and inverse images.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `Coefficient`, `constantEtale`, `constant`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, fst, snd,
  lift and symmetry.
- `Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor`:
  `Etale.closedConstantModule`, `intersectionSupport`,
  `closedConstantPullbackAdjoint`, `closedConstantTensorMap`,
  `closedConstantDerivedTensorMap`, `closedConstantTensor` and its flatness/model API.
- `Sheaf.Paper.SupportedCup`: `cupConstantIso`, `cupCoefficientMap`,
  `cupCoefficient_flat`, `cupSingleTensorMap`, `cupDerivedCoefficientMap`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`, `proEtaleSiteComparisonModules`.
- `Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization`:
  `supported`, `compare`, `pull`, `unitIso`, `compareUnit`, `comparePullback`,
  `exchange`, `gamma`, and normalization/uniqueness clauses.
- `Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections`:
  `proEtaleComparisonPullbackSections`, its restriction and unit specification.
- `Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison`:
  `ProEtale.comparisonCohomologyMap`, `comparisonCohomologyMap_bijective`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`,
  its representative characterization. The statement uses its canonical
  fixed-scalar realization `Functor.leftDerivedTensorComparison` from
  `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal`.
- Proof-plan imports also include `ConstantLeftModuleInverseImage`,
  `ModuleSheavesColimitsForgetful`, Mathlib's `Sheaf.isLocallySurjective_iff_epi'`,
  `CochainTensorUniverses` and `RingedTopoiInverseImageTensorComparison`.

Edge cases checked before drafting and again against the final statement:

- C, D or their intersection may be empty. No Nonempty or Nontrivial instance
  is requested for a support, coefficient section module, or test scheme.
  Empty schemes use their terminal/empty sections and zero module formulas.
- Nonreduced closed schemes remain the actual fibre products; no reduction,
  Cartier property, smoothness, finite type, or stalk conservativity is used.
- v is arbitrary, including identity, empty-source and non-weakly-etale maps.
  Only Y is weakly etale, because it is explicitly a pro-etale test object.
- The support-comparison lift handles identity and iterated fibre products
  without assuming their chosen objects are definitionally identical.
- Level positivity and ell different from p are inherited from P, not extra
  restrictions on X. The field structure of X is exactly the node's k-scheme
  assumption. No field compatibility is silently required of arbitrary v.
- The generic DerivedSquare helper's structural parameters are not new
  hypotheses of the main result: compilation synthesizes them from the
  finite-ring and existing inverse-image instances.

Searches for existing declarations:

- `msearch.py ... leanfinder "Etale proetale closed constant direct image canonical
  exchange sections tensor multiplication"`: 8 hits, all étale algebra/formal
  étaleness results, no closed-source site tensor normalization.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme, CategoryTheory.Sheaf"`:
  12 hits on gluing, sites and Zariski modules; none states this comparison.
- `msearch.py ... grep "closedConstant.*[Tt]ensor|comparison.*Section" CategoryTheory`:
  2 unrelated biproduct-comparison hits.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  closedConstant tensor, closed site tensor and the new namespace found the
  cited étale source and SupportedCup's private coefficient comparison, but
  no result combining the prescribed gamma's section formula, arbitrary
  pro-etale exchange and both derived squares. Existing notions are reused.
- Namespace/declaration search in `dag/lean_names_upstream.json` and the two
  project source roots found no clash. Existing unrelated `comparisonSections`
  declarations are in different namespaces; this name belongs to
  `AlgebraicGeometry.ClosedSourceSiteTensor`.

Sources read: `literature/stacks-project/proetale.tex`,
`lemma-describe-pullback-from-etale` (Tag 0GLZ), `lemma-relative-comparison`
(Tag 099V), and `lemma-compare-cohomology` (Tag 099W), together with the
four-step source proof and every statement dependency's record/signature/docstring.
No mathematical statement fault was found.

## Second reading by NQ

I reopened the complete node and the module and made a separate clause audit.
The dispatcher expressly forbids starting another agent; this is a second pass
by the same worker, not a claim of independent review. The maintainer's
independent reading remains the delivery review.

This pass checked every binder and all seven conjuncts against the node.
It checked orientations of the terminal-object maps, the comparison inverse
image, the canonical baseSquare and the support identification. It verified
that multiplication transports the existing cup map instead of reselecting it,
that gamma and exchange are the recorded maps, and that the derived clauses
are equalities of actual morphisms rather than statements about homology.
It also checked that the module-valued section formulation provides scalar
compatibility without changing the underlying Tag 0GLZ formula. During
compilation I exposed the already defined ProEtale.upperStar and
comparisonUpperStar names in the main theorem so typeclass search sees their
published instances, and added the existing finite-coefficient finiteness
instances rather than a new Noetherian hypothesis. No node statement changed.
