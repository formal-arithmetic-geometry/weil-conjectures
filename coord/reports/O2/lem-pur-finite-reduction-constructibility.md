## Worker report

N2 states `AlgebraicGeometry.FiniteReduction.finiteReduction_constructibility` in
`Sheaf.Paper.FiniteReductionConstructibility`. The only postponed proof is this named
theorem. Its docstring gives all ten proof steps, their dependency nodes and sources.
All auxiliary data are actual definitions or structures. No target, node statement,
statement dependency, proof or proof dependency was changed; only the item's `lean`
record is replaced. There are no new nodes or dependency-module repairs.

The source is the first paragraph of
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction.proof.md`,
read together with the node's explicit finite-coefficient and intrinsic qualifications.
The statement does not require a Noetherian scheme or constructible terms in the flat
model, and does not assume flatness of the coefficient quotient.

Hypotheses and their rendering:

* The prime is `l : ℕ` with `[Fact l.Prime]`. `Ring l r` is the actual
  `ZMod (l ^ r)`, lifted to the scheme universe; `Coeff l r` lifts the same ring
  to the module universe. `quotient l hmr` is the lifted `ZMod.castHom` supplied
  by `pow_dvd_pow l hmr`, not an arbitrary ring map.
* `T : Scheme.{u}` is arbitrary. `_hinvert : ∀ x : T, IsUnit (l : T.presheaf.stalk x)`
  is precisely invertibility of the integer on the scheme.
* `r m`, `_hm : 1 ≤ m` and `hmr : m ≤ r` impose the specified exponent range.
  `a b : ℤ` and `_hab : a ≤ b` impose the ordered Tor interval.
* `K` belongs to the derived category of fixed-coefficient pro-etale module sheaves.
  `realize T l r` is the canonical exact intrinsic realization, obtained from the
  dependency's `finiteCoefficientIntrinsicRealization`, with no new equivalence choice.
  `_hconstructible` applies the existing intrinsic constructibility predicate to every
  cohomology sheaf of this realization. `_hbounded` asserts one bounded cohomology interval.
* `_htor` is the existing `Scheme.HasProEtaleTorAmplitude` on the realization of K.
  It tests all intrinsic pro-etale module sheaves, as in the dependency, not merely
  those of etale origin.
* `K₀` is an ordinary-etale derived object. `_hK₀` uses the recorded global
  `Etale.DerivedCategory.isBoundedConstructible`, and `e` is the specified isomorphism
  from `ProEtale.comparisonUpperStar.mapDerivedCategory.obj K₀` to K.

Conclusions and their rendering:

* The first conjunction is `Etale.DerivedCategory.hasTorAmplitudeIn ... a b K₀`.
* The existential `Q` is an ordinary-etale cochain complex. Its first
  `Etale.IsBoundedFlatComplex` conjunction states both flatness of every term and zero
  terms outside `[a,b]`. `Nonempty (K₀ ≅ DerivedCategory.Q.obj Q)` states representation.
* `(HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q` is the existing monoidal K-flatness
  predicate: tensoring preserves quasi-isomorphisms, equivalently acyclic complexes.
  The same predicate is asserted for the actual termwise extension `Q_m`.
* `Q_m` is not independent data: it is
  `((extend T.smallEtaleTopology (quotient l hmr)).mapHomologicalComplex (.up ℤ)).obj Q`.
  Its second `IsBoundedFlatComplex` states zero terms outside the same interval and
  flatness over the reduced ring. Its representation isomorphism identifies its
  localization with `(S.etale r m hmr).functor.obj K₀`.
* `S.etale` and `S.proetale` are universal left derived functors of the concrete
  sectionwise tensor-and-sheafify scalar extensions. `DerivedExtension` includes the
  universal counit and its invertibility on K-flat complexes. Thus these expressions
  mean derived scalar extension, not an underived quotient of K₀ or K.
* The reduced ordinary-etale object satisfies `isBoundedConstructible`.
  The displayed existential `origin` identifies its comparison with the reduced K,
  and the equality fixes its hom to `(S.comparison ...).hom.app K₀` followed by the
  actual image of `e.hom`. `System.originComparison` constructs exactly this map.
* The final three finiteness conjuncts give intrinsic constructibility of every
  reduced pro-etale cohomology sheaf, boundedness and the original Tor interval `[a,b]`.
* For every `n ≥ 1` with `hnm : n ≤ m`, `S.CoherentAt ... K₀` is the explicit equality
  of the two morphisms around the comparison/associator square. It includes the
  coefficient-comparison maps at both stages and both derived associators.

Canonical constructions and size conventions:

`extend` uses the existing `Sheaf.composeAndSheafify` and `ModuleCat.extendScalars`,
with its existing restriction adjunction. `ordinaryComparison` is the unique left-adjoint
comparison induced by the identity of the common right adjoint. `ordinaryAssociator`
uses `Sheaf.restrictScalarsCompIso` and the same adjunction uniqueness construction.
Its local convention `c tensor (b tensor q) ↦ image(b)c tensor q` is exactly
`(q tensor b) tensor c ↦ q tensor bc` after exchanging the commutative tensor factors.
`System.comparison_model`, `etaleAssociator_model` and `proetaleAssociator_model`
normalize the derived maps against these actual ordinary maps on flat K-flat
representatives, by explicit counit equations. They exclude arbitrary comparison maps.
The theorem returns existence of the universal system and the asserted properties;
no definition chooses an object from that postponed existence proof.

The original small pro-etale site is retained: object universe `u+1`, morphism universe
`u`. Fixed scalar modules live in universe `u+1`; intrinsic modules use the existing
`Scheme.proEtaleDerivedCategory` and its standard localization. All variables and
universes are bound explicitly (`autoImplicit false`); in particular `ModuleCat.{u+1}`
is explicit throughout. Coefficient lifts are canonical size transports, with no
hypothesis equating site universes.

Dependency declarations read and used (or retained as the stage-3 proof plan):

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
* `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `AlgebraicGeometry.ProEtale.FiniteCoefficientModules`; its canonical intrinsic
  realization and exactness are in the publicly reexported
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`.
* `Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf` publicly retains
  `Scheme.IsConstructibleProEtaleModuleSheaf` from
  `Sheaf.Paper.ProEtaleConstructibleSheaf`; this actual-site version is used via
  the smaller module imported by the finite-ring origin interface.
* `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude` publicly retains
  `Scheme.HasProEtaleTorAmplitude` from `ProEtaleTorAmplitude`; this actual-site
  version is used. The coefficient-sized predicates are the additional model-site
  formulations, rather than replacements for the retained intrinsic predicates.
  The larger model-interface modules were inspected but are not imported: their
  additional sheafification instances cause unresolved universe inference on the
  original intrinsic site. The smaller original modules supply exactly the predicates
  used here, retaining Mathlib’s canonical abelian structure and standard localization.
* `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`:
  `Scheme.finiteRing_constructibleDerived_origin`, including the canonical
  `ProEtale.finiteCoefficientIntrinsicDerivedComparison` and the global etale
  `Etale.DerivedCategory.isBoundedConstructible` predicate.
* `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel`:
  `Etale.hasTorAmplitudeIn_iff_exists_flatModel`, `Etale.IsBoundedFlatComplex`.
* `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`:
  `CochainComplex.isKFlat_of_boundedAbove_flat`.
* `Sheaf.Paper.PbcActualScalarPullback`:
  `Scheme.pbcActualScalarDerivedPullIso_exists` and its public canonical
  ringed-topoi tensor-pullback interfaces with representative normalizations.
* `Sheaf.AlgebraicGeometry.ComparisonTorInterval`:
  `ProEtale.comparison_torAmplitudeIn_iff`.
* `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`:
  `SheafOfModules.changeOfRings_isKFlat_of_flat_terms`.
* `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`:
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`.
* `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`:
  `Etale.DerivedCategory.hasTorAmplitudeGE` and `hasTorAmplitudeIn`.
* `Sheaf.Paper.ComparisonPullbackExact`: `AlgebraicGeometry.comparisonPullbackExact`.
* `Sheaf.CategoryTheory.SiteInverseImageTensor`: `CategoryTheory.siteInverseImage_tensor`.
* `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparison`.
* `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `Scheme.IsConstructibleEtaleModuleSheaf`. The upstream file with the same
  declaration is not also imported, to avoid declaring the notion twice.
* `WeilConjectures.ConstructibleSheaf.Refinement`: `Scheme.Stratification.inter`,
  `Scheme.IsConstructibleSheaf.of_refines`.
* `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`.
* `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`:
  `CategoryTheory.Functor.homologyFunctorIso` (the node's mathlib match).
* `Sheaf.Paper.LocallyConstantTensor`:
  `SheafOfModules.locallyConstantFiniteType_derivedTensor`.
* `WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues`:
  `Scheme.finite_locally_constant_module_values_iff`.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`:
  `SheafOfModules.siteSheafTensorRightMap`.

The two upstream proof modules not present in the older local checkout were read
through `scompile.py --source`, using the current published source. All other recorded
signatures and docstrings were read locally. The existing general derived-extension
interfaces concern ringed-site presentations; the helpers here package the same
universal construction in the fixed-scalar presentation of this node's etale origin.
They use existing scalar extension, localization and adjunction constructions.

Edge cases checked by reading the statement and constructions:

* `r=m` and `m=n`: quotient and adjunction uniqueness still specify the ordinary
  identity reduction, and the associator square includes these cases.
* `m=1`, `l=2`, including `r=2,m=1`: the nonflat quotient is allowed. No flatness
  instance for that ring map is used; the representative has flat terms instead.
* `a=b`: the flat model is allowed to be concentrated in one degree. The zero
  object and an empty scheme are allowed; there is no nonvanishing hypothesis.
* No quasicompactness, Noetherianity, algebraic closure, finite-type or field base
  hypothesis has entered. Constructibility is the dependency's global definition.
* Successive quotient maps compose as actual `ZMod` homomorphisms. The ordinary
  tensor associator is defined for all exponents, so equalities of exponents and
  arbitrary supplied origin isomorphisms are retained.

Searches for an existing statement (2026-10-17):

* `msearch.py ... leanfinder "Derived extension of finite quotient coefficients
  preserves constructible etale complexes and Tor amplitude"`: eight etale-algebra
  results (including `Algebra.Etale.finitePresentation`), none about sheaf reduction.
* `msearch.py ... loogle '"hasTorAmplitudeIn", "tensor"'`: zero results.
* `msearch.py ... grep 'constructible.*(reduction|quotient)|[Kk][Ff]lat.*(baseChange|changeOfRings)'`:
  zero results.
* `msearch.py ... leansearch "Finite quotient coefficient reduction preserves
  bounded constructible sheaves and Tor amplitude on etale and proetale sites"`:
  eight general finite-limit/finite-type sheaf results, no statement match.
* `rg` in Mathlib, the upstream `WeilConjectures` tree and `lean/Sheaf` for
  constructibility/reduction, scalar extension, associators, K-flatness and Tor
  amplitude located the interfaces listed above but no theorem with this statement.
  Searching the upstream tree for the item id returned no declaration; the new
  namespace and theorem name have no existing match.

No statement is disputed and no node fault was found. Verification uses only
`scompile.py` and the prescribed `deliver2.py` checks; final results are recorded below.

## Second reading by N2

I reread the node and complete module clause by clause, with the source paragraph open.
This is the dispatcher's single-worker self-check; the independent maintainer review
is still required. No second agent was started, as explicitly instructed.

The reading checked in particular: the specified isomorphism e is used in the origin
map; the actual coefficient quotient is fixed; etale constructibility uses the recorded
global predicate; intrinsic Tor tests arbitrary module sheaves; both K-flatness assertions
are present; both zero-term bounds refer to `[a,b]`; the associator square is an equality
of the canonical morphisms, with normalization on actual flat models. The universal
system is existentially returned rather than assumed as an extra hypothesis.

During construction I made the module universes explicit, fixed the intrinsic
cohomology universe, and used `NatIso.mapHomologicalComplex` for the termwise map.
These were typing repairs, with no change to the mathematical statement. The read-through
found no remaining mismatch. All helper docstrings identify their source and this node;
the sole sorry theorem contains the full natural-language proof.

Verification: `scompile.py N2 lem-pur-finite-reduction-constructibility
lean/Sheaf/Paper/FiniteReductionConstructibility.lean` completed with exit 0 and no
warnings or errors: sandbox compile 24.3 seconds, library-path compile 21.6 seconds.
Only the node's `lean` field differs from the shared original, the stored signature
matches the file verbatim, and all source lines are at most 100 characters.
