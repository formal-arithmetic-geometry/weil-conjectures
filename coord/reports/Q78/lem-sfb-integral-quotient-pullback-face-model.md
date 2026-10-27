## Worker report

The module `Sheaf.Paper.IntegralQuotientPullbackFaceModel` states
`AlgebraicGeometry.ProEtale.IntegralQuotient.PullbackFace.integral_quotient_pullback_face_model`.
Its proof is `sorry`. Its 22 auxiliary declarations contain actual data or explicit
propositions: no resolution, scalar map, comparison or coefficient object is chosen
from a bare existence assertion. The auxiliary route predicates package this item's
six-face conclusion, rather than introducing a second K-flat or module definition.

I read the item, its eight proof steps, each statement dependency's statement and
recorded interface, and the current blueprint integral proof paragraph (3). The latter
is the reduction-of-canonical-maps sentence, not an assumption of properness or
completeness for the present elementary comparison. The supplied node is unchanged
except for `lean` and five added, already-landed statement dependencies. No source
correction, new node or dependency repair is made.

Hypotheses and coefficient objects:

- The explicit section variables `(l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]` are the prime and finite
  extension. The valuation ring, its chosen uniformizer and its powers are the
  dependency's `Padic.coefficientExtensionIntegers` and `coefficientExtensionIdeal`.
  `n : ℕ` indexes the positive exponent `n + 1`, so every and only positive exponent
  is covered, including exponent one at `n = 0`.
- `IntegralQuotient.integral l E` is exactly the existing continuous integral
  condensed ring, pulled to each site by `condensedRingObj`. Its identification with
  the inverse limit of actual finite constant coefficients is the recorded
  `sfb_integral_coefficient_limit`, including its normalization at every finite
  projection on profinite test objects. `finite l E n` is the existing discrete
  continuous-map finite quotient at exponent `n + 1`; its pullback is the finite
  constant coefficient presentation. `reduction l E n` is postcomposition by the
  actual `Ideal.Quotient.mk`, not an arbitrary epimorphism or an assumed flat map.
  `coefficientMap (reduction l E n) T` is precisely its point pullback on the site.
- `Scheme.{u}` and `Scheme.ProEt.topology T` retain the small site's object universe
  `u + 1` and Hom universe `u`. Coefficient sections are in `u + 1`, internal module
  categories have object universe `u + 2` and Hom universe `u + 1`. The generic
  `Route` therefore has separately bound object and Hom universes `v,w`.
- `QuotientChange.Modules Λ T` is the recorded internal module category. The node
  first introduces the internal rings and explicitly also regards them as their
  reconstructed section rings. The fixed `ModuleRingedComparison.equivalence Λ T`
  gives those section coordinates, with unchanged underlying abelian sheaves and
  maps. In particular `FlatRepresentative` uses the dependency's *section-module*
  `IsKFlatIndependentCoefficients` and `IsFlatOnSite` after this very equivalence,
  with the actual reconstructed ring and site. The ordinary tensor comparison is
  normalized by unchanged local pure tensors, so these coordinates retain the
  specified balanced maps. This does not use a constant integral ring in place of
  the continuous integral ring or introduce another module encoding.
- `sq : ChosenCartesianSquare h f' f g` supplies exactly the named corners, edges,
  Cartesian structure and commutativity. No geometric property of an edge is a
  typeclass hypothesis.

Conclusion, clause by clause:

1. `CoefficientCoherence (integral l E)` and
   `∀ m, CoefficientCoherence (finite l E m)` give the identity and composition
   equations for the actual `condensedPullbackHom`. These are the coefficient
   identifications supplied by `upperStarFromPointComp`. Their inverses/isomorphism
   structure are already in `cartesianCoefficients`; the new assertion is coherence,
   not an arbitrary family of ring isomorphisms.
2. The next universally quantified equality is the coefficient projection square:
   `upperStar.map (coefficientMap reduction V) ≫ condensedPullbackHom finite a =
   condensedPullbackHom integral a ≫ coefficientMap reduction U`.
   It is stated for *every* `m`, rather than just the chosen face level `n`.
   Both sides use the pulled-back condensed comparison itself, so their finite
   projections agree with that comparison. Via the integral-limit normalization
   cited above these are the actual finite projections, with no claim that inverse
   image preserves an arbitrary infinite limit.
3. For every `M : DerivedCategory (Modules (integral l E) Y)` the theorem gives a
   complex `P`, `FlatRepresentative ... P` and an isomorphism `Q.obj P ≅ M`.
   There is no boundedness or completeness predicate on either object.
4. `pull Λ a` uses the existing ordinary internal tensor pullback, termwise on
   cochain complexes; its derived functor is `QuotientChange.L`. Its comparison is
   the recorded universal computation counit `computePull`, transported from the
   homotopy category to cochain localization. `scalar` analogously uses
   `QuotientChange.extension`, its uncompleted left-derived functor `D`, and the
   existing computation map `QuotientChange.compute`.
5. The existential family `χ` is a family of natural isomorphisms with precisely
   the stated scalar/pullback direction. It is fixed by `(χ a).inv = scalarMate ... a`.
   `scalarMate` is real canonical data: it is the scalar-adjunction mate of the
   exact restriction/geometric-pullback square, using the existing exact inverse
   image comparisons. Thus no arbitrary isomorphism replaces the canonical one.
   In particular I did not use the more restrictive upstream `derivedPullIso`,
   which demands exact extension of scalars and would fail for these quotients.
6. The final `∀ P, FlatRepresentative ... P → CommonModel ... P` is for every
   flat-term K-flat input, not only a chosen representative of `M`. `Route.comp`
   retains every prefix's vertex predicate and invertibility of its canonical
   computation map. The six `.vertices P` conjuncts of `CommonModel` therefore
   assert flat terms and K-flatness over the ring at *every* intermediate vertex,
   together with the canonical representative identifications. No vertex receives
   a fresh replacement complex.
7. `start`, `afterG`, `beforeSquare`, `finish` are the first displayed route;
   `start`, `afterSquare`, `afterF`, `finish` are the second. Written as execution
   order, they are respectively `t,g,f'`; `g,t,f'`; `g,f',t`; `f,h,t`; `t,f,h`;
   `f,t,h`. Functor composition is written in Lean's execution order.
8. `SixFaces` lists in order exactly `Lf'(χg)`, `χf' Lg`, `T(ϑR)`,
   `ϑS T`, `Lh(χf)`, `χh Lf`. Each `Route.Face` is the actual equality
   `derivedFace.app (Q P) ≫ targetComparison P =
   sourceComparison P ≫ Q.map (ordinaryFace.app P)`.
   `ordinaryScalarFace` is the existing balanced `CondensedRing.pullIso` in the
   specified direction, lifted termwise by `complexSquare`. `ordinarySquare`
   uses the existing inverse-image compositors and the equality of composites
   supplied by `sq`. `derivedSquare` uses those precise published derived
   composition maps through `condensedAmbientPullbackComparison`. Whiskerings
   include the explicit associators in `leftFace`.
9. `CommonModel` universally quantifies every chain map `b : P ⟶ P'` to another
   flat-term K-flat input and gives `Route.NaturalAt b` for all six words. This is
   naturality of the very same representative identifications. The ordinary and
   derived faces are natural transformations, so their displayed face equations
   are natural with respect to those chain maps as well.

Dependency declarations used (statement modules are public imports; proof-only
modules are plain imports):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and its valuation-ring/quotient data.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, its topology and sizes.
  `def-weil-size-convention` is a convention record with no declaration to import.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, `coefficientMap`, `condensedPullbackHom`,
  `upperStarFromPointComp`, and the `condensedPushforwardHom_id/comp` laws.
- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`:
  `sfb_integral_coefficient_limit`, normalized at all quotient projections.
- `Sheaf.Paper.CartesianCoefficients`: `cartesianCoefficients`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `InternalAbelianSheafModule.sectionModuleEquivalence`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: recorded ordinary
  operations interface, publicly reexporting the *general ring-sheaf* operations
  and their canonical adjunction, not just its named constant specialization.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `WeilConjectures.integralTowerGeneralPullbackComposition`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Paper.KFlatScalarComparisonNormalization`:
  `SheafOfModules.ScalarPullback.mate` and
  `kflat_scalar_comparison_normalization`, including its nonflat scalar case.
- Five already-landed nodes added to `stmt_deps`: the actual coefficients
  (`def-sfb-integral-quotient-coefficients`, module `IntegralQuotientCoefficients`,
  declarations `integral`, `finite`, `reduction`); the actual scalar functors
  (`def-sfb-internal-derived-scalar-comparisons`, module
  `InternalDerivedScalarComparisons`, declarations `Modules`, `extension`, `D`,
  `L`, `scalarAdj`, `compute`, `V`); the canonical cochain computation map
  (`def-sfb-integral-quotient-projection-map`, module `IntegralQuotientProjectionMap`,
  declaration `computePull`); the existing section reconstruction
  (`def-pd-section-module-operations-data`, module `SectionModuleOperationsData`,
  declarations `ring`, `equivalence`); and the specified square compositor
  (`def-weil-pbc-ambient-ringed-exchange`, module `CondensedAmbientExchange`,
  declaration `condensedAmbientPullbackComparison`). All five were checked for a
  dependency path back to this item; none exists.
- Proof imports also retain `RingedTopoiTensorSections` (`RingedTensor.pure`),
  `ProEtaleFiniteReductionPullback` (`sfb_finite_reduction_pullback`),
  `Mathlib.CategoryTheory.Adjunction.Mates` (`mateEquiv_vcomp`, `mateEquiv_hcomp`),
  `KFlatRingedToposPullback` (`isKFlat_ringedToposPullback`), and
  `RingedTopoiDerivedPullbackIndependent` (`ringedTopoiDerivedPullbackIndependent`).
  `lem-trf-ringed-kflat-word-comparison-descent` has no recorded Lean module yet;
  its statement is only a proof dependency, so there is no declaration to import.

Edge cases checked: exponent one (`n = 0`); the zero complex; empty schemes;
identity edges and degenerate Cartesian squares; arbitrary unbounded complexes;
nonflat reduction such as Z_l to F_l; and ramified coefficient extensions. There
is no quotient-flatness, properness, boundedness, completeness or extra equality
of site universes in the statement. The original coefficient-extension declaration
makes the uniformizer choice, so no additional arbitrary uniformizer is assumed.

Searches actually run with `msearch.py` for this group/item (results are in the
sandbox's `searches.jsonl`):

- LeanFinder: `simultaneous K flat complex representatives scalar extension pullback
  comparison geometric cartesian square six faces`: 8 hits, including
  `AlgebraicGeometry.Flat.isStableUnderBaseChange` and
  `ModuleCat.preservesFiniteLimits_extendScalars_of_flat`; none gives this statement.
- Loogle: `Functor.IsLeftDerivedFunctor, NatIso.mapHomologicalComplex`: 0 hits,
  unknown identifier `Functor.IsLeftDerivedFunctor`; not an exact-match search success.
- Mathlib grep: `pullback.*[Tt]ensor|[Tt]ensor.*pullback|mapHomologicalComplexCompIso`
  in `Algebra/Category/ModuleCat/Sheaf`: 0 hits.
- LeanSearch: `K-flat representatives compute six scalar extension and geometric
  pullback faces on a cartesian square naturally in chain maps`: 8 hits, including
  `HomologicalComplex.Hom.sqFrom_left`, flat base-change and ordinary module
  extension exactness; none supplies a simultaneous normalized derived model.
- Project/upstream `rg`: K-flat, scalar, pullback and comparison searches found the
  existing interfaces above, which are reused. Exact item-id and theorem-name
  searches in `lean/Sheaf` and `lean/WeilConjectures` found no attachment; the required
  `grep -rn` of the item id in `lean/WeilConjectures` likewise returned no match.

Validation: the prescribed server `scompile.py` compiled the module both as the
sandbox module and its final library module, with no errors or warnings. After
making all recorded statement imports public, it passed again (31.9 s sandbox,
14.9 s library). No global or local Lake build was run.

## Second reading by Q78

This is a single dispatched worker, with independent maintainer review at delivery;
no second agent or independent reviewer is represented as having read this file.
I reread the complete node against the complete module. In particular I checked
that the two routes share `start` and `finish`, that six face equations use that
same P and its composed counits, and that the naturality quantifier covers arbitrary
chain maps between permitted representatives. The important correction during this
reading was to avoid upstream `CondensedRing.derivedPullIso`: its exact-scalar
hypothesis would have added a false flatness restriction. The current `scalarMate`
uses only exact restriction and geometric inverse image, and the theorem asserts
its invertibility and the ordinary balanced normalization. I also separated the
object/Hom universes in `Route`, made the site and ring explicit in flatness, and
checked that positive levels are indexed by `n + 1`. The final module compiles
with these changes. The actual independent mathematical review remains the
maintainer's review specified in the dispatch.
