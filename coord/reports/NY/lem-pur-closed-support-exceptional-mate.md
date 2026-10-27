## Worker report

The module `Sheaf.Paper.ClosedSupportExceptionalMate` states
`AlgebraicGeometry.closedSupport_exceptional_mate` and
`AlgebraicGeometry.closedSupport_exceptional_mate_origin`. Both proofs are `sorry`.
All helper definitions have concrete data. No dependency node, natural-language statement,
proof, or dependency list is changed. No new DAG notion is needed: Diagram is only a typed
package of the existing functors and comparisons, always instantiated by `diagram` with
those exact constructions. Its equation predicates abbreviate the displayed formulas.

Source read: current blueprint main-20261015,
`sec-six-functors-basics/sk-prop-a1-kummer/thm-pur-affine-line-orientation.proof.md`,
the supported Cartier naturality sentence and final etale-origin comparison.
The item's eight-step refinement is retained in the theorem docstring: finite exchange;
the inverse adjunction formula; exchange naturality; transposition; supported-Hom pullback;
exact site comparison and its endpoint comparisons; image of the restricted adjunct;
identity/closed compactification and the comparison unit. The source's supported-Hom
normalization is the recorded `SupportHomPair.Identification`, including its injective
cocycle evaluation-at-one condition, rather than an arbitrary Hom equivalence.

Hypothesis and clause correspondence:

- The global finite-field datum, ell different from its characteristic, finite extension E,
  positive level n and quotient A are exactly `P : PurityFiniteSetting.{u}` and
  `P.Coefficient`. This is the published ULift of O_E/(varpi_E^n), not a new coefficient
  ring. The finite instances use `Padic.finite_coefficientExtensionRing` and ULift.
- Schemes Z,X,Z',X' are `Scheme.{u}`. The binders `i`, `i'`, `h`, `g` and
  `sq : ChosenCartesianSquare g i' i h` give precisely the chosen Cartesian square.
  `IsClosedImmersion i` and `IsClosedImmersion i'` express closedness. The second
  closedness is the given base change's property, and follows from the square and the
  first; it imposes no additional mathematical case restriction. There are no finite-type,
  separatedness, quasi-compact-complement or base-field hypotheses on this assertion.
- `F : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
  (ModuleCat.{u+1} P.Coefficient))` is every bounded-below ordinary etale A-complex;
  `a : ℤ` is every integer, and `alpha : (etaleSupportHomPair P i).group F a` is the
  supported hypercohomology class of the recorded kernel-of-restriction functor.
- `diagram` uses exact `Etale.lowerStar.mapDerivedCategory`, exact
  `Etale.upperStar.mapDerivedCategory` and the ordinary closed
  `Etale.lowerStar.rightDerivedFunctor.rightAdjoint`, with `adjunction` transporting
  its counit through `rightDerivedFunctorIsoMapDerivedCategory`.
  Its exceptional objects at `F.obj⟦a⟧` are Ri!(F[a]) and Ri'!(h*(F[a])). The canonical
  adjoint shift comparisons identify these with (Ri!F)[a] and (Ri'!h*F)[a]. This uses
  `Adjunction.rightAdjointCommShift` and its counit compatibility, not an extra
  assumption that exceptional inverse image commutes with shifts. The `Bounded` clause
  explicitly states that both objects belong to D+.
- `exchange` descends the actual `Etale.baseChangeMap` to derived categories and turns
  it into an isomorphism using `Etale.isIso_baseChangeMap_of_isFinite` on the actual
  pullback witness of sq. The two exact-composition comparisons are explicit. Its
  components are b_B; naturality is the natural-isomorphism type. All functors and maps
  are in fixed-A modules. `constantExchange` evaluates it on the degree-zero constant,
  followed by the published constant inverse-image comparison, and is c.
- `classMorphism P i (chiE i) F a alpha` is M. `supportedSingle` first identifies exact
  closed pushforward of the constant single with the single of the actual supported
  constant; `chiE` then applies the recorded normalized supported-Hom identification.
  `adj.homEquiv` is u. `pulledCounit` is b_K inverse followed by h*epsilon;
  `beta` is precisely `adj'.homEquiv` of this morphism. No arbitrary beta and no
  invertibility hypothesis occurs. `pulledMorphism` is c inverse followed by h*M.
  `pulledAdjunct` is g*u with the canonical constant-source comparison inserted.
- `Diagram.Equations` gives the four equations in order. In Lean's order of composition:
  M = push.map u followed by adj.counit; pulledMorphism M = push'.map pulledAdjunct(u)
  followed by pulledCounit; push'.map beta followed by adj'.counit = pulledCounit;
  adj'.homEquiv(pulledMorphism M) = pulledAdjunct(u) followed by beta.
- The last conjunct of the main theorem says that `pulledMorphism M`, followed by the
  canonical `upperStar.mapDerivedCategory.commShiftIso a`, equals `classMorphism` on X'
  of the pulled supported class. That class is `homologyFunctor.map (e.derivedMap.app F)
  alpha`. Thus it is the specified supported pullback, not a free map on cohomology.
- The existential chiE and chiP families are constrained by the full published
  `Identification` type. `e`, `p`, `v`, `v'` are the recorded etale pullback, pro-etale
  pullback, and two site-comparison transports. Their `Compatible` clauses retain the
  source, single, shift, kernel-inclusion and scalar-unit comparisons.
  `SupportHomSquareCoherent` asserts that the two routes commute on actual derived
  supported sections and on the supported constants.
- `ImageEquations` is all four equations under exact comparison inverse image
  `comparison`, on X, X' and Z' respectively. Its fourth equality is explicitly the
  image of beta composed with g*u. Together with the Compatible clauses and the square
  coherence, this gives the pro-etale supported-class identification at both ends.
  The equations are stated in the images' coordinates; conjugating endpoints by the
  canonical direct-image and pullback comparisons gives their pro-etale coordinates.
- The final finite-type clause is the second theorem. `Over (Spec P.field.k)`,
  `LocallyOfFiniteType` and `QuasiCompact` on both structure morphisms mean finite-type
  k-schemes; `i.IsOver` means a k-morphism. No separatedness of those structure maps
  is added. `transported` is literally the recorded `sfFiniteExceptionalAt` at
  `Compactification.ofIsProper i`, with its existing left-adjoint witness supplied.
  `compactNormalization` removes identity extension by zero and uses exact direct
  image. `rightComparison` is uniqueness of the two ordinary right adjoints through
  that comparison. `originIso` maps the actual comparison-unit isomorphism and then
  this right-adjoint comparison. `originTranspose` inserts the compactification
  comparison and site-unit into M, takes its ordinary compact-support transpose and
  applies nu_Z*. The second theorem identifies it with nu_Z*(u) followed by originIso.
  Hence the main theorem's image restriction is exactly the restriction in the
  transported Hom chain. Every supported M is covered by this equality.
- For an arbitrary geometric fibre use the main theorem with that square: its target
  is nu_Z'*(Ri'! h*F[a]) by construction. No finite-type binder is introduced for it,
  and no ambient pro-etale exceptional adjunction is used or asserted.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `Coefficient`, `constantEtale` and the published ring structure.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare`,
  its `toCommSq`, `isoPullback`, `hom_fst`, `hom_snd`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: `Etale.DerivedCategoryModule`,
  `DerivedCategory.Plus` of the same module sheaves.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`,
  `Etale.lowerStar` and `upperStarLowerStarAdjunction` on arbitrary scheme morphisms.
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`:
  `Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`.
- `Sheaf.AlgebraicGeometry.SupportCohomology`: `Etale.supportRestrictionArrow`,
  `Sheaf.supportedSectionsFunctor`; the module-valued derived support is the recorded
  `SupportHomPair.group` of `Sheaf.Paper.SupportedHomPullback`.
- `Sheaf.Paper.SupportedHomPullback`: `etaleSupportHomPair`, `proEtaleSupportHomPair`,
  `SupportHomPair.Identification`, its normalized `chi`, `etaleSupportHomTransport`,
  `proEtaleSupportHomTransport`, `siteSupportHomTransport`, `Transport.derivedMap`,
  `Transport.Compatible`, `SupportHomSquareCoherent`, `supportedHom_pullback`.
- `Sheaf.Paper.SupportedCohomologyHom`: `ProEtale.supported_cohomology_hom`;
  `Sheaf.AlgebraicGeometry.ClosedSupportHom`: `Etale.closedSupportHom`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparison`
  and its fixed-module version, realized by `ProEtale.comparisonUpperStar`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`, through its data module
  and `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`:
  `ProEtale.sfFiniteExceptionalAt`; ordinary compact adjunction witness from
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`:
  `Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
- `WeilConjectures.SixFunctors.Finite.BaseChange`:
  `Etale.isIso_baseChangeMap_of_isFinite`; `Mathlib` exact derived descent:
  `Functor.mapDerivedCategory`, `mapDerivedCategoryCompIso`,
  `mapDerivedCategoryNatIso`, `mapDerivedCategorySingleFunctor`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf`:
  `Etale.constantSheafCompUpperStarIso`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition`:
  `Etale.mapDerivedCategoryOpenImmersionLowerShriekId`.
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`:
  `ProEtale.isIso_compactSupportComparisonUnit`; its unbounded-component form is
  `ProEtale.isIso_derivedComparisonAdjunction_unit_app` from
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison`.
- The proof-only imports retain `exactDerivedAdjunction_isGE`,
  `comparisonPullbackExact`, `isIso_comparisonDirectImagePlus`,
  `supportSiteComparison_pullback_coherent`, `etaleInverseImageModulesExact`,
  the finite/closed/affine permanence instances, and the Mathlib adjunction and shift APIs.

Edge cases checked against the formulas: i=id and h=id reduce to the adjunction and
constant-comparison identity laws; Z empty and F=0 give zero supported groups and zero
morphisms; no positivity restriction excludes negative a; general h includes arbitrary
geometric fibres, without a finite-type k-structure on X'. The second theorem is invoked
only in its stated finite-type k-domain. The independent object and morphism universes
of the small sites remain u+1 and u; modules and coefficients are at u+1.

Searches actually run using the prescribed msearch wrapper:

- LeanFinder query "Closed support exceptional adjunction counit base change mate
  represents pullback of supported cohomology for etale module sheaves": eight results,
  sheaf-of-modules pullback adjunction/unit formulas, no exact statement.
- Loogle query `CategoryTheory.Adjunction.homEquiv`: twelve results, including homEquiv,
  homEquiv_counit and mkOfHomEquiv; these supply the adjunction API, not the geometric
  supported-class statement.
- Mathlib grep `exceptional.*[Mm]ate|closedSupport.*[Mm]ate|supportedHom_pullback`:
  zero results.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for the item id and exceptional-mate
  patterns: no existing exact match; `ExceptionalMateSiteComparison` concerns the
  transported finite-type framework, `ClosedFiniteAdjointCounitTransport` its counit
  transport with a complementary quasi-compact open, and `SupportedHomPullback` the
  supported-Hom pullback without the four ordinary-closed-adjoint equations. Their
  interfaces were opened and checked. The present theorem retains arbitrary h and X'.

No STATEMENT-DISPUTED flag and no statement correction. The example CompactObject module
is now withdrawn; its node still supplies the expected Lean-record shape. All compilation
and probes used scompile.py with module-mode headers. The final module contains no
profiling commands, no diagnostic checks, no file-local notation or local instances.

## Second reading by NY

This is the author's final check; the maintainer supplies the independent delivery review,
as required by the dispatcher brief. I reread the node and both theorem signatures.
The first draft's final comparison was only described in its proof docstring: it now has
an explicit theorem using the actual transported functor, compactification normalization,
unit and right-adjoint uniqueness. The shift is inserted on the argument F, and the
pullback shift isomorphism remains explicit in the supported-class equation. The four
mathematical composition orders agree with `≫`; the only maps inverted are the finite
exchange and canonical comparisons, never beta. The class source is exact pushforward of
the degree-zero constant, compared to the supported single by `supportedSingle`.
The two exceptional objects have explicit boundedness. The site-square and four
Compatible assertions are retained in full, and the fourth ImageEquations equality
states the image of the restricted adjunct. Empty, zero and arbitrary-fibre cases remain
admissible. No node meaning or dependency interface has changed.

Validation: scompile.py accepted the complete delivered module with no warnings.
The prescribed deliver2.py --no-push passed server preflight and per-file compilation
(checked packet commit 0d8c17082f3). Both theorem proofs remain sorry.
