## Worker report

The module `Sheaf.Paper.SmoothMateCounitCancellation` states
`AlgebraicGeometry.ProEtale.smoothMate_counit_cancellation`, with `sorry` as its entire
proof. Its helpers construct exactly the counit, the inverse exchange, the two
transposes, and the comparison maps named in the node. They introduce no new
independent notion and no arbitrary comparison data. There are no new nodes,
statement corrections, or dependency record changes.

Hypotheses and clauses, in the order of the node:

- `P : WeilConjectures.PurityFiniteSetting` retains the fixed finite-field datum,
  the prime different from its characteristic, the literal finite coefficient
  subextension, and its positive level. The coefficient ring is `P.Coefficient`,
  the recorded size lift of `P.Ring = O_E/(varpi_E^n)`. The instance
  `mateCounitCoefficientFinite` uses `Padic.finite_coefficientExtensionRing` and
  the ordinary `ULift` equivalence; finiteness is not a new hypothesis.
- `aX`, `aY`, `aY'` are the three structure morphisms to `Spec P.field.k`.
  Their `LocallyOfFiniteType` and `QuasiCompact` instances express finite type
  over k. `_hf` and `_hv` assert that f and v are k-morphisms.
  `IsSeparated f`, `LocallyOfFiniteType f`, and `QuasiCompact f` are the stated
  separated finite-type hypotheses. There is no smoothness hypothesis, no
  separatedness instance on any structure map, and no property assumption on v.
- `sq : IsPullback u' f' f v` is the Cartesian square, including its commutativity.
  A specified Cartesian object is equivalent to choosing the node's fibre product;
  no noncanonical map replaces its projections. `c : Compactification f` carries
  its open immersion, proper map, and factorization equality. `QuasiCompact c.i`
  is the node's stated quasi-compactness. `c.ofIsPullback sq` is exactly c prime.
  Properness of c.g and finite type of Y imply finite type of c.Z over k, and
  the same holds after base change to Y prime. No dimension bound is assumed.
- All etale categories are `DerivedCategory (Sheaf T.smallEtaleTopology
  (ModuleCat P.Coefficient))` and their `DerivedCategory.Plus` subcategories.
  Pro-etale categories use `Sheaf (Scheme.ProEt.topology T) (ModuleCat ...)`.
  This is the fixed-scalar presentation used by the recorded canonical comparison
  and exchange declarations, rather than modules on a different site or with
  different scalar coefficients. The small site's object/morphism universes are
  unchanged; coefficients are in u+1, schemes in u.
- `comparisonUpperStar.mapDerivedCategory` is C; `comparisonLowerStar.rightDerivedFunctor`
  is U; `derivedComparisonAdjunction.unit` is eta in ambient coordinates. Its
  bounded-below restriction is the unit in the dependency
  `CompactSupportComparisonUnit`. `leftDerivedUpperStarComparisonIso` is kappa.
- `Etale.rightDerivedLowerShriekOfCompactification[Plus]` and its pro-etale
  counterpart are the two chosen compact-support functors. The existing
  `compactExchangeTransportComparison` is C_c, constructed from the inverse of
  `compactSupportSiteComparison` and the published Plus compatibility. Its source
  and target paths are `compactExchangeTransportSource` and `...Target`, the S
  and T in the node. Their proper factors retain the canonical counit mate.
- `mateCounitExchangeIso` is S inverse, then C applied to the actual etale exchange
  isomorphism, then T. The theorem's first conjunct identifies its forward map
  with `rightDerivedLowerShriekOfCompactificationBaseChangeMap.app (C_X M)`.
  Thus its inverse in every subsequent expression is the inverse of the
  specified ambient exchange. The isomorphism is constructed from real data:
  the named etale finite-torsion theorem supplies the invertibility proof.
- `R`, `adj`, `R'`, `adj'` retain the chosen ordinary etale right adjoints and
  their actual Hom equivalences/counits. These are exactly the choices made by
  the node, not arbitrary pro-etale adjoints. `G : DerivedCategory.Plus ...`,
  `hM : t.plus (R.obj G.obj)`, and `_hR' : t.plus (R'.obj (v^*G).obj)` are
  precisely its boundedness conditions. The bounded-below object representing M
  is always the subtype `⟨R.obj G.obj, hM⟩`, not a freely chosen representative.
- `mateCounitEtaleCounit` inserts `...PlusCompatibility.hom` before the ambient
  counit; this renders epsilon^e in Plus coordinates. `mateCounitProCounit` is
  C_c inverse followed by C_Y applied to that counit, exactly epsilon^p.
- `mateCounitEtaleComposite` is the inverse of the specified etale exchange
  followed by v^* epsilon^e, the node's w. `mateCounitProComposite` is the inverse
  of E^p followed by Lv^* epsilon^p, the node's z. `mateCounitCancelled` is T
  followed by z followed by kappa_v inverse. The second conjunct says that it
  equals C_Y prime(w), which is identity (1), in Lean's left-to-right composition.
- `mateCounitEtaleTranspose` applies the actual `adj'.homEquiv` to w; the only
  extra arrow is the inverse Plus/ambient compact-support compatibility.
  `mateCounitProTranspose` first precomposes z with T, which is precisely
  C_c prime followed by F_c prime^p(kappa_u); then it applies the actual
  comparison Hom equivalence, applies J prime, applies C_X prime, and finally
  precomposes with kappa_u inverse. Expanding `Adjunction.homEquiv_unit` gives
  exactly the displayed U(z C_c prime) eta formula and the witness rule of
  the node. No ambient pro-etale compact-support adjunction is assumed.
- The third conjunct is kappa_u followed by beta^p equals C_X prime(beta^e)
  followed by C_X prime R prime(psi), exactly identity (2).
  `mateCounitTargetUnit` is eta followed by U(kappa_v), namely psi. Its `IsIso`
  conjunct records the target conjugating isomorphism explicitly; the source
  conjugating map is already a component of the natural isomorphism kappa_u.
  No invertibility of either beta is requested.
- The final universally quantified clause takes every H with the same two
  boundedness conditions and every arrow `a : G ⟶ H`. It states naturality of
  the cancelled map in (1), beta^e, and beta^p. `mateCounitInputMap` is merely
  u^* applied to R(a), packaged into the strictly full Plus subcategory.
  Together with the two identities this also supplies naturality of their
  right sides and of the comparison identity. There is no hidden restriction
  on arrows or on representatives.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `PurityFiniteSetting.Ring`, `PurityFiniteSetting.Coefficient` and their ring instances.
- `WeilConjectures.Compactification.BaseChange`: `Compactification.ofIsPullback`
  and `Compactification.baseChange`; `...Compactification.Refinement`:
  `Compactification.Refinement`, with the existing `Compactification` data.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and the recorded Mathlib
  derived-category API: `DerivedCategory`, `DerivedCategory.Plus`, `TStructure.t.plus`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: the recorded finite-coefficient
  module categories and comparison realization; the canonical fixed-scalar
  presentation is supplied by the following recorded repaired interfaces.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `siteComparisonDerivedPullbackPlus`, namely `comparisonUpperStar.mapDerivedCategoryPlus`.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `compactSupportSiteComparison` and `compactSupportSiteComparisonPlus`.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`: the canonical
  `supportSiteComparisonCoefficientPullbackIso` and its coherence. Its derived
  module specialization is `leftDerivedUpperStarComparisonIso`, as used by the
  recorded compact-support exchange transport module.
- `Sheaf.Paper.CompactSupportExchangeTransport`:
  `compactExchangeTransportComparison`, `compactExchangeTransportSource`,
  `compactExchangeTransportTarget`, and `compactSupport_exchange_transport`.
- `Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass`:
  `ComparisonClassAdjunction`, `exists_comparisonClassAdjunction`. The transpose
  is written directly in the node's explicit canonical normalization; it does
  not choose a fresh class adjunction or an unspecified compact-support iso.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`, its Plus functor and compatibility.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`:
  `rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`.
- `Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion`: `compactSupportFiniteTorsion`.
- `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`:
  `isLeftAdjoint_rightDerivedLowerShriekOfCompactification`, the ordinary etale adjoint.
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`:
  `isIso_compactSupportComparisonUnit`, `compactSupportComparisonUnit`.
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison`
  supplies `derivedComparisonAdjunction` and its actual ambient unit.
- `Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage`:
  `sfFiniteExceptionalFixed` and its canonical realization; its finite formula
  is U then the ordinary etale right adjoint then C, exactly the target of beta^p.
  `Sheaf.Paper.DerivedPullbackTensorHom` was read; the tensor and internal Hom
  clauses of that general operation node do not occur here. The finite derived
  inverse image used here is the same fixed-scalar `upperStar.leftDerivedFunctor`,
  already imported through the recorded exchange module. No new tensor/Hom
  definition or unrelated higher-coefficient imports are introduced.
- The scheme-properties dependency is a convention node with no declaration:
  its named Mathlib scheme properties above are used directly.

Edge cases: empty X, Y or Y prime remain permitted (there is no nonempty binder,
point, dimension maximum or nonnegative dimension equality). Zero G and its zero
maps are permitted. Identity v, identity compactification parts, arbitrary
nonsmooth separated finite-type f, and nonseparated structure maps are all
retained. The boundedness subtype records proofs only and does not change the
ambient objects or maps. All universes and variables are explicitly bound and
`autoImplicit` is false. Every definition has real data. The only postponed
proof is the named main theorem, whose docstring carries the five-step proof.
No `STATEMENT-DISPUTED` issue was found.

Searches:

- msearch LeanFinder: `Counit transpose cancellation for compact support exchange
  under etale proetale comparison` returned eight condensed-category counit
  declarations, none concerning these specified geometric maps.
- msearch Loogle: `CategoryTheory.Adjunction.homEquiv_naturality_right_square`
  found the generic declaration in `Mathlib.CategoryTheory.Adjunction.Basic`.
  Its full type is general Hom-equivalence naturality, not this geometric identity.
- msearch grep, Mathlib/CategoryTheory:
  `counit.*cancel|mate.*counit|homEquiv_naturality_right` returned 25 generic
  naturality/mate hits, no specified compact-support comparison statement.
- msearch LeanSearch: `Naturality of counit transposes under the canonical compact
  support site comparison` returned eight generic counit naturality declarations.
- rg in the upstream WeilConjectures tree and side `lean/Sheaf`, and the upstream
  name table: `mate_counit|mateCounit|counit.*cancellation|lem-pur-smb-mate-counit-cancellation`.
  Only unrelated ringed/affine/open counit cancellations were found, not either
  identity of this node. The direct upstream node-id search had no hits.
- Read the exact blueprint source proof, the item and every statement dependency,
  the recorded declaration signatures/docstrings, and the generic adjunction API.
  Published finite-coefficient comparison sources missing locally were obtained
  with the prescribed `scompile.py --source` wrapper.

Further duplicate-notion check: read `Etale.smoothExceptionalBaseChangeMap` in
`SmoothExceptionalBaseChange`, `smoothExceptionalComparisonMate` and
`smoothExceptionalProEtaleBaseChangeMap` in the parent
`SmoothExceptionalBaseChangeStatement`, and the scalar-extension `mateMap`.
These use canonical compactification-independent adjoints, a comparison-site
mate, or coefficient changes, respectively. None states the present two
identities for the specified c/c prime and supplied ordinary etale adjunctions.
Importing the downstream parent here would also reverse the proof dependency.
The present helpers spell out the new node's own named maps in those chosen
coordinates, and do not redefine a canonical library functor.

Elaboration repair: the initial componentwise `IsIso` synthesis in the definition
of w produced an expensive kernel proof term. The final definition takes the
inverse of `asIso` of the existing natural transformation and then its component;
it is the inverse of exactly the same exchange map. Explicit helper result types
prevent local invertibility proofs from leaking into inferred signatures. The
final source uses the default heartbeat settings and the required wrapper limit.

Validation: `scompile.py Q137 lem-pur-smb-mate-counit-cancellation` accepts the
final file in both sandbox and final-library module modes, with exit code 0 and
no warnings. There is exactly one theorem with `sorry`, no line over 100 columns,
no diagnostic options, and the node copy differs from the base only in `lean`.

## Second reading by Q137

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
