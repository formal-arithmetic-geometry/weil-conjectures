## Worker report

This delivery states `lem-weil-finite-duality-locally-closed-comparison` in
`Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison`. Its theorem
`AlgebraicGeometry.ProEtale.finiteDuality_locallyClosed_comparison` has `sorry` as its
entire proof. The second theorem `locallyClosed_comparison_factorization` states the
factorization-independence clause, also with an entire `sorry` proof. The helper
structures package precisely the adjunctions and equations asserted by this node.
No theorem was proved. Every definition contains real data; in particular Delta is a
composition of specified natural isomorphisms, never a choice from a Nonempty isomorphism.

The statement is unchanged. There are no new DAG nodes and no disputed statement.
The module docstring cites the current main-20261015 blueprint, whose second proof
paragraph was opened and read. The main theorem docstring carries all twelve current
DAG proof steps. The factorization theorem docstring gives the complete Step 12 argument.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* `D : WeilConjectures.FiniteFieldDatum.{u}` is the fixed algebraic closure of the finite
  field, retaining its prime `D.p`. `l`, `[Fact l.Prime]`, `_hl : l ≠ D.p` are exactly the
  prime and invertibility restriction in the node. `E`, `[Field E]`, `[Algebra (Padic l) E]`,
  `[FiniteDimensional (Padic l) E]` give the stated finite extension. The ring is the
  recorded `Padic.coefficientExtensionRing l E (n + 1)`, using its recorded uniformizer
  and valuation ring. Indexing positive levels by `n + 1` covers precisely every n >= 1;
  the explicit proof supplied to `Padic.finite_coefficientExtensionRing` supplies its
  finiteness, rather than adding a finite-coefficient hypothesis to the theorem.
* `S V T : Scheme.{u}`, `aS`, `aT`, their `LocallyOfFiniteType`, `QuasiCompact`, and
  `IsSeparated` instances are exactly separated finite-type k-schemes S and T.
  `c : S ⟶ V` with `IsClosedImmersion c`, `v : V ⟶ T` with `IsOpenImmersion v`, and
  `_hs : (c ≫ v) ≫ aT = aS` give the locally closed k-immersion and its chosen factorization.
  The node's s is the literal composite `c ≫ v`. There is no additional ambient V assumption.
* `IsNoetherian T` and `QuasiCompact (c ≫ v)` are existential proof witnesses in the
  conclusion, because finite type over k implies them; they are not extra premises.
  The Brown-adjoint interface at the closure compactification derives all of its
  local-Noetherian and compactness conditions from the immersion and T. It imposes none
  of those as a further premise on S or V.
* The categories are the existing `DerivedCategory (Sheaf ... (ModuleCat.{u+1} A))`
  on `T.smallEtaleTopology` and `Scheme.ProEt.topology T`. The small sites, their object
  universe u+1 and morphism universe u, and coefficient universe u+1 are retained.
  These are ordinary constant-A module sheaves, with no constructibility restriction
  on ambient adjunctions and no replacement of the pro-etale site.
* `locallyClosedEtaleExtension` and `locallyClosedProEtaleExtension` are F_et and F_proet.
  They use the existing R c_* and exact derived open extension. Closed pushforward is
  exact, so R c_* is the node's termwise c_*; no resolution-dependent substitute is made.
  `LocallyClosedComparisonAdjoints` supplies both ambient closed right adjoints together
  with their actual adjunctions. An adjunction determines its right adjoint up to the
  unique counit-compatible isomorphism, so these are coordinates for the specified
  ambient closed functors, not arbitrary candidate functors assumed in the theorem.
* `adjoints.etaleRight v` and `adjoints.proetaleRight v` are J_tau = Rc_tau^! v_tau^*.
  The definitions `etalePasted` and `proetalePasted` use literal `Adjunction.comp` after
  `mapDerivedCategoryAdjunction` for the open factor. Their units and counits therefore
  are the pasted ones on the ordinary unbounded categories, as required.
* The target domain is exactly the recorded
  `Etale.DerivedCategory.isBoundedConstructible A T`. The package's `bounded` field
  asserts J_et M lies in the standard t-structure's `plus`, for every such M.
  `gamma` is a natural isomorphism between the two displayed functors restricted to
  this full subcategory. Thus naturality, both directions, and all constructible inputs
  are included rather than an isolated isomorphism at one input.
* `fixedDirectImageComparisonIso A c` is the inclusion-transport of the exact named
  `fixedComparisonDirectImageMatePlus A c`, with invertibility from the recorded theorem.
  `locallyClosedExtensionComparison` first uses the specified open comparison at c_*L
  and then the specified closed mate under open extension, exactly Delta_L in Step 5.
  Its domain is all `DerivedCategory.Plus` etale L. No unbounded invertibility is asserted.
* The package's `counit` field is literally Delta at J_et M, followed by F_proet(gamma_M),
  followed by the pasted pro-etale counit, equal to nu_T^* of the pasted etale counit.
  The bound witness makes this Delta component well typed. This equation uniquely
  characterizes gamma as a transpose; by Steps 1--6 of the source proof it is precisely
  closed exceptional comparison composed with open restriction comparison. In particular
  no scalar twist or unspecified isomorphism with the same endpoints can satisfy it.
* `locallyClosedImageCompactification s` uses s.toImage and s.imageι, with the actual
  scheme-theoretic closure; it works without a density or nonemptiness assumption.
  `locallyClosedEtaleSheafIso` uses the existing uniqueness-normalized identity-on-S map
  of `etale_locallyClosed_extension_comparison`. Its theorem specifies the unique map
  by restriction, so choice here chooses a uniquely determined natural isomorphism.
  `locallyClosedEtaleSupportIso` localizes this map and the existing exact-closed
  direct-image identification. `locallyClosedEtaleRightIso` is adjoint uniqueness after
  that precise left identification, hence is the required counit-compatible J_et ≅ s-times.
* `transport` is a natural isomorphism from J_proet nu_T^* on bounded constructible
  targets to `sfFiniteExceptionalAt A` at that closure compactification. The latter is
  literally Rnu_T,* followed by the ordinary etale right adjoint followed by nu_S^*.
  It asserts no ambient pro-etale compact-support adjunction.
* `unit_normalization` says gamma followed by transport is
  nu_S^*(e_M ; s-times(eta_M)), where e is the specified adjoint identification. This
  is exactly nu_S^* s-times(eta_M) under J_et ≅ s-times. eta is the actual unit of
  `derivedComparisonAdjunction`, not an independently chosen full-faithfulness isomorphism.
* `relative_hom` compares the actual pasted ambient transpose with the specified
  `FixedComparisonClassAdjunction.homEquiv` at the same closure compactification. Its left
  comparison is explicitly the proper/open comparison B, inverse normalized q_et, and
  Delta. It quantifies over every bounded-below etale-origin K, every representative L,
  and every witness w : nu_S^*L ≅ K. Consequently equality is independent of the
  witness, and identifies units/counits wherever the relative adjunction defines them.
  The proof arguments hK and hM are evidence for the two domains of that Hom equivalence,
  universally quantified inside the conclusion, not extra premises restricting the theorem.
* `locallyClosed_comparison_factorization` compares any two factorizations with equal
  composite and any packages satisfying the asserted equations. It uniquely specifies
  the etale adjoint identification by the normalized closure comparison and the pro-etale
  comparison on the stated target domain by `transport`, then gives the gamma square.
  `HEq` records equality after equality of the composite scheme maps, without silently
  identifying differently indexed chosen functors. Uniqueness forces identity and cocycle
  laws. The adjunction maps being compared are the literal pasted maps above.

Dependency declarations used (and source signatures/docstrings inspected):

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the coefficient construction it imports.
* Mathlib `AlgebraicGeometry.Morphisms.ClosedImmersion`, `Proper`, `FiniteType`,
  `QuasiCompact`, and `AlgebraicGeometry.OpenImmersion`: `IsClosedImmersion`, `IsProper`,
  `LocallyOfFiniteType`, `QuasiCompact`, `IsOpenImmersion`; Mathlib `Adjunction.Basic`
  and `Adjunction.Unique`: `Adjunction.comp`, `rightAdjointUniq`, their counit formulas.
* `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategoryModule`, `Etale.DerivedCategory.isBoundedConstructible`,
  `Etale.BoundedConstructibleDerivedCategory`. The latter current source was read
  with `scompile.py --source`, because its recorded upstream path is absent locally.
* `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `FiniteCoefficientModules` and its canonical fixed-ring module realization;
  `ProEtaleIntrinsicExtensionByZero.sfIntrinsicExtensionByZero` and
  `ProEtaleIntrinsicClosedAmbient.sfIntrinsicClosedAmbientAdjunction` supply the
  intrinsic coordinates for the same constant-module constructions. Their full
  ordinary-category statements and support-kernel proof docstrings were read.
* `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`:
  `Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`;
  `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`:
  `Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`, used to construct
  the closure-adjoint instance from its actual hypotheses.
* `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison` and `proEtaleSiteComparisonModules`;
  `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`:
  `isIso_compactSupportComparisonUnit`; fixed-coefficient upstream Comparison:
  `comparisonUpperStar`, `comparisonLowerStar`, `derivedComparisonAdjunction`.
* `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `fixedComparisonDirectImageMatePlus`, `isIso_fixedComparisonDirectImageMatePlus`,
  `fixedComparisonPullbackPlus`, `fixedComparisonDirectImageMatePlus_counit`.
* `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`:
  `openImmersionLowerShriekComparisonUpperStarIso` and its coherence theorem;
  the actual etale/pro-etale `openImmersionLowerShriekUpperStarAdjunction`.
* `Sheaf.SixFunctors.EtaleLocallyClosedExtensionComparison`:
  `etale_locallyClosed_extension_comparison` and its unique restriction normalization;
  `WeilConjectures.SixFunctors.Finite.Exact`:
  `Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory`.
* Repaired dependency modules in this delivery: `FiniteComparisonClassAdjunction`
  (`FixedComparisonClassAdjunction`, `exists_fixedComparisonClassAdjunction`, three canonical
  comparison definitions) and `FixedFiniteExceptionalAt` (`sfFiniteExceptionalAt`).

Proof imports include the recorded exactness, coefficient comparison, localization,
open unit normalization, locally closed extension coherence and ringed adjunction modules.
The old `SupportComparisonPullbackCoherence` wrapper is not imported: it introduces
retired duplicate finite/generic comparison declarations; the actual inverse-image
comparison and its adjunction are already imported through the smaller fixed-mate API.
The now-landed Step 9–11 dependency `lem-pur-bounded-site-adjunction-transpose` is
imported through `Sheaf.Paper.BoundedSiteAdjunctionTranspose`. Its imports include the
original `EtaleOriginAdjointClass`, so every compile of the main module also verifies
that both relative-adjunction interfaces coexist. The complete proof steps remain
in the main theorem docstring.

Edge cases checked against the formulas: S empty, T empty (forcing S empty), S=T and
identity factorization, a pure open immersion, a pure closed immersion, zero complexes,
disconnected schemes, arbitrary bounded-below sheaves (no finite-stalk condition), the
first positive coefficient level n+1=1, and the zero-ring case of the generic helper
interfaces. Closure uses no nonempty-chart choice. No dimension of the empty scheme is
used. Both module-value and site universes retain their given sizes.

Searches: the prescribed msearch leanfinder query was
“Exceptional inverse image along a locally closed immersion commutes with etale to
proetale site comparison with counit normalization”; its eight hits were ordinary
scheme restriction identities, not this statement. The loogle query
`CategoryTheory.Adjunction.comp, CategoryTheory.Adjunction.rightAdjointUniq` returned
zero hits through that service (the actual Mathlib declarations were then opened directly).
The msearch grep query
`locallyClosed.*Comparison|locally_closed.*comparison|exceptional.*comparison` returned
zero Mathlib hits. The sandbox's searches.jsonl records the exact results. Direct rg of
`WeilConjectures/SixFunctors` and `lean/Sheaf/AlgebraicGeometry` for locally closed and
finite-duality comparison names found only the existing extension-coherence statements,
not the exceptional comparison. The exact item-id search of upstream WeilConjectures
returned no declaration. Existing extension comparison was reused, not duplicated.
The live generic and FiniteCoefficient derived source modules were opened with
`scompile.py --source` to inspect the recorded interface and chosen-map normalization.

## Dependency modules

`thm-sf-ambient-adjoint-class`: the recorded interface is unusable for this consumer
because its normalized Hom formula uses an arbitrary `.some`-chosen proper comparison,
which cannot express the equality required by the named `fixedComparisonDirectImageMatePlus`
counit mate. It also omits the node's explicit preservation of bounded-below (D+)
complexes by the transported right functor. `FiniteComparisonClassAdjunction` constructs
`fixedDirectImageComparisonIso` from the actual fixed mate, constructs the open/proper
compact-support comparison from it, and transports the canonical etale compactification
comparisons through these fixed maps. The repaired structure is exported under the fresh
name `FixedComparisonClassAdjunction` (with theorem
`exists_fixedComparisonClassAdjunction`) to avoid colliding with the existing
`AlgebraicGeometry.ProEtale.ComparisonClassAdjunction` export. The theorem retains the
FullCD bound, ordinary etale right adjoint, all relative Hom bijections, naturality,
witness independence, and compactification identity/cocycle/compatibility.

`def-weil-exceptional-inverse-image`: the recorded `SfFiniteExceptionalInverseImage`
uses A : Type u and Scheme.{u}, then lifts A to build fixed-ring modules. This cannot
accept the recorded coefficient-extension universe Type(u+1) while retaining Scheme.{u}.
`FixedFiniteExceptionalAt` reexports that existing interface and adds the exact same
finite transported composite directly over fixed-ring modules of the correct universe.
It works at the specified compactification; its etale right adjoint is characterized by
the ordinary compact-support adjunction. In this consumer that adjoint-existence class
is explicitly supplied by the existing Brown-adjoint theorem with all needed Noetherian
and compactness witnesses derived from the immersion. No new premise is imposed on
the main comparison theorem and no ambient pro-etale adjoint is assumed. Only the node's
`lean` field is changed; the original intrinsic definitions are reexported, and no
integral/scalar construction is replaced or asserted by the new finite-level helper.

## Second reading by Q43

This is the dispatcher worker's clause audit, not an independent reviewer signature;
the prescribed workflow assigns independent review to the maintainer. I reopened the
node and all delivered files and compared their binders, categories and equations.
The substantive interface faults found were the unspecified proper comparison in the
relative-adjunction normalization, the omitted D+ preservation
clause in that datum, and the too-small coefficient parameter in the transported functor.
The two dependency modules repair those faults without changing natural statements.
The main theorem retains characteristic and positive-level conditions, both separated
finite-type scheme hypotheses, the chosen closed/open factorization, bounded
constructible targets, all bounded-below etale-origin witnesses, and both normalization
equations. Gamma and transport are natural isomorphisms with equations, not bare
Nonempty maps. The factorization theorem records uniqueness and the gamma square;
the units/counits come from the explicit pasted adjunction definitions. Definitions
contain no sorry and the two main theorem proofs and repaired existence theorem are
exactly sorry. Compilation and delivery preflight are run through the required wrappers.


## Returned-delivery repair

R1: renamed the new relative-adjunction structure and existence theorem to
`FixedComparisonClassAdjunction` and `exists_fixedComparisonClassAdjunction`, updated
the dependency's Lean record and the item's `relative_hom` binder. The original
`EtaleOriginAdjointClass` declarations remain available to their existing importers.
The main module now imports `Sheaf.Paper.BoundedSiteAdjunctionTranspose`, making the
requested compatibility check part of its ordinary single-file compile.

R2: removed the incorrect claim that the recorded `EtaleOriginAdjointClass` module
fails to compile with a duplicate `derivedComparisonAdjunctionPlus`. The dependency
record and this report now give the actual two interface defects: its arbitrary
`.some`-chosen proper comparison in `homEquiv_normalized` and its missing D+
preservation clause. The helper structure's docstring also explicitly records its
`boundedBelow` clause. The informal node statements remain unchanged.


Validation: `scompile.py Q43 lem-weil-finite-duality-locally-closed-comparison`
with all three delivered modules and `checks/LocallyClosedCombinedImports.lean`
returned exit code 0 with no warnings or errors. The check file imports the item
and `Sheaf.Paper.BoundedSiteAdjunctionTranspose` together and successfully checks
both `ComparisonClassAdjunction` and `FixedComparisonClassAdjunction`, the repaired
existence theorem, the item theorem, and `boundedSiteTranspose`. It is a sandbox-only
validation artifact, outside the delivered `lean/` modules.
