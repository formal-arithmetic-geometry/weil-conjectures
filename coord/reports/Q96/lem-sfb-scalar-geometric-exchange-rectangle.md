## Worker report

The module `Sheaf.Paper.ScalarGeometricExchangeRectangle` states
`AlgebraicGeometry.ProEtale.QuotientChange.scalar_geometric_exchange_rectangle`,
with its sole proof `sorry`. The original three helpers name the internal ambient
exchange and its two routes. Eight additional real definitions expose the fixed
pushforward comparison, the normalized section lambda, its actual rho mate, the
section exchange, the source and target comparison isomorphisms, and both section
routes. These assemble the existing constructions without replacing their data.

Hypothesis and clause correspondence:

- The commutative condensed rings are the explicitly bound sheaves `Λ`, `Λ'` on
  `coherentTopology Profinite.{u}`, with `MonObj` and `IsCommMonObj` instances.
  `φ : Λ ⟶ Λ'` with `IsMonHom φ` is their ring-object morphism.
- `Modules Λ T` is precisely internal modules over `condensedRingObj Λ T` on
  `Scheme.ProEt.topology T`. `D φ T` is the total derived extension of scalars,
  `L Λ h` and `F Λ h` the ordinary unbounded geometric derived functors.
  They use the actual pulled-back coefficient maps from the point.
- `sq : ChosenCartesianSquare a f' f c` supplies the chosen cartesian square,
  including its scheme pullback identification and its commutativity equation.
- `b h : D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U` is exactly λ_h with the
  functional composition convention translated to Lean's left-to-right `⋙`.
  `normalized` requires the existing `PullNormalized φ h (b h)` equation, fixing
  the universal computation counits and ordinary pure-tensor `pullIso`.
  This is the specified balanced K-flat comparison, not a freely chosen
  isomorphism or an added square-coherence assumption. Quantification over a
  normalized family states the result for the canonical family supplied in the
  node, independently of its choice of representative.
- `rho φ h (b h)` is the existing `mateEquiv` with `adj Λ h`, `adj Λ' h`.
  Its counit transpose is exactly `b.hom` followed by `D` of the integral
  counit. No alternative geometric adjunction is supplied by a hypothesis.
- `scalarAmbientExchange R sq` is definitionally the recorded
  `CondensedRing.condensedAmbientExchange R sq`; its `by unfold; exact` body
  only exposes the irreducible named functor wrappers `F` and `L`.
- `scalarExchangeLeft φ sq b J` is, in Lean composition order,
  `c*.map (rho_f.app J) ≫ Ex_new.app (T_X.obj J) ≫ Rf'*.map (λ_a.app J)`.
  This is exactly the left side of the displayed equation.
- `scalarExchangeRight φ sq b J` is
  `λ_c.app (Rf*.obj J) ≫ T_C.map (Ex_old.app J) ≫ rho_f'.app (a*.obj J)`.
  This is exactly its right side.
- Both helper signatures display source `c* T_Y Rf* J` and target
  `Rf'* T_X' a* J`, in `DerivedCategory (Modules Λ' C)`.
  `J` is any derived object, with no boundedness, completeness or
  constructibility restriction.
- The first conclusion is the unchanged internal rectangle equality. The second
  now explicitly realizes the normalized section rectangle. It supplies
  `s : ∀ T, SectionScalarComparison φ T`, their `SectionScalarNormalized`
  properties, and `p : ∀ h, SectionPullNormalized φ h (s U) (s V) (b h)`.
  These are existential conclusions: no new normalization hypothesis is imposed.
- `sectionRectangleLambda φ h ... (p h)` selects the *d* already appearing in
  `SectionPullNormalized`, retaining the independent ordinary conjugation and
  K-flat computation square. Its final equation uniquely determines d after
  precomposition by the essentially surjective section equivalence and conjugation
  by isomorphisms. Therefore the choice determines a canonical comparison; it is
  not data selected from an existence claim that fails to determine the object.
  This is an existing predicate and witness, not a copied normalization predicate.
- `sectionRectangleRho` is `mateEquiv` applied to this lambda under the two actual
  `ModuleRingedComparison.derivedAdjunction` values. Its transpose is exactly
  scalar extension of the old counit after lambda. No arbitrary section map or
  transported replacement for the ringed adjunction is supplied.
- `sectionRectangleExchange R sq` is precisely the section expression in the last
  conjunct of `GeometricAgreement` in `IntegralQuotientSectionMateRealization`:
  the mate of the inverse `(f',c)` section compositor, the equality of composite
  morphisms, and the `(a,f)` section compositor. It uses g'=a, g=c and the actual
  independently constructed section adjunctions; no integral coefficient
  specialization or downstream exchange-rectangle theorem is imported.
- `sectionRectangleLeft` and `sectionRectangleRight` spell out respectively
  `c_B*.map(rho_f) ≫ Ex_B ≫ Rf'_B.map(lambda_a)` and
  `lambda_c ≫ T_C.map(Ex_A) ≫ rho_f'`, at `D(E_X).obj J`.
- `sectionRectangleSource` identifies the realization of the internal source
  with the section source by pullback comparison, scalar comparison, then the
  pushforward comparison under the section scalar functor and section pullback.
  `sectionRectangleTarget` identifies the target by pushforward comparison,
  scalar comparison, then pullback comparison under scalar and pushforward.
- The two explicit realization equations are
  `Source.inv ≫ derivedFunctor.map(internalLeft) ≫ Target.hom = sectionLeft`
  and the corresponding equality for the right route. The final conjunct is
  `sectionLeft = sectionRight`. Unlike the returned `congrArg` conjunct, these
  assert agreement with the independently normalized section factors.
- Explicit universe `u` keeps site object universe `u+1` and morphism universe
  `u`; coefficients are `Ab.{u+1}`. The `HasDerivedCategory.{u+1}` family is the
  ordinary section-localization size data used by the recorded realization,
  now for both Λ and Λ' to type the explicitly named section routes, matching
  `def-weil-size-convention`, not a geometric condition. All variables
  are bound and `autoImplicit` is false.
- No flatness, properness, constructibility, completeness, invertibility of rho,
  or invertibility of exchange hypothesis occurs.

Dependency declarations read and used:

- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPullback`, `moduleObjectDerivedPushforward`;
  its public upstream `Derived.UpperLowerStar` gives the specified
  `derivedUpperStarLowerStarAdjunction` and `leftDerivedUpperStarComp`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `condensedPullbackHom`, `coefficientPullbackIso`, `condensedPushforwardHom`,
  their ring-object instances, and `condensedPushforwardHom_comp`.
- `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`:
  `Mod.derivedExtendMapDerivedCategoryAdjunction` and the generic
  `leftDerivedFunctor`; scalar extension is their prescribed composite.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare`.
- `Sheaf.Paper.CondensedAmbientExchange`:
  `CondensedRing.condensedAmbientExchange`, `condensedAmbientPullbackComparison`.
- `Sheaf.Paper.KFlatScalarComparisonNormalization`:
  `SheafOfModules.ScalarPullback.kflat_scalar_comparison_normalization`,
  `θ_composition`, `θ_identity` (proof import).
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`, `mateEquiv_counit`.
- `Sheaf.Paper.InternalDerivedScalarComparisons`:
  `QuotientChange.Modules`, `D`, `L`, `F`, `adj`, `PullNormalized`, `rho`.
- `Sheaf.Paper.SectionDerivedTensorData`:
  `ModuleRingedComparison.modules`, `derivedFunctor`, `derivedEquivalence`.
- `Sheaf.CategoryTheory.InternalSectionScalarAdjunction`:
  `InternalAbelianSheafModule.internal_section_scalar_adjunction` (proof import).
- `Sheaf.Paper.SectionDerivedPushpullNormalization`:
  `ModuleRingedComparison.sectionDerivedPushpullNormalization` (proof import).

The existing definition nodes `def-sfb-internal-derived-scalar-comparisons` and
`def-pd-section-derived-tensor-data` are retained in stmt_deps. The repair also
cites the landed owners `def-pd-section-derived-realization` (geometric comparisons,
section adjunction and compositor), `def-sfb-scalar-hom-comparison-data` (the
universal ScalarDerivedPair), and `def-sfb-section-scalar-map-data` (its coefficient
map); and the new definition owner
`def-sfb-internal-section-scalar-pullback-comparison-data` (the four existing
section comparison definitions). The normalization theorem
`lem-sfb-internal-scalar-pullback-normalization` remains a proof dependency only.
No copied predicate, dependency record or mathematical statement is changed. The theorem docstring retains all six proof steps and both transposes.

Edge cases checked: empty schemes, zero derived objects, identity coefficient
maps and identity geometric edges are allowed by every binder. Non-flat ring maps
are unrestricted. Neither rho nor Ex is cancelled in the natural-language proof.
The universe convention retains the actual small pro-etale site universes.

Searches for an exact existing statement:

- `msearch.py`, LeanFinder: “Derived extension of scalars commutes with the
  geometric base change exchange through normalized adjunction mates” returned
  `ModuleCat.homEquiv_extendScalarsComp`, scalar associativity and unit lemmas;
  none states this unbounded internal geometric rectangle.
- `msearch.py`, Loogle: `CategoryTheory.mateEquiv` returned the generic mate
  equivalence, its counit formulas and horizontal/vertical pasting lemmas. They
  are the formal tools, not the coefficient/geometric specialization.
- `msearch.py`, grep: `scalar.*exchange|exchange.*scalar`, Mathlib CategoryTheory,
  returned no matches.
- `msearch.py`, LeanSearch: “Derived change of coefficients commutes with
  geometric base change via adjunction mates” returned linear base change,
  generic `mateEquiv`, and derived adjunction factorization equations; no match.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item id and proposed declaration names found no exact statement.
  Concept searches for scalar/geometric exchange and `PullNormalized` found the
  existing `InternalDerivedScalarComparisons` interface, which is reused.
  Etale scalar mates and the integral residue specialization have different
  coefficients or sites and do not state this result.

Source read: the current blueprint refinement proof, part (2), and the local
Stacks `sites-cohomology.tex` remarks `remark-base-change` and
`remark-compose-base-change-horizontal` (07A7 and 0E47). They use precisely
unit-square-counit exchange and formal mate pasting, without flatness assumptions.

## Returned point H3

The immutable returned head was 7870af9fd6fe. On resumption the saved original
packet passed `deliver2.py --no-push` as c3fb1808fa6. That mechanical pass did not
repair H3, so the realization conjunct was replaced as described above. The
internal equality, canonical b normalization, rho and exchange, all unrestricted
scheme/coefficient binders and their universes are preserved. The change adds the
missing interpretation of step 6; it does not correct the natural-language node.

Additional dependency declarations read in full:

- `Sheaf.Paper.InternalScalarPullbackNormalization`: `SectionScalarComparison`,
  `SectionScalarNormalized`, `scalarSectionPullComparison`, `SectionPullNormalized`,
  `internal_scalar_pullback_normalization`.
- `Sheaf.Paper.SectionDerivedRealization`: `derivedPullComparison`,
  `derivedPushComparison`, `derivedAdjunction`, `derivedPullbackComposition`.
- `Sheaf.Paper.IntegralQuotientSectionMateRealization`: the final exchange conjunct
  of `GeometricAgreement`, read for its exact formula (not imported or specialized).
- `Sheaf.Algebra.Homology.ScalarInternalHomData`: `ScalarDerivedPair`,
  through the recorded section scalar interface. This is the same independently
  normalized universal pair used by SectionScalarComparison.

Repair searches: `rg` for `SectionScalarComparison`, `SectionPullNormalized`,
`derivedPushComparison`, and `GeometricAgreement` in the project's Lean and DAG
located these landed owners. `rg` for the new helper names in WeilConjectures,
Sheaf and dag/lean_names_upstream.json found no preexisting declarations. The
original three external searches above remain applicable to the theorem; the final H2 repair below adds a definition ownership node for the existing
comparison data, without introducing a new implementation.

## Second reading by Q96

Repair self-check with the item, returned point, full module and owning declarations
open: both internal routes are unchanged; both section routes use the same
orientation and endpoints. The source inverse starts at c*_B T_Y Rf*_A D(E_X)J;
the target comparison ends at Rf'*_B T_X' a*_A D(E_X)J. The two realization equations
therefore compare maps with identical section endpoints. Lambda is the independently
K-flat-normalized witness, rho its specified mate, Ex the geometric compositor mate.
The existence of s and p is asserted, not assumed; the realization clause is no
longer a consequence of the internal equality alone. All added data is real; only
the one named theorem is sorry. Empty schemes, zero objects and zero target ring,
identity coefficient maps and square edges, arbitrary nonflat maps and unbounded
J remain admitted. The extra section size family for Λ is needed to express the
old-coefficient section operations and excludes no case under the size convention.
No statement correction or dependency record repair is needed. The dispatcher
forbids subagents; the independent mathematical reading remains the maintainer's.

Validation: repaired `scompile.py` passed for the sandbox module (37.6 s) and
`Sheaf.Paper.ScalarGeometricExchangeRectangle` (24.5 s), with no errors or warnings.
`deliver2.py --no-push` then passed preflight and compilation as acfcaeea7a4.
No global build or direct live repository mutation was run.


## Returned point H2 (492d472edfc2)

The retained packet first passed the required initial dry run as 08a8e9fafd2.
That mechanical pass does not resolve the independent H2 finding. Replaced the
added theorem stmt_dep `lem-sfb-internal-scalar-pullback-normalization` with
`def-sfb-internal-section-scalar-pullback-comparison-data`, retaining the theorem
in proof_deps. The Lean module is unchanged. The item differs from current main
only in lean and authorized added definition stmt_deps. The delivery wrappers
rebuild the packet on current main; no direct git command was run.

## New nodes

`def-sfb-internal-section-scalar-pullback-comparison-data` owns the existing
`SectionScalarComparison`, `SectionScalarNormalized`, `scalarSectionPullComparison`
and `SectionPullNormalized` in `Sheaf.Paper.InternalScalarPullbackNormalization`,
with existing:true and a verbatim primary structure signature. Its TeX statement
describes exactly those four notions: scalar comparison data; identity-on-sections,
balanced-generator and K-flat computation equations; the fixed geometric pullback
comparison; and the existential ordinary conjugate/derived computation/realization
equations. It cites all seven definition owners requested in the return.
The source is the current integral proper-base-change proof (1),(3), with the
Stacks places in the existing docstrings. LeanSearch returned flat scalar algebra
results, LeanFinder ordinary IsBaseChange and extension/restriction adjunction
results; Mathlib grep returned zero exact-name hits. Project and DAG grep found
exactly the existing implementation and its theorem record, but no definition
owner. Blueprint searches returned no definition. Full search outputs and
queries are retained in the new node's mathlib_searches. No Lean copy is added.

Second reading of the H2 repair by Q96: read all four definitions with their
docstrings and the entire item's retained Lean statement. The structure has
the actual ScalarDerivedPair and three comparison isomorphisms; the first
predicate has precisely the restriction, generator and flat-term K-flat counit
clauses. scalarSectionPullComparison unfolds only the internal L wrapper. The
second predicate quantifies r, c and d, pins r sectionwise, c by conjugation, d
by its K-flat square and final realization equation. All are plain definitions
before the theorem; none selects data from that theorem. The new node states
these data, without asserting their existence. Its seven dependencies own the
section map/generator, scalar derived pair/computation map, geometric realization,
localized section equivalence, internal scalar functors, K-flatness and flatness.
The theorem's internal equality, existential normalized section comparisons,
two route-realization equations, section equality, universes and all edge cases
remain unchanged. No statement_change is needed and no point remains disputed.

H2 validation: scompile.py passed sandbox and library module checks (37.6 s and
24.5 s), with no errors or warnings. The repaired packet then passed the server
preflight and all per-file compilation in deliver2.py --no-push as cb30088e69e.
The preflight also checked the existing definition module. The retained item
Lean SHA256 is ab0af532829a29e7a0b76d549943572b2fdb8f72ff6183032e69e713a756335b.
Self-check: item changes only lean and added definition stmt_deps; new node
statement citations equal its seven dependencies; theorem retained in proof_deps
and removed from added stmt_deps; all four existing definition names recorded.
