## Worker report

The module `Sheaf.SixFunctors.FiniteFreeImageComparison` states
`AlgebraicGeometry.Etale.finiteFreeImageComparisons`, with one sorry and no proved
lemmas. Four real helper definitions expose the basis inclusions, compact-support
projection and restriction maps, and the finite-sum/inverse equations. They belong
to the item's comparisons, rather than introducing independent notions. The module
and the theorem docstring cite the blueprint source and give all seven proof steps.

The statement is unchanged. Its clauses are rendered as follows.

- Finite commutative rings: `{A B : Type (u + 1)}`, `[CommRing A]`, `[CommRing B]`,
  `[Finite A]`, `[Finite B]`. The given ring map is represented by `[Algebra A B]`
  and `algebraMap A B`; every commutative ring map supplies exactly this structure.
- Free rank r: `(r : ℕ) (basis : Module.Basis (Fin r) A B)`. Quantifying over an
  arbitrary basis expresses the assertions for every basis, and supplies the finite
  freeness assumed by the statement. There is no nonzero-ring or positive-rank binder.
- The categories are precisely `DerivedCategoryModule A T` and `DerivedCategoryModule B T`,
  namely the ordinary small-etale unbounded derived categories of ModuleCat-valued
  sheaves, as the recorded derived-category dependency requires. The size convention
  has scheme universe u, coefficient/module universe u+1; no site-universe equality.
- T and U are the published `scalarExtension` and `Sheaf.derivedRestrictScalars`.
  The chosen left adjoint used by scalarExtension is the existing ordinary derived
  tensor extension, not a new functor or an assumed comparison.
- Arbitrary scheme morphism: `∀ {V W : Scheme.{u}} (f : V ⟶ W)`.
- The canonical unbounded restriction map is the existing
  `scalarRestrictionDirectImageMap`; `IsIso` on the natural transformation gives
  its natural isomorphism on every unbounded B-object N.
- The projection is the existing `scalarMate`; `IsIso` on it gives a natural
  isomorphism on every unbounded A-object K. The next equality writes its B-counit
  transpose explicitly as `scalarPullbackIso.hom` followed by scalar extension
  of the A-counit. No arbitrary projection map is quantified over.
- The existential family `e T K` is the basis insertion isomorphism from r copies
  of K to UTK. Its columns are fixed to `finiteFreeImageBasisInclusion`, the scalar
  unit followed by multiplication by the actual basis element. This is k ↦ k⊗b_j;
  the B-scalar multiplication takes place before restriction, so the inclusions
  themselves are only A-linear, as required.
- `FiniteFreeImageCoordinates` writes each restricted projection column as FA(i_j).
  The inverse is the explicit `biproduct.lift` of FA applied to `eV.inv ≫ π_j`,
  followed by eW.hom. Both inverse identities are asserted. These projections are
  uniquely determined by the basis, so they are the coefficient maps λ_j, not
  arbitrary inverse data. Column equality plus the basis isomorphism states exactly
  equality with the finite-sum comparison, including the empty-sum case.
- Compact support is quantified over `c : Compactification f`, with Noetherian V,
  W and c.Z. Its stored open immersion c.i, proper c.g, and factorization are used.
  FA/FB are the recorded `rightDerivedLowerShriekOfCompactification`, whose body is
  Dj_! followed by Rp_*. There is no assertion of compactification existence.
- `finiteFreeCompactRestrictionMap` pastes the canonical direct-image restriction
  with the inverse of the published open restriction identification.
  `finiteFreeCompactImageMap` is c_p followed by Rp_* of the actual open scalar
  comparison. IsIso is asserted for both natural transformations.
- `OpenScalarExtensionNormalization` fixes q on K-flat representatives; the next
  derived restriction equation states its identity on the open under the canonical
  tensor identifications. The ordinary open scalar equation spells out the same
  identity before derivation, using `openScalarExtensionZero` and
  `openScalarRestrictionZero`. For Uj_!, the displayed unit equation is its identity
  restriction under `upperStarRestrictScalarsIsoSheaf`. For maps t with image disjoint
  from the open, the pulled-back ordinary q and scalar restriction identification
  are explicitly zero. These are the unique maps between zero objects off the open.
- The final `FiniteFreeImageCoordinates` gives exactly the compact-support columns
  FA(i_j) and inverse row FA(p_j), using the same basis isomorphisms as direct image.
- There is no boundedness, constructibility, torsion, finite cohomological dimension,
  finite type, or separatedness hypothesis. A structure morphism to any field is
  covered when a compactification is supplied; a closed immersion is covered by its
  proper identity-open compactification. No additional special-case clause is needed.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: imports the recorded
  `AlgebraicGeometry.Etale.DerivedCategoryModule`; torsionCohomology is not imposed.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  general ring-sheaf presentation; its ModuleCat constant-coefficient presentation
  is the one fixed by the derived-category dependency.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`: publicly retains generic
  `SheafOfModules.DerivedChangeOfRingsCochainModel`. The already-published
  `Sheaf.Paper.EtaleDerivedScalarTensor.scalarExtension` supplies its constant
  ModuleCat-sheaf realization and is imported by the scalar-mate module.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`: recorded general
  `SheafOfModules.restrictScalars`; constant-coefficient realization is the existing
  `Sheaf.derivedRestrictScalars`, retaining the sectionwise scalar action.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`:
  `rightDerivedLowerStarProjectionMap`, publicly imported by the scalar-mate module.
  `scalarMate` is its changing-coefficients counterpart with the same counit convention.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`.
- Added already-landed statement dependencies, using declaration ownership:
  `def-pur-etale-scalar-mate` owns `scalarMate` and
  `def-pur-etale-scalar-pullback-iso` owns `scalarPullbackIso`, both in
  `Sheaf.Paper.PurEtaleScalarMateProjection`.
  `def-kun-scalar-restriction-comparison-maps` owns
  `scalarRestrictionDirectImageMap` in
  `Sheaf.Paper.EtaleUnboundedRestrictionComparison`.
  `def-sf-etale-open-scalar-data` owns `derivedExtension`, `derivedRestriction`,
  `openScalarExtension`, `openScalarExtensionZero`, `openScalarRestrictionZero`
  and `openScalarRestrictionMap` in `Sheaf.SixFunctors.EtaleOpenTensorDefs`.
  `lem-coef-etale-open-comparison-data` is a genuine theorem dependency in that
  same module: `openScalarRestriction` is `asIso (openScalarRestrictionMap φ j)`
  using `openScalarRestrictionMap_isIso`; that node also owns the predicate
  `OpenScalarExtensionNormalization` used in the statement. No conclusion of
  `scalarMate_restrict_eq_projection` or `etaleOpenTensorComparisons` is used to
  define any map or object here. `lem-coef-etale-open-tensor` remains solely an
  inherited proof dependency, with a plain import.
- `WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange`:
  `openImmersionLowerShriekRestrictScalarsIso` and
  `derivedRestrictScalarsCompOpenImmersionLowerShriekIso`, with their full unbounded
  signatures. Its finite-cohomological-dimension direct-image isomorphism is NOT used.
- Every already-stated proof dependency is imported (ordinary import when needed
  only for the future proof), including the K-injective, exact derivation, tensor,
  scalar-Hom, sheafification, and algebraic inverse-image comparison interfaces.
  The convention `def-weil-scheme-morphism-properties` introduces no declaration.

Edge cases checked before writing: r=0 forces the zero coefficient ring and all
basis sums and their inverse equations are empty; no positivity assumption appears.
For identity coefficient extension the unit/basis and counit composites become
identity comparisons. For A→A×A, the columns are the two inclusions and the inverse
is the two projections. Empty schemes and the empty open give zero categories/maps.
The identity open and the identity compactification recover direct image. Arbitrary
unbounded complexes are allowed throughout; no vanishing bound is hidden in a helper.

Searches made:

- msearch.py leanfinder: "Finite free scalar extension commutes with unbounded derived
  direct image and compact support with finite sum normalization": 8 hits, chiefly
  Condensed.profiniteSolidCounit, Condensed.profiniteSolid, and sheaf pullback free
  infrastructure; none is the node's comparison with these normalizations.
- msearch.py loogle: `"mapBiproduct"`: 5 hits, including Functor.mapBiproduct,
  mapBiproduct_hom, mapBiproduct_inv; finite-sum infrastructure only.
- msearch.py grep: `finiteFree.*[Pp]ush|[Dd]irectImage.*[Ss]calar|preservesFiniteBiproductsOfAdditive`:
  one Mathlib hit, the additive-functor preservation instance; no full statement.
- rg in WeilConjectures and Sheaf for the item id and finite-free/direct-image/scalar
  names: no declaration of this item. Existing scalarMate and restriction maps were
  found and reused. The existing bounded-below restriction comparison and the
  unbounded comparison requiring a dimension bound cannot state this node's theorem.
  FiniteFreeDerivedScalarCalculus requires Noetherian schemes and additionally states
  tensor/constructibility laws; it is not a replacement for arbitrary-scheme direct
  image. DerivedFiniteFreeScalarCoordinates is a general ring-sheaf presentation and
  has neither the geometric direct-image nor compact-support clauses.

No new nodes, dependency repairs or statement correction. No disputed assertion.
The only postponed proof is `finiteFreeImageComparisons`, with its matching DAG node.

## Second reading by Q100

Repair reading with the live DAG node, its blueprint source paragraph, the saved
module and the owning declarations open. This records the dispatched worker's
clause-by-clause check; the maintainer supplies the independent review, as the
brief prohibits starting another agent.

| Node hypothesis or clause | Lean counterpart checked | Finding |
| --- | --- | --- |
| A→B is a map of finite commutative rings | `{A B : Type (u + 1)}`, both `CommRing` and `Finite` instances, `[Algebra A B]`, `algebraMap A B` | Every unital commutative ring map induces the displayed algebra structure, including zero rings; no coefficient map is lost. |
| B is free of finite rank r; every basis may be used | `(r : ℕ) (basis : Module.Basis (Fin r) A B)` | The basis is universally quantified. There is no positive-rank or nontriviality hypothesis. |
| Ordinary small-etale module derived categories, T and exact U | `DerivedCategoryModule A T`, `scalarExtension`, `Sheaf.derivedRestrictScalars` | Read their source signatures: these are unbounded ordinary ModuleCat-valued sheaf derived categories; module universe u+1 accommodates the small-etale site of Scheme.{u}. No bounded category or completed tensor appears. |
| f is any scheme morphism | `∀ {V W : Scheme.{u}} (f : V ⟶ W)` in the direct-image conjunct | No Noetherian, properness or dimension binder applies to this conjunct. |
| The canonical restriction comparison is an isomorphism on every unbounded N | `IsIso (scalarRestrictionDirectImageMap (algebraMap A B) f)` | This is IsIso of the natural transformation between the full B-derived-category functors, so it covers every N and is natural. Its body is the mate of the exact restriction/pullback square, with the required U Rf → Rf U direction. |
| The canonical projection c is a natural isomorphism on every unbounded K | `IsIso (scalarMate (algebraMap A B) f)` | Its source is Rf_A followed by T_W; its target is T_V followed by Rf_B. The existing plain def fixes c by `mateEquiv`, rather than assuming any isomorphism. |
| The transpose is extension of the A-counit using canonical pullback/tensor | The equality beginning `L(upperStar ... B ...).map ((scalarMate ...).app K)` | Its left side is pullback of c followed by the B-counit. Its right side is `scalarPullbackIso.hom` followed by `scalarExtension.map` of the A-counit. The source objects and composition direction match. |
| Under any basis, UTK is K to the r-th finite direct sum with specified inclusions | Existential isomorphisms `e T K` and `biproduct.ι ... j ≫ (e T K).hom = finiteFreeImageBasisInclusion ...` | The helper is the scalar-adjunction unit followed by restriction of multiplication by `basis j`. Thus the column is k↦k⊗b_j, with no arbitrary insertion map. |
| After restriction and the displayed d, c is the finite-sum map with Rf(i_j) columns | First conjunct of `FiniteFreeImageCoordinates`, specialized to `R(lowerStar ... A f)` and `R(lowerStar ... B f)` | Read the expanded formula: i_j on W is followed by U(c), then d at T_V K, and equals FA(i_j). This is exactly the conjugated finite-sum comparison. |
| The inverse is given by Rf of the coefficient projections | Last two conjuncts of `FiniteFreeImageCoordinates` | The proposed inverse is `biproduct.lift (fun j ↦ FA.map ((eV K).inv ≫ biproduct.π ... j)) ≫ (eW (FA.obj K)).hom`; both composite identities are asserted. The inverse of the pinned basis isomorphism gives precisely the coefficient projection, including r=0. |
| No boundedness or cohomological dimension condition | Quantification over all `DerivedCategoryModule` objects; inspect all helper signatures | Neither the theorem nor its helpers assumes boundedness, constructibility or a vanishing bound. Finite rings and a finite basis are the only coefficient conditions. |
| Chosen compactification and Noetherian schemes; F_R=Rp_*j_! | `(c : Compactification f)` with `[IsNoetherian V] [IsNoetherian W] [IsNoetherian c.Z]`; `rightDerivedLowerShriekOfCompactification` | c stores the open immersion, proper morphism and factorization. The functor body is degreewise derived open extension followed by unbounded Rp_*. No compactification is postulated for an arbitrary f. |
| Canonical scalar/open comparison is identity on the open | `OpenScalarExtensionNormalization ... (openScalarExtension ...)`, the following derivedRestriction equality, and the ordinary `upperStar.map (openScalarExtensionZero.hom.app M)` equality | The predicate fixes q on K-flat representatives by the actual ordinary q. The two unit-inverse equations give the derived and ordinary on-open identities under the canonical scalar/restriction tensor identifications. The normalization conjunct is retained because it pins the derived map to that ordinary pure-tensor formula. |
| Canonical U/open comparison is identity on the open | Equation starting with `(openImmersionLowerShriekUpperStarAdjunction ... A ...).unit.app` | The open unit, pulled-back canonical restriction identification, and `upperStarRestrictScalarsIsoSheaf.hom` compose to restriction of the B-open unit, expressing the identity on the open. |
| Both open comparisons are the unique zero maps off the open | `Disjoint (Set.range c.i.base) (Set.range t.base)` implies the two `upperStar.map ... = 0` equations | This quantifies over every scheme map t avoiding the open, including the empty scheme. Both q and the U/open comparison are tested; no additional support assumption on input objects is made. |
| U_W F_B≅F_A U_V and c! is a natural isomorphism | `IsIso (finiteFreeCompactRestrictionMap ... c)` and `IsIso (finiteFreeCompactImageMap ... c)` | Open restriction is inverted before whiskering by Rp_A. The c! helper is exactly c_p followed by Rp_B of q; neither comparison is a free parameter. |
| After restriction c! has F_A(i_j) columns, and the finite-sum inverse | Final `FiniteFreeImageCoordinates basis` with the two compact-support functors and the same `e V`, `e W` | Expansion gives the F_A images of the same basis inclusions and coefficient projections, with both inverse identities, matching the direct-image normalization. |
| Structure morphism to a field and a closed immersion are included | Compact-support conjunct quantifies over every f and supplied c with the stated Noetherian instances | There is no restriction on the base beyond those stated. An identity-open compactification covers a proper closed immersion; a supplied compactification covers the structure-morphism case. |

H2 repair found and made: the saved packet had added three theorem nodes merely
for their plain definitions. The live node has the original seven stmt_deps and
no Lean record. Preserve all seven; replace only the saved packet's three added
theorem references by the four already-landed owning definition nodes
`def-pur-etale-scalar-mate`, `def-pur-etale-scalar-pullback-iso`,
`def-kun-scalar-restriction-comparison-maps`, `def-sf-etale-open-scalar-data`.
Also cite `lem-coef-etale-open-comparison-data`, following the return's first
option: `openScalarRestriction` really uses its invertibility theorem via
`asIso`, and this node owns `OpenScalarExtensionNormalization`. The source
`scalarPullbackIso` uses the unique normalized witness, owned by its definition
node, rather than any direct-image projection theorem. These references are
existing live declarations; no node or notion is duplicated.

Import visibility now follows those dependencies: EtaleOpenTensorDefs and
EtaleUnboundedRestrictionComparison are public, while EtaleOpenTensor is a plain
proof import. The latter remains in the unchanged inherited proof_deps. The
q-normalized and q-restricts clauses are retained because they express the
specified canonical open comparison and its identity on the open; no proof or
construction is obtained from `etaleOpenTensorComparisons`.

H11 repair made: replaced the previous generic audit paragraph by the explicit
hypothesis/clause correspondence above. No Lean signature or natural-language
statement changed. All four helper definitions have actual maps or a Prop formula;
the sole postponed theorem is `finiteFreeImageComparisons`. Rechecked r=0,
identity scalar extension, A→A×A, empty schemes/open, and identity-open
compactification; none requires an extra hypothesis. The node lean.statement
matches the theorem signature verbatim. The repaired module compiled cleanly via
scompile.py in both sandbox and library module modes (exit 0, no diagnostics).
