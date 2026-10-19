## Worker report

Q11 states `lem-trf-finite-cover-tube-comparison` in
`Sheaf.TraceFormula.FiniteCoverTubeComparison`. The namespace is
`AlgebraicGeometry.OrientedNearbyCycles.FiniteCoverTubeComparison` (abbreviated below).
This is stage 2: every theorem has only `sorry`; all definition data are explicit.
No node statement was corrected, no new node or dependency replacement was needed.

The source read is Orgogozo, *Modifications et cycles proches sur une base générale*,
Lemma 2.6 and Lemma 2.6.1, printed pp. 4–5, in the author PDF linked by the node:
https://www.cmls.polytechnique.fr/perso/orgogozo/articles/Modifications%20et%20cycles%20proches%20sur%20une%20base%20g%C3%A9n%C3%A9rale.pdf .
The source reduces to strict-local bases, uses the finite geometric-fibre components,
and identifies the restrictions with the nearby comparison. The node spells out
its derived and finite-local-factor interpretation; the module follows those clauses.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| Finite-type `f : X → S` | `[LocallyOfFiniteType f] [QuasiCompact f]` in `ordinaryComparison` and `coverRestriction_ordinaryComparisons`. This is the recorded Mathlib finite-type interface. |
| Arbitrary `g : U → S`, Cartesian `X_U` | `g : S' ⟶ S`, `h : X' ⟶ X`, `f' : X' ⟶ S'`, `w : h ≫ f = f' ≫ g`, and `IsPullback h f' f g`. This permits any Cartesian realization of the specified fibre product. No property of `g` is imposed. |
| Finite commutative coefficients with invertible exponent | `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasInvertibleExponent Λ S]`. The last class is the recorded positive annihilating integer, invertible on S. |
| The recorded constant-module category and bounded constructibility | `K : EtaleDerived.{u,u+1} X Λ`; `IsBounded (etaleDatum X) (Coeff Λ) K`; for every integer n, `Scheme.IsConstructibleEtaleModuleSheaf` of `Hypercover.readModules X Λ` applied to `DerivedCategory.homologyFunctor` of K. `readModules` is the existing constant-ring-module equivalence, not a new category. |
| The two geometric points, fields, and chosen specializations | `Point f Ω Ξ` has `x`, `b`, `c` and the over-S equation. Both fields are explicit, arbitrary algebraically closed fields in the scheme universe. `Change` has `x_over`, `b_over` and the specialization commutative square; thus it expresses the stipulated image point with the original fields. |
| The two displayed tubes, with their original coefficient maps | `tube z`, `tube z'`, `toSource`, `toBase` are literal strict-local pullbacks and projections; `tubeSections` is the derived section functor on the coefficient pullback along `toSource`. |
| The natural map N → M | `Change.sourceMap`, `genericMap`, `tube_condition`, and the explicit `pullback.lift` in `Change.tubeMap`. `tubeMap_over` identifies its structural map to X. |
| Actual stalks and the normalized point-cohomology isomorphisms | `pointModules` is the published sigma section composed with the geometric point `basePoint z`. `stalk` computes the same geometric stalk by restriction along c followed by sections on the strictly local scheme S_(b). Such sections are the closed-point stalk. `pointCohomology` is an explicit composite of the published counit-normalized strict-local description, ordinary direct-image base change, the adjoint-conjugate Leray isomorphism, and the normalized coefficient-composition isomorphism. Its normalization is the restriction normalization of `orientedPointCohomology`, as detailed in its docstring and `pointCohomology_isIso`. `pointCohomology_pullback_isIso` supplies the same isomorphism for each pulled-back coefficient complex, in particular K_U and K on X_P. |
| The stalk of the ordinary comparison equals restriction RΓ(M,K) → RΓ(N,K_U) | `ordinaryComparison` is the commuting square with the actual `baseChange f f' h g w Λ K` on its left path, and the explicit `tubeRestriction d Λ K` on its right path. `Change.stalkRestriction` is the image-point stalk identification; `stalkRestriction_isIso` states its invertibility for every complex. `restriction` is the adjoint transpose of pullback of the global-section counit; it is not an arbitrary map. |
| Finite surjective P → S_0 and all Cech stages | For a map `p` to `strictHenselizationScheme (z.x ≫ f)`, `cechMap z p q` is exactly the augmentation map of `(Arrow.mk p).augmentedCechNerve` at `[q]`, whose source is the wide fibre product of q+1 copies of P. `cechMap_finite_surjective` retains both finiteness and surjectivity at every q, including zero. |
| Q_q, A_q, B_q, their actual restrictions and augmentations | Instantiate `changedCoverMap d p`, `coverSections z p Λ K`, and `coverSections z' (changedCoverMap d p) Λ (h* K)` with `p := cechMap z originalCover q`. `coverRestriction` is A_q → B_q. `coverCoface` is restriction along every cover map over S_0; each simplex map of the Cech nerve supplies such a map by naturality of its augmentation. `coverAugmentation` restricts from the original tube along its covered-tube projection. |
| I_q and J_q as finite geometric-fibre component sets | `Index z p` is the set of geometric lifts with exactly the field Ξ of b; `componentIndex` sends that lift to its actual connected component in the geometric fibre. `finiteTubeDecomposition` asserts both `Finite (Index z p)` and bijectivity of this map, so this is the specified canonical indexing by π₀, including nonreduced fibres. The same statement applies with z' and Q_q. |
| The lift of b and the closed points a and a_U | `basePoint z = strictLocalPoint z.b ≫ z.c`; the closed base point is `strictLocalPoint (z.x ≫ f)`. The same definitions apply to z'. |
| The finite strictly local factor, its closed lift with the field Ω of x, and the resulting specialized point | `LiftedPoint z p t` has a point of `coverMorphism z p = X_P → P`, its generic point is literally `t.val`, its closed point lies over the specified closed base point, and its `Change` gives x-over-X and the specialization square. Its `factor_open` and `factor_closed` say that the canonical strict localization at its closed point is the open-and-closed factor H containing the generic lift. The field of its closed lift is exactly Ω; it is not chosen independently. Because the structural map of this factor is an open immersion, `Point.over` uniquely forces its c to be the factored structural map required in the node. Different t are allowed to share that factor. |
| The specified lifted tubes M_qi and N_qj | They are exactly `tube (l t).point` and `tube (l' t).point`. `LiftedPoint.inclusion` is the canonical map to the covered tube, defined by its projections, not by selecting an isomorphism. |
| The canonical finite disjoint-union identifications | `finiteTubeDecomposition` supplies the lifted points and `IsColimit (Cofan.mk (coverTube z p) (fun t ↦ (l t).inclusion))`. This states the coproduct through the actual inclusions and therefore its canonical identification. Its proof plan spells out the strict-local invariance, finite-base decomposition, closed-factor calculation and fibre-product reassociation. Apply it to both p and its pullback. |
| The finite-product decompositions of derived sections | `finiteSectionDecomposition` says that the fan with vertex `coverSections z p Λ K` and legs `(l t).sectionRestriction Λ K` is a limit. These are exactly the actual restrictions to the lifted tubes, with the coefficient-composition isomorphisms specified. Finiteness is supplied by the preceding theorem. |
| Projection J_q → I_q and the Cartesian squares Q_q → P_q | `componentProjection` sends the actual geometric lift through the Q → P projection. `coverSchemeMap` is X_Q → X_P and `coverSchemeMap_isPullback` states the required Cartesian square. `liftedPoints_compatible` supplies the `Change` for every corresponding pair of lifted specializations; no compatibility is assumed without its existence statement. |
| Whenever projection is bijective, A_q → B_q is the product of ordinary-comparison stalks | `coverRestriction_ordinaryComparisons` retains precisely `Function.Bijective (componentProjection d p)`. For every product coordinate t its equation identifies the projection of `coverRestriction` with `ordinaryTubeMap D Λ K_P` followed by the canonical coefficient identification. `ordinaryTubeMap` explicitly contains `baseChange` for Q → P and the image-point stalk identification. Only the point-cohomology isomorphism is inverted; beta is never assumed invertible. Together with both `finiteSectionDecomposition` limit cones this is the stated product equality. `coverRestriction_component` also gives the restriction version before that identification. |
| Compatibility with cofaces; no base-change invertibility or truncated descent | `coverRestriction_coface` is the naturality square for every cover map a, hence every Cech coface and degeneracy, and `coverRestriction_augmentation` is the augmentation square. `restrictionOver_comp` supplies composition compatibility. These equations concern the actual arrows. There is no `IsPsiGood`, no `IsIso baseChange`, no cohomological truncation and no descent hypothesis. |

The decomposition statements are given for every finite p, without needing its
surjectivity; applying them to the explicitly finite-surjective Cech stages gives
exactly the node's conclusions. Likewise the restriction identities are naturally
stated for every cover map, which includes all the required cofaces. These auxiliary
generalisations do not exclude any case or alter the node's hypotheses.

### Dependency declarations used

- `Sheaf.Paper.OrientedNearbyCycles`: `etaleDatum`, `vanishingDatum`, `Coeff`,
  `EtaleDerived`, `VanishingDerived`, `IsBounded`, `etaleModules`, `squareModules`,
  `nearbyCycles`, `baseChange`; its fixed AdicSites module-pull/push adjunctions.
- `Sheaf.TraceFormula.OrientedPointCohomology`:
  `CategoryTheory.OrientedPointCohomology.orientedPointCohomology`, with the full
  `sourceUnit`/`targetUnit` restriction normalization, used by the point-cohomology
  proof plan. This interface is bounded below; a bounded K and its exact pullbacks
  are covered by it. No replacement or private copy is made.
- Mathlib: `LocallyOfFiniteType`, `QuasiCompact`, `IsFinite`, `Surjective`,
  `pullback`, its projections, lift and map; `Arrow.augmentedCechNerve` and its
  augmentation; `Cofan`, `IsColimit`, `Fan`, `IsLimit`, `ConnectedComponents`.
- `Sheaf.AlgebraicGeometry.StrictHenselization` and
  `Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift`:
  `Scheme.strictHenselizationScheme`, `strictHenselizationStructuralMap`,
  `strictHenselizationPointEvaluation`, `strictHenselizationMap`,
  `strictHenselizationMap_over`. Geometric points use the dependency's literal
  algebraically closed field and `Spec` map convention.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `Scheme.IsConstructibleEtaleModuleSheaf`.
- `WeilConjectures.AlgebraicGeometry.InvertibleExponent`: `HasInvertibleExponent`.
- `Sheaf.TraceFormula.FiniteBaseStrictLocalization`:
  `Scheme.finite_strictLocalization_decomposition` and
  `Scheme.finite_strictLocalization_isPullback`, used with their actual projection
  equations in the finite-tube proof plan.
- Proof-plan imports `Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance`,
  `Sheaf.AlgebraicGeometry.StrictBaseClosedPointLocalizations`, and
  `Sheaf.AlgebraicGeometry.FiniteBaseCechComponents` retain the corresponding
  already stated proof dependencies. The finite-radicial proof dependency has
  no recorded Lean module; no invented import is used.
- Existing landed `Sheaf.Paper.OrientedNearbyStrictLocalDescription`:
  `localSections`, `localEpsilon`, `localDirectSections`, `strictLocalPoint`,
  `strictLocalSigma`, `strictLocalSigmaModules`, `strictLocalIdentityPull`,
  `strictLocalDescriptionComparison`, `strictLocalDirectBaseChange`,
  `strictLocalSquareBase`, `strictLocalSigmaPullSquare` and the ordinary-comparison
  counit-mate statement. This node is added to stmt_deps because the actual maps
  reuse these canonical constructions.
- Existing landed `Sheaf.Paper.OrientedHypercoverDescentDatum`:
  `Hypercover.readModules` and `Hypercover.pullComposition`. Its node is added to
  stmt_deps for the existing scalar-normalized coefficient interface; its descent
  structure and any descent theorem are not used.
- Existing landed `Sheaf.Paper.OrientedProductPointsConservative`:
  `punctualSite`, `punctualEquivalence`, `geometricEtalePoint`. Its node is added to
  stmt_deps for those presentations; the conservativity theorem is not assumed.
  The three added nodes already carry Lean records. Their dependency closures were
  searched and none reaches this item, so these additions introduce no cycle.

### Edge cases and typing checks

- Empty geometric fibres: `Index` may be empty, the cofan is the empty coproduct
  and the fan is the empty product. No `Nonempty Index` or nonzero-ring hypothesis
  is imposed. The component bijection and compatibility then have their usual
  empty meanings.
- Nonreduced finite fibres have one geometric lift per connected component;
  the construction indexes by those lifts, not by points of the total finite
  scheme. A factor may contain more than one generic-fibre component.
- The closed residue field need only be separably closed, not the entire chosen
  geometric field. The closed lift with field Ω is retained in `LiftedPoint`;
  no equality of residue field with Ω or Ξ is imposed.
- Identity base change and identity covers are permitted. All comparison arrows
  retain their adjunction units/counits and canonical composition identifications.
- q = 0 is the one-factor stage; the arbitrary-q statement includes every higher
  stage and every degeneracy, with no truncation convention to choose.
- g may be non-finite-type and non-quasicompact. Only f is finite type. No
  isomorphism assumption is made on the ordinary base-change comparison.
- Zero coefficients/zero K cause no exceptional binder or excluded case.
- Scheme universe u and coefficient universe u+1 are explicit, as in the landed
  constructibility/readModules interface. `Coeff` supplies the established ULift
  transport, and the output stays in derived constant modules on `punctualSite`.
  No map is replaced by an additive-group map or an arbitrary chosen isomorphism.
- All variables and universes are explicitly bound and `autoImplicit` is false.

No `STATEMENT-DISPUTED` issue or source-statement correction was found.

### Searches and verification

Before defining maps, the prescribed searches were run using msearch.py with Q11
and this item. `searches.jsonl` contains the actual tool records:

- LeanFinder: “stalk of ordinary nearby cycles base change comparison is restriction
  on Milnor tubes and finite cover decompositions”: 8 hits, including
  `Scheme.Modules.restrictStalkNatIso`, presheafed-space restrict-stalk isomorphisms
  and `TopCat.Presheaf` stalk-pullback maps; none is the oriented nearby-cycle theorem.
- Loogle: `nearbyCycles, pullback`: 0 hits; unknown Mathlib identifier `nearbyCycles`.
- Mathlib grep: `Milnor|nearbyCycles|tube` under `AlgebraicGeometry`: 0 hits.
- `rg` in upstream `WeilConjectures` and side `lean/Sheaf` for the item id and
  tube/nearby/strict-local/component terminology: found the already landed nearby
  definitions, strict-local description, oriented-point cohomology and finite-base
  helpers described above. The exact item id occurs only in explanatory comments
  of `NearbyFiniteBaseDescent` and `OrientedClosedBaseExtension`; neither states it.
- A final exact namespace/item-id search covered Mathlib, upstream
  `WeilConjectures`, side `lean/Sheaf`, and `dag/lean_names_upstream.json`.
  There is no prior `FiniteCoverTubeComparison` declaration. The only item-id
  hits remain those two explanatory comments.

The whole module compiles through the required scompile.py wrapper, both in its
private sandbox check and as the deliverable library module. Expected theorem
`sorry`s are the only postponed content. The delivery preflight and its fresh
per-file compile are run after this report and the node record are written.

## Repair of returned delivery

The retained delivery was returned for a packaging-path failure while applying
the independent stage-2 review fixes: the review tool received a full
`coord/reports/Q11/...` path where its repair protocol accepts the item report
basename. The Lean module, node statement, and declarations therefore remain
unchanged. This repair keeps the report at the required sandbox `report.md`
path, records the packaging diagnosis here, and reruns the prescribed
`scompile.py` and `deliver2.py --no-push` checks before delivery.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
