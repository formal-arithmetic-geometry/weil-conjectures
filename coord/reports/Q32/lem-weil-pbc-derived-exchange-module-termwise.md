## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedExchangeModuleTermwise` states
`AlgebraicGeometry.Etale.derivedExchangeModuleTermwise`, with proof `sorry`.
Its three auxiliary definitions contain real data and only abbreviate the canonical
maps explicitly specified by this node: chi, t, and e. There are no new DAG nodes,
no dependency repairs, and no statement corrections. No STATEMENT-DISPUTED issue was found.
The theorem docstring carries all six proof steps with their dependencies.

Hypotheses and clauses, in the order of the node:

- The commutative ring is `(Λ : Type (u + 1)) [CommRing Λ]`, with the recorded
  six-functor size convention. The four schemes and four arrows are individually
  bound. `sq : ChosenCartesianSquare g' f' f g` supplies the chosen pullback
  identification, projection equations and commutativity; the mate uses `sq.toCommSq`.
- The module category is `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
  `DerivedCategoryModule Λ X` is precisely the recorded unbounded derived category.
  Localization is `DerivedCategory.Q`, with integer-indexed cochain complexes.
- The exact module inverse image and direct image are the existing `Etale.upperStar`
  and `Etale.lowerStar` with coefficient category `ModuleCat Λ`. Their sheaf adjunction
  is `upperStarLowerStarAdjunction`; its exact derived adjunction is
  `mapDerivedUpperStarLowerStarAdjunction`. The latter is exactly the adjunction used
  inside `exactDerivedBaseChangeMap`. The inverse-image comparison φ is
  `Functor.mapDerivedCategoryFactors`, in the direction `D(u⁻¹)(QP) ≅ Q(u⁻¹P)`.
- The sheaf square comparison θ⁰ is `squareUpperStarIso (ModuleCat Λ) sq.toCommSq`.
  `baseChangeMap` is its mate under these sheaf adjunctions. Thus it is exactly
  the node's underived transpose, with its stated counit normalization. The
  dependency's `exactDerivedSquareUpperStarIso` is the termwise descent of this
  same square comparison, not an arbitrary comparison.
- `K : DerivedCategoryModule Λ X`, `I`, `[I.IsKInjective]` and
  `s : K ≅ DerivedCategory.Q.obj I` encode the arbitrary representative.
  `J`, `[J.IsKInjective]`, the chain map `j : g'⁻¹I ⟶ J`, and `[QuasiIso j]`
  encode the arbitrary replacement. There is no boundedness binder and no
  K-injectivity hypothesis on `g'⁻¹I`.
- Naturality produces the complex map via `NatTrans.mapHomologicalComplex`.
  `moduleExchangeRepresentativeMap Λ sq I j` defines e as that termwise exchange
  followed by `(f'_*.mapHomologicalComplex (.up ℤ)).map j`. Its signature gives
  exactly `g⁻¹f_*I ⟶ f'_*J`.
- `moduleExchangeDirectImageIso Λ f I s` defines chi as the inverse of
  `rightDerivedFunctorObjQIso I` followed by `Rf_*.mapIso s.symm`. This is the
  canonical right-derived comparison Q(f_*I) ≅ Rf_*(QI) followed by Rf_*(s⁻¹).
  Reading `RightDerivedFunctor/KInjective.lean` verifies that this existing iso
  is the right-derived unit on the homotopy quotient, conjugated by
  `quotientCompQhIso`, rather than a freely chosen iso.
- `moduleExchangeReplacementIso Λ g' s j` defines t as
  `D(g'⁻¹).mapIso s ≪≫ φ.app I ≪≫ asIso (Q.map j)`. It is the specified t,
  with invertibility obtained from the existing localization of quasi-isomorphisms.
  The target chi is `moduleExchangeDirectImageIso Λ f' J t`.
- The left side of the theorem is `φ.inv.app (f_*I) ≫ D(g⁻¹).map chi.hom ≫ Ex.app K`,
  exactly σ_src followed by the fixed exchange. The right side is
  `Q.map e ≫ chi_target.hom`, exactly the other side of the displayed node equation.
  Lean's `≫` writes composition in the reverse order from the node's function notation.
- Both source factors are maps of isomorphisms or components of an isomorphism,
  and the target chi is explicitly an isomorphism. Cancelling them in this equation
  identifies every representative construction with the same `Ex.app K`; universal
  quantification over I, s, J and j gives choice independence. The bounded below
  injective case is a logical specialization using the last clause of
  `etale_kinjective_resolutions_exist`, not an added restriction or a separate map.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `AlgebraicGeometry.ChosenCartesianSquare`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` (read through `scompile.py --source`):
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, originally in
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact` (full theorem and
  docstring read through `scompile.py --source`): `AlgebraicGeometry.etaleInverseImageModulesExact`.
  The concrete six-functor module encoding is the one mandated by the derived-category
  record and already used by `def-kun-unbounded-exchange`.
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`:
  `AlgebraicGeometry.Etale.exactDerivedSquareUpperStarIso`, `exactDerivedBaseChangeMap`.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `CategoryTheory.mateEquiv`, used by
  the existing underived and derived mate definitions, not duplicated here.
- `Sheaf.AlgebraicGeometry.KInjectiveResolutions`: `CochainComplex.IsKInjectiveResolution`,
  whose two ingredients `CochainComplex.IsKInjective` and `QuasiIso` are used directly.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`:
  `CategoryTheory.exists_rightDerived_of_enough_isKInjective`, imported for the proof plan.
  The concrete canonical comparison is the existing
  `Functor.rightDerivedFunctorObjQIso` from
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`.

Every recorded proof-dependency module is imported, including
`ExactFunctorDerivedFunctor`, `KInjectiveResolutionsExist`,
`EtaleUnderivedExchangeModuleLinear`, `HomotopyCategory.Adjunction`,
`RightDerivedFunctor.Comp`, Mathlib's `DerivedCategory.KInjective` and
`Localization.Predicate`. No proof import is omitted for a cycle.

Sources read: current main-20261015 `sk-def-exchange/_section.md`, especially its final
paragraph; Stacks `sites-cohomology.tex` at `lemma-base-change-map-flat-case` (0736)
and `remark-base-change` (07A7). The node explicitly labels the unbounded representative
formula as agent-formulated support, rather than a verbatim Stacks theorem.

Edge cases checked: the zero ring and zero complex require no nontriviality;
empty schemes require no nonemptiness; identity squares still use the same canonical
mate; acyclic K is allowed; negative degrees and complexes unbounded in both directions
are allowed by index ℤ and the absence of any truncation hypothesis. There is no
restriction on characteristic, properness or torsion. The equations typecheck at
these levels of generality with all universes explicitly bound.

Searches made (machine-readable outputs are also in sandbox `searches.jsonl`):

- msearch.py leanfinder: “Derived exchange mate equals localized termwise base change
  followed by a K-injective replacement on arbitrary module complexes”. Eight hits,
  mainly `mapDerivedCategoryFactors`, `mapDerivedCategoryFactorsh`, `DerivedCategory.Q`;
  no complete exchange formula.
- msearch.py loogle: `CategoryTheory.Adjunction.derivedε_fac_app`. One hit. Read its
  full signature and surrounding hypotheses; it states individual derived-counit
  compatibility, not the four-edge exchange equation.
- msearch.py grep: `mateEquiv|baseChange|exchange` in `Algebra/Homology/DerivedCategory`.
  No hits.
- msearch.py leansearch: “The derived exchange mate is computed by the termwise
  exchange on any unbounded K-injective resolution of etale module sheaves”. Eight
  hits about individual injective-resolution computations, no full match.
- rg in Mathlib, upstream `WeilConjectures`, `dag/lean_names_upstream.json`, and side
  `lean/Sheaf` for the proposed names: no declaration collision.
- rg for the item id in upstream: no match. Concept searches in side `lean/Sheaf`
  found `DerivedExchangeTermwise`, `DerivedExchangeUnboundedTransport` and
  `DerivedExchangeBoundedComparison`; the signatures were opened. All concern a
  bounded below derived object with abelian coefficients, so none states this
  unbounded module result. Existing functors, square comparisons, mates, K-injectivity,
  and right-derived comparisons are reused instead of redefined.

Validation: prescribed `scompile.py Q32 lem-weil-pbc-derived-exchange-module-termwise`
compiled the complete delivered file in sandbox and library modes, cleanly (2.8 s
and 3.0 s respectively). No warning was emitted. Only the theorem has a postponed proof.

## Second reading by Q32

No independent worker second reading: this is the direct-delivery worker's self-check;
the maintainer supplies the independent mathematical review. Reopened the node and
complete file and checked the ordered clauses above against the actual expressions.
In particular checked the direction of φ, the inverse in the direct-image comparison,
the order in t, the mate's coefficient category, and the equation's common source and
target. Checked that no `let`, `show ... from`, private definition, file-local notation,
or auto-bound universe/variable occurs. The sole `sorry` belongs to the named DAG
statement. All three auxiliary definitions only compose existing maps and isomorphisms.
No mismatch or statement correction was found.
