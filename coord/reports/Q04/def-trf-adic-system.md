## Worker report

Repair of the return on immutable head `5115eb5cdd49` (H2 and H13).
The accepted item module is retained byte for byte (SHA-256
`aa02c2997c38c86c1b0ee576e69eb23ce65ed4b04747c743f16391740a2943d9`).
This delivery contains only that module, the item node, and this report.

The item statement is unchanged. In particular its first paragraph and its recorded
restriction-of-scalars dependency explicitly specify the completed coefficient sheaf
and its projections. The notation `D(X_proet,O_E)` in this item therefore means the
completed-sheaf module category. The returned implementation's restriction to the
discrete constant sheaf R_X has been removed. `adicCompletedRes` restricts along pi_n.

Every hypothesis and clause has the following rendering (Lean index n corresponds to
the mathematical positive index n+1 throughout this module):

1. The global finite-field datum, including prime p, positive a, q=p^a and the chosen
   fields k₀ and k, is `T.datum : FiniteFieldDatum`. The coefficient prime and ell≠p
   are `T.coefficients`; `T.extension` is the finite coefficient extension inside its
   fixed algebraic closure. `T.coefficientField` is its recorded small model, transported
   through `Shrink.algEquiv`; no new coefficient field is chosen.
2. `T.X₀` is an object over Spec k₀, with the recorded locally finite type,
   quasi-compact and separated instances. These are precisely separated finite type.
   `T.geometricBaseChange` is `(T.datum.geometricFiber T.X₀).left`, over the actual
   chosen `T.datum.k`. Frobenius is `T.datum.geometricGaloisFrobenius T.X₀`.
3. `adicConventions T n` retains all of T except its level, which is replaced by
   n+1 with a proof of positivity. The coefficient ring is therefore exactly
   `Padic.coefficientExtensionRing ... (n+1)`, or O_E/(varpi^(n+1)). Lean index zero
   denotes A₁. This is an explicit reindexing in this module; the upstream AdicSystem
   instead uses R/I^n and has the zero ring at index zero. No claim that the upstream
   framework already implements the positive shift is made.
4. `adicLevel T n` is the recorded `proEtaleDerivedCategory` over the constant
   finite ring sheaf on the small pro-etale site. `TraceFormulaASystem.K n` belongs
   to `(adicConventions T n).boundedConstructibleFiniteTor.FullSubcategory`, so its
   boundedness, constructibility and finite Tor amplitude are the recorded predicates.
5. The finite ring sheaves and quotient maps are `integralCoefficientSheafSystem`
   and `normalizedDVRQuotient`. They are the actual constant sheaves of A_(n+1).
   `adicModuleRes` is `SheafOfModules.restrictScalars` along this quotient, and
   `adicRes` is its exact termwise derived descent. Exactness is the recorded
   `normalizedDVRModuleRes_exact`: underlying abelian sheaves, kernels and sheafified
   cokernels are unchanged. No flatness assumption is introduced.
6. `TraceFormulaASystem.t h` is K_m -> r_(m,n) K_n, source-coefficient-linear in
   the ambient derived category, for every h:n≤m. The adjacent transition is
   `t (Nat.le_succ n)`. `t_refl` uses the canonical `normalizedDVRResUnit` to say
   t_(n,n)=1. `t_comp` uses `normalizedDVRResComp` for the quotient cocycle.
   These equations force all composite transitions to be the specified composites
   of adjacent ones, so they add no independent non-adjacent choices.
7. `TraceFormulaASystem.IsNormalized` says that for every target P the map
   f |-> t h ≫ Res.map f is bijective. Under derived extension/restriction this
   is precisely precomposition with the map nu adjoint to the actual t h. Yoneda
   makes it equivalent to invertibility of that map, rather than existence of an
   unrelated tensor isomorphism. `adicDerivedChangeModel` directly invokes the
   recorded `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel` for the
   actual quotient, retaining its prescribed ordinary tensor and universal counit.
   `adjointTransition` gives the actual adjoint for any presentation of that
   derived adjunction. The identity and tensor-associative cocycle for nu follow
   by taking mates of `t_refl` and `t_comp`. Equal indices are included.
8. `TraceFormulaASystem.Hom.f` is a family of ambient arrows. `Hom.comm` is the
   transition square, for every composite (equivalently for every adjacent arrow).
   `Hom.id` and `Hom.comp` are levelwise identity and composition; their named
   well-definedness obligations have only `sorry` proofs and documented proofs.
9. `adicCompletedCategory` is the recorded `completedIntegralDerivedCategory`,
   whose ring sheaf is the inverse limit of these finite constant ring sheaves.
   `adicCompletedRes` is `normalizedDVRResCompleted`, exact termwise restriction
   along `completedIntegralCoefficientProjection`, the literal limit projection pi_n.
10. `restrictedObjects n` is Res_n K_n. `restrictedStep n` restricts the actual
    adjacent t and follows it by `normalizedDVRResCompletedComp`. That comparison
    is constructed from the limit equation pi_(n+1) ≫ quotient = pi_n.
11. `adicCompletedCountableProducts` states the countable-product clause in this
    exact category. Its proof docstring applies exact pro-etale countable products
    for the completed ring sheaf, followed by the recorded derived-product theorem.
12. `TraceFormulaASystem.IsIntegralRealization S L` is exactly
    `CategoryTheory.IsDerivedLimit S.restrictedStep L`. That recorded predicate
    existentially supplies p and delta making the displayed Roos triangle with
    1-s distinguished. It is a separate property of a supplied L, valid for any
    A-system, with no realization field, existence field or chosen limit functor.
13. `TraceFormulaAdicSystem.K n` is a recorded strict Weil complex at that level.
    Its carrier is bounded constructible finite Tor and its structure isomorphism
    is `strictWeilFrobenius`. The fields t, t_refl, t_comp and normalized impose
    exactly the preceding normalized A-system clauses; `toASystem` forgets phi.
14. `TraceFormulaAdicSystem.weil_comm` is the adjacent transition/Frobenius square.
    `adicRestrictionFrobenius` is the canonical coefficient identification, obtained
    by exact derived descent of the mate of the sectionwise identity direct-image
    comparison under `sfIntrinsicConstantModuleAdjunction`. The comparison is fixed
    on every section, not selected as an arbitrary nonempty natural isomorphism.
    The general `adicPushRestriction_existsUnique` states this identity comparison
    for a commuting ring square before substituting the large coefficient field
    constructions. `adicFrobeniusRingMap_square` is naturality of the actual
    constant-scalar unit in the finite quotient. These are helper statements for
    this node's coefficient identification, with source and complete proof docstrings.
15. `TraceFormulaAdicSystem.Hom.f n` is a morphism in the recorded strict-Weil
    category, hence includes exactly the required phi-compatibility square.
    `Hom.comm` adds transition compatibility on its forgotten ambient arrow
    `adicWeilMap`. `Hom.id`, `Hom.comp` and `traceFormulaAdicSystemCategory` give
    levelwise identities, composition and category laws. This is the requested
    D^b_ctf,W,adic, a category of systems of strict pairs rather than Ext groups.

No hFrob field, arbitrary endomorphism, ideal I, or redundant ideal-equality proof is
stored: all geometric and coefficient maps are the recorded constructions.

Dependency declarations used:

- `Sheaf.Paper.TraceFormulaCoefficientConventions`: `TraceFormulaCoefficientConventions`,
  `coefficientField`, `coefficientRing`, `geometricBaseChange`,
  `boundedConstructibleFiniteTor` and `derivedPullback`.
- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `geometricFiber`, `CoefficientDatum`;
  `Sheaf.AlgebraicGeometry.FrobeniusDetailed` and the recorded SchemeFrobenius module
  supply the Frobenius map on that chosen geometric fiber.
- Mathlib `Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`: `SheafOfModules.restrictScalars`;
  `Algebra.Homology.DerivedCategory.ExactFunctor`: `Functor.mapDerivedCategory` and
  its canonical identity/composition/natural-isomorphism comparisons.
- `Sheaf.Paper.CompletedIntegralCoefficients`: `integralCoefficientSheafSystem`,
  `integralCoefficientCommRingSheaf`, `completedIntegralCoefficientProjection` and
  `completedIntegralDerivedCategory`.
- `Sheaf.Paper.NormalizedDVRTower`: its shared actual quotient, restriction, unit,
  composition and completed restriction helpers. Its own NormalizedDVRTower structure
  is not used, since that structure additionally requires a coherent D(Towers) lift.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `sfIntrinsicConstantModuleAdjunction` and the recorded `proEtaleConstantModuleDirectImage`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `nonempty_derivedChangeOfRingsCochainModel`, ordinary tensor and universal counit;
  `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`:
  `CategoryTheory.Mod.derivedExtendRestrictAdjunction`, the recorded adjunction
  underlying the equivalent normalization test. The sheaf tensor/closedness and
  flat-resolution dependencies supply this adjunction's ambient setting.
- `Sheaf.Paper.TraceFormulaStrictWeilComplex`: `strictWeilComplex`, `strictWeilForget`,
  `strictWeilFrobeniusPullback` and `strictWeilFrobenius`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`: `IsDerivedLimit`;
  the recorded pro-etale exact-products and derived-limit-products-core statements
  supply the documented proof of product existence.

Edge cases checked: Lean index zero is positive exponent one, and the zero coefficient
exponent is excluded. Every positive exponent occurs. Equal indices use identity
restriction. Zero transitions between nonzero levels fail normalization. The zero
system and empty scheme are admitted. No smoothness, properness, connectedness or
nonemptiness is required. A complex without a Weil isomorphism may occur in an
A-system but not in the strict-Weil category. No integral model, coherent derived
tower lift or realization existence is assumed as extra object data.

Searches: LeanFinder for normalized inverse systems of bounded constructible finite-Tor
complexes with compatible Weil structures returned eight unrelated derived-category,
inverse-system and local-cohomology declarations. Loogle for
`AdicSystem, IsDerivedLimit, strictWeilComplex` returned no Mathlib hit (AdicSystem is
unknown there). Mathlib grep `AdicSystem|IsNormalizedTower|strictWeilComplex` returned
no hits. Upstream and project rg, plus the item-id search, were read in full at the
matching declarations. Upstream AdicSystem has ModuleCat-valued sheaf levels, a zero
coefficient level and constant integral target; it is not the recorded intrinsic
constant-ring-sheaf category and completed integral target. NormalizedDVRTower adds
a coherent D(Towers) lift and has no ctf/Weil condition. No existing exact definition
of this node was found; the shared restriction helpers are reused without duplicating
their definitions. No statement correction or disputed statement is needed.

## Return repair and self-check

H2: retain the live fourteen statement dependencies and add only
`def-coef-normalized-dvr-tower` and `def-weil-proetale-inverse-image`, as requested.
Remove `lem-coef-derived-system-evaluation-calculus`, `def-coef-ringed-sequence-site`,
`def-weil-constructible-heart`, `def-pur-integral-compact-support-coefficient-data`,
`def-weil-derived-pullback-tensor-hom`, and `def-weil-frobenius-detailed` from the
item's added dependencies. The evaluation-calculus theorem is not used by the item
and is not moved to proof dependencies. Transitive Frobenius declarations mentioned
above remain supplied by the published dependencies, without extra direct DAG edges.

H13: remove all seven dependency modules and dependency-node records from the packet:
FiniteFieldFiber, CoefficientRingedSequenceSite, CoefDerivedSystemEvaluationCalculus,
IntegralCompactSupportCoefficientData, SfConstructibleHeart,
DerivedPullbackTensorHom, and FrobeniusDetailed. Their former copies are archived only
under scratchpad, outside the delivery. No live dependency is overwritten, so their
current public imports and the October 19 DerivedPullbackTensorHom changes are retained.
There are no new nodes or dependency modules in this delivery.

The item node is based on the current shared node: only lean and the two authorized
stmt_deps additions differ. The mathematical statement, proof and proof dependencies
are unchanged. The fifteen-clause correspondence and edge cases above remain applicable
because the accepted module bytes are unchanged. This is the author's self-check;
the maintainer performs the independent review.

The required initial saved-packet dry run passed as commit `7fa3ab659b`, but its staged
list still contained the seven dependency replacements rejected by this return.
It was not pushed. Validation below checks the reduced delivery against the live library.

Validation: `scompile.py Q04 def-trf-adic-system` checked the sole delivered module
cleanly (sandbox 40.7 s; library 28.5 s). The reduced packet passed
`deliver2.py --no-push` as `0efd5920ad`; its staged list contained exactly the report,
item node and item module. The self-check verified the accepted module hash, the
verbatim signature, line lengths, and the exact sixteen dependencies.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
