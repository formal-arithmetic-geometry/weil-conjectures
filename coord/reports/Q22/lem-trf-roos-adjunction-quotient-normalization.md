## Worker report

The module `Sheaf.Paper.RoosAdjunctionQuotientNormalization` states
`WeilConjectures.roosAdjunctionQuotientNormalization`. Its only new declaration is
this theorem, with proof `sorry`. It introduces no definitions or instances.
The natural-language statement and accepted stage-1 split are preserved.

The inherited BLOCKED ending concerned an attempt to split the accepted stage-1
item again. The 2026-10-22 stage-handoff rule in `coord/brief-stage2.md` explicitly
permits this stage-2 work. The current node has no Lean record; its queue entry
is stage 2, action `state`. No released repair note exists for this item.

### Hypotheses and objects

- The prime is `(l : ℕ) [Fact l.Prime]`. The arbitrary coefficient field is
  `(F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]`.
  The statement is uniform in F; instantiate it at E, L, or M in the node's fixed
  algebraic closure. None of the conclusions compares different fields or uses
  either embedding. Consequently no embedding, distinctness, or proper-extension
  hypothesis is introduced. Equality E=L=M is included.
- The scheme is `(W : Scheme.{t})`. The hypothesis
  `[∀ x : W, Invertible (l : W.residueField x)]` says precisely that l is
  invertible on W. There is no finiteness, separation, or nonemptiness condition.
- The recorded coefficient constructions in `scalarReductionSource l F W`
  give modules over `completedIntegralCoefficientSheafUnrestricted l F W`.
  This is the inverse limit of the constant positive quotient sheaves, with
  the chosen uniformizer and actual quotient maps from the dependency nodes.
  Lean index n means the paper's exponent n+1, so every positive level occurs.
- The pro-etale site is the recorded `Scheme.ProEt.topology W`. Its objects
  have universe t+1 and morphisms universe t; the coefficient/module universe
  is max u (t+1). The independent universes `t u` are explicit, and no equality
  of site-object, site-morphism, and field universes is assumed. The published
  small-model/sheaf APIs implement the node's size convention.
- `coefficientSequenceDerived l F W` is the ordinary unbounded derived category
  of the actual strict quotient-module systems, not a tower of unrelated
  derived objects. `CompletionUnit.tower` is exact scalar restriction applied
  to complexes. `coefficientConstantTowerLimit` is the total right derived
  inverse limit; `coefficientSequenceLimit` is its composite with exact system
  restriction. `S.reduction`, `S.adjunction`, and its unit and counit are the
  whole-system calculus from the recorded evaluation-calculus dependency.
- Existence of the simultaneous data is part of the conclusion: S, its
  coherence, M, D, H, κ, ρ, and adj are existential witnesses, not hypotheses
  assuming the desired normalization. The OrdinaryModel/DerivedModel structures
  are the published canonical comparison interfaces, with their tensor,
  transition, adjunction, and representative normalizations. No arbitrary map
  replaces reduction, realization, an augmentation, or a counit.

### Clauses of the conclusion

1. The single strict functor H(D)=Cone(1-s_D)[-1] is the existing `roosF`, whose
   definition uses products of complexes and the actual tower transitions.
   Its maps are product-induced cone maps on strict squares. The derived
   descent is the witness `H` with `κ : roosF ⋙ Q ≅ Q ⋙ H`.
   The witness `ρ : H ≅ coefficientConstantTowerLimit l F W` is natural on the
   entire derived tower category. The first equality identifies their composite
   with the one fixed `D.roos` used in every subsequent formula.
2. For every tower complex X and every quasi-isomorphism q:X→I, with I
   K-injective and every I.X p injective, the first quantified clause asserts
   `QuasiIso (roosι I)`. Its coordinate equation says the shifted coordinate is
   zero and the unshifted coordinate is the tuple of ordinary limit projections.
   The witness j is an isomorphism whose hom is exactly `Q.map (roosι I)`.
   The witness d is pinned by `d.hom ≫ RL.map (Q.map q) = D.limitUnit.app I`.
   Thus the following equality
   `D.roos.hom.app X = Q.map (roosF.map q) ≫ j.inv ≫ d.hom`
   is precisely the node's normalized comparison under Rlim X = lim I.
3. The next equation, for every n, identifies the canonical total-limit
   projection with the ordinary limit projection after q_n. It is written
   after composition with the invertible Q(q_n), avoiding an unspecified
   inverse or an extra assumption about evaluation. The separate all-X
   equation `D.roos.hom.app X ≫ projection_n ≫ evaluationFactors = Q(roosEval X n)`
   makes projection compatibility explicit even before choosing a resolution.
4. The full counit formula is an equality in the derived **tower** category.
   Its left side is `constDerived.map d.hom ≫ adj.counit.app (Q.obj X)`.
   On the right, `mapDerivedCategoryFactors` identifies derived constants with
   constants of a representative; `D.towerLimitComparison.inv.app I` converts
   the limit of complexes to the termwise limit complex; the ordinary
   `constLimAdj.mapHomologicalComplex` counit is the single strict cone of all
   limit projections. Finally `inv (Q.map q)` transports its target to X.
   This is ε_X=[q]⁻¹[Δ lim I→I], with its domain identified by d. It is asserted
   for every permitted q, not reconstructed from equality of evaluations.
5. For every actual coefficient system C and every n, the next clause takes
   the evaluated fixed counit `S.adjunction.counit.app C`, identifies the source
   by `S.reductionEvaluation n`, and applies the actual derived scalar-extension
   adjunction `coefficientFiniteAdjunction`. Its value is exactly
   `coefficientSequenceProjection l F W n` at C. That projection is defined
   in `CoefficientRingedSequenceSite` as the canonical constant-tower projection
   after derived restriction, followed by `coefficientRestrictedEvaluationIso`.
   Hence clauses 3 and 4 compute this component on every K-injective resolution
   as ordinary projection followed by q_n inverse. The system morphism is the
   one fixed counit of S; no independent levelwise lifts are selected.
6. The last clause quantifies over every complex P with
   `P.IsKFlatIndependentCoefficients` and every term flat on the site. The actual
   quotient tower is `(CompletionUnit.tower l F W).obj ((M.quotient l F W).obj P)`.
   `M.transition` records the actual quotient-linear transitions at all levels.
   The section equation identifies the ordinary augmentation with
   `unrestrictedIntegralTensorSection ... 1 z`, the recorded pure tensor z⊗1.
   `M.coneAugmentation` is an actual chain-map composite, not an existence
   assertion; the next equation pins its shifted-first coordinates to (0,tuple).
   Actual quotient transitions preserve these tensors, so (1-s) kills the tuple.
7. For **every** ambient derived object K and **every** isomorphism p:QP≅K,
   the final equality identifies `S.adjunction.unit.app K` with p inverse,
   the localized strict augmentation, and `D.completionComparison`, followed
   by realization of reduction(p). The latter comparison is the published
   composite of the very same `D.roos` with exact-restriction and K-flat
   comparison isomorphisms. This is the whole-morphism equality u_K=ρ[v_P][p]⁻¹
   including the necessary representative identifications.
8. Naturality is retained in the natural isomorphisms κ, ρ, and D.roos, and
   in the actual adjunctions and projection natural transformations. Every
   K-injective resolution satisfies the same equations with that fixed data;
   the normalization uniquely pins d since RL(Qq) is invertible. Every K-flat
   representative satisfies the same fixed unit equation. This gives the stated
   independence of all resolutions without assuming projections detect arbitrary
   derived tower maps. K and C are unbounded and have no completeness or
   constructibility condition.

### Dependency declarations read and used

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the underlying coefficient
  constructions publicly imported from `CoefficientExtension`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`.
  Scheme-morphism properties and the size convention are convention records;
  the relevant hypotheses and universes are explicit as described above.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `WeilConjectures.integralConstantToCompletionOfUniverses` and its existing
  unrestricted completed coefficient sheaf constructions.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`,
  `HasDerivedCategory`; `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, `CoefficientDerivedSystemCoherence`,
  `CoefficientDerivedSystemReduction.counit_projection`,
  `coefficientDerivedSystemEvaluationCalculus`; the inherited reduction,
  adjunction, finite evaluation and normalization fields were read in full.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`:
  `ModuleCat.nonempty_ordinaryDerivedChangeOfRings`, reexporting the ringed-site
  construction. The actual sheaf adjunction used in the statement is the
  published `coefficientFiniteAdjunction` from the coefficient-system interface.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`, reexported
  by the coefficient-system calculus, and its recorded independent-universe
  K-flat and flat-on-site predicates.
- `Sheaf.Paper.CompletionUnitModels`: all of `CompletionUnit.OrdinaryModel`,
  `DerivedModel`, `tower`, `quotient`, `augmentation`, `coneAugmentation`, and
  `completionComparison`. Its already-landed definition node
  `def-trf-completion-unit-models` is added to stmt_deps.
- `Sheaf.CategoryTheory.StrictRoosModel`: `roosF`, `roosχ`, `roosι`, `roosEval`.
  Its already-landed node `def-weil-strict-roos-model` is added to stmt_deps.
- Proof imports retain the accepted split: `CategoryTheory.strictRoosComparison`,
  `CategoryTheory.derived_tower_counit_projections`,
  `CompletionUnit.completionUnitStrictQuotientModel`,
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`,
  `AlgebraicGeometry.Scheme.ProEt.countableProducts_exact`, and
  `CochainComplex.IsKInjective.Qh_map_bijective`, in their recorded modules.
  No import cycle or unstated prerequisite was found.

### Source and edge checks

Read Stacks `sites-cohomology.tex`, lemma-derived-limit-is-ok (0941): the proof
uses an injective-term K-injective tower, its ordinary termwise limit, and the
short exact product sequence. Read the current trace-transport proof in
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-thm-trace-transport/`;
this node is the preserved integral comparison refinement identified by its
accepted split, not the unit's own statement or a change of proof route.

Checked the zero tower, zero representative, empty W, positive exponent one,
equal coefficient fields, non-complete/unbounded inputs, and independent t/u.
The zero maps have zero shifted coordinate; the empty scheme is allowed because
invertibility is pointwise; index zero is exponent one, never a zero exponent.
No argument requires a nonzero object, a bound, or a distinct extension.
Composition order in the full counit is first the strict ordinary cone, then
inverse q; normalization and evaluations use the same d and D throughout.
No disputed statement or source-based statement correction was needed.

### Searches

The LeanFinder, Loogle and Mathlib grep searches preceded the theorem draft.
LeanSearch and final declaration-name collision checks supplemented them during
verification; no exact existing statement or declaration-name collision was found.

- `msearch.py ... leanfinder`: "Natural Roos comparison with derived inverse
  limit normalized on K-injective towers and the unit and counit of derived
  quotient reduction". Eight generic exact-functor/derived-functor hits,
  including `Functor.mapDerivedCategoryFactorsh_hom_app`; no combined statement.
- `msearch.py ... loogle`: "CategoryTheory.Adjunction.derived,
  CochainComplex.mappingCone, CategoryTheory.roosF". Zero hits; roosF is a
  project declaration, not a Mathlib identifier. Its project definition was
  located and reused directly.
- `msearch.py ... leansearch`: "Roos derived inverse limit quotient system unit
  counit normalized comparison". Eight generic monadicity/comonadicity and
  inverse-system hits; no combined strict quotient normalization.
- `msearch.py ... grep`: "Roos|roos|constLimAdj" in Mathlib `Algebra/Homology`:
  zero hits. Mathlib supplies the cone, exact-derived-functor and adjunction
  machinery; the project supplies the normalized Roos and coefficient models.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, by the concepts Roos,
  completion unit, coefficientConstantTowerLimit/Projection, and by this node's
  id: found the recorded strict Roos comparison, ordinary/derived completion
  models, completion-unit theorem, and canonical coefficient tower projection.
  The additional `CoefficientConstantTowerRoosComparison` was read: it supplies
  only projection compatibility, not this simultaneous counit/unit statement.
  None states this combined result. Searches for the new full declaration name
  were empty in both library roots and Mathlib.

### Validation

`scompile.py Q22 lem-trf-roos-adjunction-quotient-normalization` compiled the
single delivered module cleanly on the server, in sandbox and library mode
(6.8 s and 7.5 s respectively). No errors or warnings. The statement explicitly
binds every variable and universe; `autoImplicit` is false. The only postponed
proof is the named theorem matching this node and its full proof-plan docstring.

The required `deliver2.py ... --no-push` dry run passed preflight and compilation
with commit a615f4c50ce; nothing was pushed by that dry run.

## Second reading by Q22

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
