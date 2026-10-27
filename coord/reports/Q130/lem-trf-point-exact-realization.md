## Worker report

The module `Sheaf.TraceFormula.PointExactRealization` states
`WeilConjectures.trfPointExactRealization`, with one postponed proof. Its four helper
constructions contain real data: powers in the existing point automorphism group,
ordinary canonical pullback in the recorded intrinsic realization, and the two
canonical `Functor.mapDerivedCategoryFactors` natural isomorphisms. No arbitrary
comparison or functor is assumed or selected. The node's statement is unchanged.

Hypotheses and objects:

- `D : FiniteFieldDatum.{u}` supplies precisely the prime p, positive exponent a,
  q=p^a, the field of q elements, and its fixed algebraic closure with its inclusion.
- `l : ℕ`, `[Fact l.Prime]`, and `hl : l ≠ D.p` supply the second distinct prime.
  `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]` are the recorded finite coefficient extension.
  As in all finite-level dependency interfaces, its embedding in the chosen algebraic
  closure is not used by these operations; every such embedded extension supplies
  this same coefficient extension and there is no separability or unramified condition.
- `n : ℕ` indexes the positive exponent n+1, so n=0 gives the required exponent 1.
  The ring is exactly `Padic.coefficientExtensionRing l E (n+1)`, using the dependency's
  valuation ring, uniformizer and quotient ideal, with no alternative coefficient ring.
- `r : ℕ` and `_hr : 1 ≤ r` give exactly the positive iterate range.
  `trfPointFrobeniusPower D r` is the power of `frobeniusPointIso D`, Spec of the
  recorded inverse q-power field automorphism, in `Aut (Spec (.of D.k))`.
- The site is `Scheme.ProEt.topology (Spec (.of D.k))`. The ring is the recorded
  `proEtaleConstantRing`; modules are `proEtaleRingModules`, definitionally the
  recorded `ringedSiteModules` / `SheafOfModules` over that constant ring. Its site
  object universe is u+1 and morphism universe u. Coefficients and module carriers
  use the standard u+1 lift. This changes size only, not scalar action or finiteness.
  `proEtaleDerivedCategory` uses the standard localization `DerivedCategory.Q`.

Clause-by-clause correspondence:

1. The first six conjuncts give additivity, finite-limit preservation and finite-colimit
   preservation for H_r and Gamma separately. H_r is `trfPointOrdinaryPullback`, a
   specialization of the published `sfIntrinsicPullback` with the canonical constant
   scalar action. This is the intrinsic realization of the ordinary module pullback,
   not a new pullback construction. Gamma is precisely `pointFiniteSections`, namely
   final-object `pointModuleSections` followed by restriction along
   `pointConstantSectionMap`. No identification of the section ring is assumed.
2. The next conjunct quantifies over arbitrary unbounded `CochainComplex ... ℤ`, and
   every morphism f with `QuasiIso f`, asserting quasi-isomorphism preservation by
   both `mapHomologicalComplex (.up ℤ)` functors. These are C(H_r) and C(Gamma).
3. `trfPointPullbackExactComparison` has the natural-isomorphism type
   `DerivedCategory.Q ⋙ Q_r ≅ C(H_r) ⋙ DerivedCategory.Q` verbatim, where Q_r is
   the specified `finiteDerivedPullback`. Its body is the canonical exact-functor
   factorization; finiteDerivedPullback unfolds to that functor, not an arbitrary
   isomorphic substitute. `trfPointEvaluationExactComparison` is the corresponding
   canonical factorization of ambient `pointFiniteSections.mapDerivedCategory`.
   The next two theorem conjuncts assert respectively the `IsLeftDerivedFunctor`
   property for e.hom and the `IsRightDerivedFunctor` property for v.inv. Thus these
   are total derived comparisons, in the required directions, on all complexes.
   On a K-flat resolution q:P→K, naturality of the specified e gives
   Q_r(L(q)) ≫ e_K = e_P ≫ L(C(H_r)(q)); the latter localized map is invertible
   by the quasi-isomorphism clause. This is exactly the stated K-flat normalization.
   The definitions make the same comparison on K-flat inputs; no flatness condition
   is imposed on K or on any complex binder.
4. The next conjunct quantifies over every ambient K satisfying
   `intrinsicFiniteTorsionConstructible`, and asserts the same predicate for Q_r K.
   This is precisely preservation of D^b_c(s,A).
5. The final conjunct is equality of functors, including their action on morphisms:
   `pointFiniteFibre ... ⋙ pointFiniteCohomology.ι` equals the restriction of the
   specified ambient derived evaluation. Its left functor already has codomain
   `(DerivedCategory.pointFiniteCohomology (ULift A)).FullSubcategory`, which is exactly
   bounded finite cohomology. This supplies the values in D^b_fin(A) as well as the
   identification with the existing V, without a replacement choice of fibre functor.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its imported
  `CoefficientExtension`: `Padic.finite_coefficientExtensionRing`,
  `Padic.coefficientExtensionRing`, and the actual integer-ring/uniformizer quotient.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: the recorded field Frobenius and
  `FiniteFieldDatum.geometricFrobenius`; the point is its Spec-of-field form already
  supplied by `Sheaf.SixFunctors.FrobeniusPointTransport`, `frobeniusPointIso`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointFiniteFibre`, `pointFibreFinite_exact`,
  `pointFibre_sections_mem`, and the exactness instances for ambient evaluation.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: `Scheme.proEtaleDerivedCategory`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleSheafInverseImage`,
  `proEtaleConstantInverseImageMap`, `proEtaleModuleInverseImage`, `proEtaleConstantRing`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, underlying the recorded tensor pullback.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `WeilConjectures.finiteDerivedPullback`;
  its defining interface `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`:
  `sfIntrinsicPullback`, `sfIntrinsicDerivedPullback`, and their exactness instances.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`:
  `finiteCoefficientInverseImageMap_isIso`, `finiteCoefficientInverseImageMap_constant`.
- `Sheaf.Paper.PointProEtaleSectionsExact`: `pointModuleSections`,
  `point_proEtale_sections_exact`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryFactors` and `Functor.mapDerivedCategory`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`: `Functor.exactFunctor_derivedFunctor`.
- `Sheaf.Paper.PointFiniteCohomologyComplexes`: `DerivedCategory.pointFiniteCohomology`.
- Proof imports also retain `ProEtaleConstantExact.finiteCoefficientModulePullback_tensor`,
  `IsomorphismDerivedPullback.isomorphismFiniteDerivedPullback_termwise`, and
  `PointSectionsFiniteness.point_sections_finiteness` through their respective modules.

Two already-landed definition nodes are added to stmt_deps to name the existing helper
interfaces actually used: `def-weil-frobenius-point-transport` for `frobeniusPointIso` and
`def-weil-pbc-proetale-operations` for `sfIntrinsicPullback`. Neither has a dependency path
back to this item. No new nodes and no dependency repairs are needed.

Edge cases checked before writing: exponent 1 (n=0), r=1, zero and acyclic complexes,
unbounded complexes, complexes that are not K-flat, arbitrary finite extensions including
ramified ones, and the original small-site universe convention. There is no condition on
termwise boundedness, termwise finite generation or flatness. The point Spec k is nonempty;
the ambient coefficient pullback interface itself handles the empty scheme without a
nonempty-source assumption. No STATEMENT-DISPUTED flag or source correction is needed.

Searches:

- `msearch.py ... leanfinder`: "Exact pullback of finite constant coefficient proetale
  sheaves on an algebraically closed point and exact evaluation compute their derived
  functors" returned 8 hits, including Profinite.NobelingProof.succ_exact,
  SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal and Condensed.hasExactLimitsOfShape;
  none states this specialized theorem.
- `msearch.py ... loogle`: `CategoryTheory.Functor.mapDerivedCategoryFactors` returned
  12 hits headed by that generic canonical factorization and its naturality/shift
  properties. Used this exact ingredient, not a duplicate construction.
- `msearch.py ... grep`: `proEtaleConstantModulePullback|pointFiniteSections|pointExactRealization`
  returned zero Mathlib hits.
- `rg` over both project Lean roots for `lem-trf-point-exact-realization`,
  `pointExactRealization`, `pointFiniteSections`, `finiteDerivedPullback`, and
  `pointFiniteFibre` found the recorded ingredient modules and sibling transport statements,
  but no existing declaration for this node. In particular no blueprint-tagged theorem
  for this item was found in WeilConjectures.

Sources inspected: local Stacks derived.tex, lemma-right-derived-exact-functor (Tag 015F),
proetale.tex lemmas at Tags 0982 and 098H, and main-20261015 blueprint
lem-trf-frobenius-operator-compact-description.proof.md, its transport paragraph.

Validation: scompile.py compiled both the isolated sandbox module and the correctly named
library module successfully, within the fixed 60-second limit. The only postponed proof is
this node's theorem; all data in the canonical comparisons are fully written.

## Second reading by Q130

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
