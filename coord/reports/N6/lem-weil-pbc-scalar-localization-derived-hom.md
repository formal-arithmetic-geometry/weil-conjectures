## Worker report

This delivery states `CategoryTheory.scalarLocalization_derivedHom` in
`Sheaf.CategoryTheory.ScalarLocalizationDerivedHom`, with every postponed theorem proved
by `sorry`. All definitions have actual data. It retains the item's statement and proof
plan. The main theorem applies `scalarLocalizationHomComparison`, a fully written
Prop-valued definition containing the fraction formula and separate equations for
naturality, identities, composition and simultaneous shifts. Its two predicate
arguments are the actual continuity and bounded-below conditions, and its functor
is the actual `E.mapDerivedCategory`; the abstraction keeps Lean from repeating
large derived-category instance searches for every equation.

The previous worker's reported unchanged-item refusal concerned a stage-1 delivery by
NO. The preserved sandbox had only dispatcher markers, and the node had no Lean record.
This packet supplies a new stage-2 record, rather than resubmitting the stage-1 split.

Clause-by-clause rendering:

- A small ringed site is `{C : Type u} [SmallCategory C]` with
  `J : GrothendieckTopology C` and `R : Sheaf J CommRingCat.{u}`. The site is arbitrary;
  no scheme, constructibility, subcanonicity or cohomological-dimension condition occurs.
  `A : Type v` has its own universe and `[CommRing A]`; `t : A` is arbitrary.
- The commutative A-algebra sheaf structure is the ring homomorphism
  `a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)`.
  Equivalently, each object has a ring homomorphism from A, natural under restriction.
  This specifies the coefficient action; it is not a free choice of a linear structure.
- `R_t` is `ringedLocalizationRing R (a t)`, built from the existing actual localizations
  and restriction lifts. `ringedLocalizationRingUnit` is the sheafified algebra map.
  The dependency repair identifies the underlying module with the recorded
  `ringedSectionLocalization` by an isomorphism normalized on every local fraction.
- Module categories are the recorded `ringedSiteModules`, hence exactly Mathlib's
  `SheafOfModules`. Derived categories are `DerivedCategory` with explicitly bound
  `HasDerivedCategory.{w}` instances, using the same chosen Hom universe for both.
- `E`, `hE` and `hmap` present the actual scalar-extension functor: both its objects and
  its maps are fixed by `SheafOfModules.changeOfRings` and `changeOfRingsHom` along
  `ringedLocalizationRingUnit`. There is no arbitrary functor or unspecified map in
  place of scalar extension. Such a presentation is supplied by the recorded
  `derivedChangeOfRingsIndependentCoefficients` theorem. `scalarLocalization_exact`
  states additivity and both finite-preservation instances from these equations;
  consequently the main theorem's exactness instances add no mathematical hypothesis.
  `E.mapDerivedCategory` is the actual termwise exact derived functor F, with Mathlib's
  canonical shift structure and quotient factorization.
- `DerivedCategory.CountableBoundedBelowHomContinuous K` is exactly the item's
  countable-family hypothesis. It quantifies every family indexed by ℕ, every common
  lower bound `b`, every coproduct cofan and every integer `q`. The comparison is
  `DirectSum.toAddMonoid` of postcomposition with the shifted coproduct legs.
  The cofan form does not choose a coproduct or require any extra coproduct instance;
  in this Grothendieck module-sheaf derived category coproducts exist. It tests all
  coproducts and is equivalent to the displayed canonical comparison in the node.
  K itself is not required to be bounded below.
- `∃ b : ℤ, L.IsGE b` is the bounded-below condition on L. Every integer q is retained.
  A family `e K hK L hL q` of `≃ₗ[Localization.Away t]` supplies the asserted isomorphisms.
- `scalarLocalizationHomEquiv A t (K ⟶ L⟦q⟧) ...` is an abbreviation for a linear
  equivalence from the exact existing `LocalizedModule.Away`, using
  `LocalizedModule.moduleOfIsLocalization`. It introduces no new localization relation:
  its source is Mathlib's actual fraction quotient, with precisely the powers-of-t
  equality criterion of the dependency.
- `scalarLocalizationCoefficientLinear` restricts the existing global-section action
  on sheaf Homs. For the target its ring homomorphism is the localization lift
  `scalarLocalizationCoefficientMap`; its definition uses the named theorem that
  the image of t is a unit. `scalarLocalizationDerivedLinear` carries these actions to the ordinary derived categories.
  The two instance lambdas in the statement are immediately
  applied to these concrete structures. They are not quantified extra assumptions,
  and the statement has no unspecified scalar action.
- The first conjunct specifies every fraction:
  `(e ...).toFun (LocalizedModule.mk f ⟨t^n, ⟨n,rfl⟩⟩)` equals
  `IsLocalization.Away.invSelf t ^ n • (F.map f ≫ (F.commShiftIso q).hom.app L)`.
  The final isomorphism changes `F(L[q])` to `(FL)[q]`; this is exactly
  `u/t^n ↦ t^(-n) F(u)` with the specified shifts.
- The second conjunct is simultaneous contravariant/covariant naturality in K,L,
  for arbitrary input maps, arbitrary numerators and every denominator t^n.
  These fractions exhaust the quotient, so this is naturality on the entire module.
- The third conjunct preserves identities, with the shift-zero isomorphisms written
  explicitly. It is asserted whenever the object satisfies both displayed conditions.
- The fourth conjunct preserves arbitrary shifted compositions; denominators multiply
  to t^(n+m) and `shiftFunctorAdd` identifies the double shift with the sum shift.
- The fifth conjunct commutes with simultaneous shifts of source and target, using
  `shiftFunctorComm` and the actual F shift comparison. The continuity and lower-bound
  certificates are supplied exactly for the shifted objects involved.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings` and its retained Mathlib site conventions.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; `TStructure` supplies `DerivedCategory.IsGE`.
- `Sheaf.CategoryTheory.RingedSectionLocalization`:
  `ringedSectionLocalizationCarrier`, `ringedSectionLocalizationMap`,
  `ringedSectionLocalizationPresheaf`, `ringedSectionLocalization` and its unit.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule.Away`,
  `LocalizedModule.mk`, `LocalizedModule.moduleOfIsLocalization` and the fraction relation.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`, publicly retaining
  `TensorProductOfUniverses` and `TensorProduct`: `changeOfRings`, `changeOfRingsHom`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`:
  `CategoryTheory.Functor.exactFunctor_derivedFunctor`, read with its full ordinary and
  bounded-below Kan-extension clauses. F is Mathlib's `Functor.mapDerivedCategory`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule`:
  `SheafOfModules.homModule`, `SheafOfModules.homLinear`. I read the current published
  module with `scompile.py --source`; the local Sheaf-path module is retired.
- The stated proof interfaces are imported, including
  `sequence_relative_hom_telescope`, `derivedChangeOfRingsIndependentCoefficients`,
  `sheafRingDerivedCoefficientAdjunction`, `tensorClosed`,
  `exists_sheafificationTensorIso`, `IsLocalization.flat` and the exact module
  sheafification API. The underlying-localization telescope node has no Lean record,
  so its future proof import is absent; it is not a missing statement prerequisite.

Edge cases checked against the source before writing: K=0, L=0, the zero ring, t=0,
t a unit, t nilpotent, q=0 and negative q, the empty site, zero coproduct summands,
and negative/common lower bounds. When t is nilpotent localization and its Hom groups
are zero; the continuity hypothesis supplies the telescope argument even if K is not
bounded below. For a unit t this is the ordinary Hom equivalence. All formulas include
these cases. No disputed statement or source-based statement correction is needed.

Searches: `msearch.py leanfinder` for scalar localization of derived Hom returned only
small shifted-Hom and derived-linearity infrastructure; `loogle` for
`IsLocalizedModule, LocalizedModule.Away` returned ordinary-module localization results;
Mathlib `grep` for localization/Hom returned categorical localization infrastructure.
`rg` of both project trees for the item id and scalar-localization/derived-Hom terms
found no declaration of this statement. The nearby `ringedLocalizationRHom_calculus`
concerns slice restriction and internal-Hom currying, not scalar-extended global Hom.
For the continuity notion I ran LeanSearch, LeanFinder and Mathlib grep, project/DAG
search and `blueprint_refs.py search`; exact tool outputs are recorded in the new node.
`CategoryTheory.IsCompactObject` requires arbitrary families, so it is a different,
stronger predicate. Section-localization searches found only the existing module
construction and slice-module presentation, which do not give a ring sheaf.

## New nodes

`def-weil-pbc-countable-bounded-below-hom-continuity`, in
`Sheaf.CategoryTheory.BoundedBelowCountableHomContinuity`, defines exactly the source
condition of the item as a real Prop-valued definition. It follows Bhatt–Scholze
Lemma 6.8.12 as used in Proposition 6.8.14(2), with the abstract countable-family
hypothesis explicitly extracted. It depends on the existing ordinary derived-category
node and is cited by the item. Searches found no matching node or declaration; full
compactness, CountableAB4 and size-of-shifted-Hom are different notions.

## Dependency modules

`def-weil-pbc-ringed-section-localization` is repaired only in `lean`.
`Sheaf.CategoryTheory.RingedSectionLocalizationRing` publicly retains its old module,
uses its actual carriers and localization restriction lifts, and supplies their
commutative-ring presheaf, ring sheafification, canonical ring map and the normalized
comparison with the old module sheafification. The old primary declaration returned
only an R-module, so it could not type the coefficient ring of D(R_t). The repair
supplies that ring structure without replacing the recorded module construction.

Validation: `scompile.py` compiled each of the three delivered modules separately,
in dependency order and at its final module path, with no errors or unexpected
warnings. All three use `set_option autoImplicit false`; every universe is bound
explicitly. The longest Lean source line is below the 100-column limit.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
