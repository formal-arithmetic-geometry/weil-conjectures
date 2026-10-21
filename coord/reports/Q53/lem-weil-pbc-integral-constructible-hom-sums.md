## Worker report

The module `Sheaf.Paper.IntegralConstructibleHomSums` states
`AlgebraicGeometry.Scheme.integralConstructible_hom_sums`, with its sole proof `sorry`.
No definitions, dependency repairs, statement corrections, or new nodes are needed.
The natural-language statement and all dependencies remain unchanged.

Clause-by-clause correspondence:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The finite extension is `(E : Type u)
  [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]`.
  The integer ring and chosen uniformizer are the published `PbcIntegralRing ℓ E`
  and `pbcUniformizer ℓ E`, used by `pbcIntegralDatum ℓ E`. This is the canonical
  ULift of `Padic.coefficientExtensionIntegers ℓ E`; the ULift ring equivalence
  identifies its modules and scalar action with A-modules. It changes no coefficients.
- The scheme is `(X : Scheme.{u}) [IsNoetherian X]`. Mathlib's noetherian condition
  is locally noetherian plus quasi-compact, equivalently the stated finite affine
  noetherian cover. `hdim : ∃ N : ℕ, topologicalKrullDim X ≤ (N : WithBot ℕ∞)`
  bounds the lengths of irreducible-closed chains. `hℓ : ∀ x : X,
  IsUnit (ℓ : X.presheaf.stalk x)` says ℓ is invertible in every local ring.
- The small site is the recorded `Scheme.ProEt`, used throughout `pbcModules`.
  `PbcCompletedDerived X (pbcIntegralDatum ℓ E)` unfolds to the unbounded derived
  category of module sheaves over the actual completed coefficient sheaf
  `pbcAdicCompletion X (pbcIntegralDatum ℓ E)`. This is the coefficient presentation
  the statement expressly permits. The continuous-function and tensor conventions
  are imported from the recorded dependency modules; no second sheaf, tensor, or
  constructibility predicate is introduced. `continuousCoefficientModule` realizes
  the local model A_Y tensor_A P, and `IsContinuousConstructible` uses finite
  stratifications and finitely presented P. The coefficient identification is the
  normalized comparison of `continuousCoefficientImmersionRestriction`, imported
  here; its choice is not an additional hypothesis or part of the theorem's data.
- `(K : PbcIntegralCategory ℓ E X hdim hℓ)` is exactly the published full subcategory
  `PbcBoundedConstructibleComplete X (pbcIntegralDatum ℓ E)`, so `K.obj` is its ambient
  object and `K.property` is its defining predicate. The recorded
  `pbcBoundedConstructibleComplete` in `IntegralUniformCoefficient` specializes the
  very same predicate to the unlifted ring with E in Type (u+1). We reuse its public
  supporting module's original, lifted specialization matching the continuous
  coefficient interface and the already stated compactness theorem, rather than
  defining another category or changing the dependency record.
- `(I : Type (u + 1)) [Countable I]` expresses the small countable family, with no
  nonemptiness assumption. `(M : I → PbcCompletedDerived X (pbcIntegralDatum ℓ E))`
  allows arbitrary ambient derived objects. `_hM : ∃ n : ℤ, ∀ i : I,
  DerivedCategory.IsGE (M i) n` is precisely a common cohomological lower bound;
  no upper bound, constructibility or completeness is required of M.
- `(q : ℤ)` includes all integer shifts. `(s : Cofan M) (_hs : IsColimit s)` supplies
  any ambient derived coproduct, without completing it or assuming RHom preserves it.
  Such coproducts exist in this Grothendieck derived category; choosing an arbitrary
  colimiting cofan expresses the same comparison independently of chosen sums.
- `Linear.rightComp (PbcIntegralRing ℓ E) K.obj
  ((shiftFunctor (PbcCompletedDerived X (pbcIntegralDatum ℓ E)) q).map (s.inj i))`
  is the linear map f ↦ f followed by the shifted ith coprojection.
  `DirectSum.toModule` assembles exactly these maps from the algebraic direct sum
  of `K.obj ⟶ (M i)⟦q⟧` to `K.obj ⟶ s.pt⟦q⟧`. `Function.Bijective` asserts that
  this specified linear map is an isomorphism of coefficient modules. The linear
  structure is the existing `pbcCompletedDerivedLinear`, induced by actual constant
  scalar sections, not an arbitrary module structure.

Dependency declarations read and reused (module, declarations):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the imported coefficient integer
  ring, uniformizer and quotient constructions from `CoefficientExtension`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`.
- `Sheaf.Paper.ContinuousConstructibleModule`:
  `AlgebraicGeometry.ProEtale.continuousCoefficientModule` and
  `AlgebraicGeometry.ProEtale.IsContinuousConstructible`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`.
- `Sheaf.Paper.IntegralUniformCoefficient`: `Scheme.pbcBoundedConstructibleComplete`;
  its public supporting `Sheaf.Paper.BoundedConstructibleComplete` supplies
  `PbcIsBoundedConstructibleComplete`, `PbcCompletedDerived`, `PbcIntegralCategory`,
  `PbcIntegralRing`, `pbcIntegralDatum`. Its public `PbcRationalCategory` supplies
  `pbcCompletedScalarSections` and `pbcCompletedDerivedLinear`.
- `Sheaf.Paper.AdicCoefficientDatum`: `Scheme.completedReductionTower` and the actual
  completed ring and coefficient datum; `BoundedConstructibleTower` supplies the
  published `pbcModules` and `pbcAdicCompletion` abbreviations of those constructions.
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`:
  `Scheme.continuousCoefficientImmersionRestriction`.

All five stated proof-dependency modules are imported without `public`:
`IntegralConstructibleBoundedBelowCompactness.integralConstructible_boundedBelow_compactness`
(in namespace `AlgebraicGeometry.Scheme`), `AdicGlobalDerivedHom.adicGlobalRHom`
(same namespace), `WeilConjectures.CategoryTheory.DerivedModuleHomologyCoproduct`
(`AlgebraicGeometry.derivedModuleHomology_coproduct`),
`Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`
(`CategoryTheory.ringedDerived_closed_symmetric_monoidal`), and
`Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel`
(`CategoryTheory.DerivedInternalHomSectionsModel.derived_internalHom_sections_model`).
Their natural-language proof is included in full in the theorem docstring, including
coefficient linearity and the canonical-map identification.

Edge cases checked: empty I gives the zero coproduct and a bijection between zero
modules; singleton I gives postcomposition with a shifted isomorphism. q = 0 and
negative q use the same integer shift API. Zero K, zero summands and the empty scheme
are permitted. Torsion integral K is not excluded by any flatness assumption.
There is no assertion when the family has no common lower bound. Site objects and
coefficients have universe u+1, site morphisms universe u; no equality of those
universes is imposed. All variables and universes are explicitly bound.

Searches performed using the prescribed msearch wrapper:

- leanfinder: "Hom groups from a bounded constructible complete integral pro etale
  complex commute with countable coproducts with a common lower cohomology bound".
  Eight hits, concerning condensed locally constant colimits and internal projectivity;
  none states this integral constructible Hom comparison.
- loogle: "DirectSum.toModule, CategoryTheory.Linear.rightComp". Zero hits.
  Direct source inspection finds both generic constructors in Mathlib, and these are
  used directly rather than copied.
- grep: "constructible.*(compact|[Hh]om)|[Hh]om.*constructible", CategoryTheory.
  Zero Mathlib hits.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for integral-constructible Hom/sum and
  Hom-coproduct terms finds the stronger `integralConstructible_boundedBelow_compactness`,
  the distinct etale internal-Hom theorem `isIso_sigmaComparison_derivedHom_of_constructible`,
  and generic coproduct machinery, but no same-statement declaration. The stronger
  theorem is used as a proof dependency, not recorded as an exact existing match.
- rg for the full item id in `lean/WeilConjectures` found no result; rg of the proposed
  declaration name in both libraries and `dag/lean_names_upstream.json` found no collision.

Source checked directly: the local Bhatt--Scholze PDF, Lemma 6.8.12, states that
RHom(K,-) commutes with arbitrary direct sums in D≥0; its common-lower-bound shifted
form gives this consequence on Hom in every degree. The subsequent Lemma 6.8.13
uses exactly its integral Ext consequence. No statement dispute was found.

Validation: the prescribed scompile wrapper compiled the module cleanly, with no
errors or warnings. No local compiler, global build, or live-source edits were used.

## Second reading by Q53

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
