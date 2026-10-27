## Worker report

The module `Sheaf.Paper.CompletedInverseImageScalarCounit` states
`WeilConjectures.completedInverseImage_scalarCounit`. It contains both counit
identities as equalities of derived morphisms, conjoined for every constructible
complete integral object. No item statement, proof, or dependency edge is changed.

The additional declarations construct the counit already introduced in the item's
statement: the site isomorphism is a concrete composite of Mathlib `Over.mapComp`
and `Over.mapId`, both identity on underlying schemes. A named existence-and-uniqueness
lemma fixes the module isomorphism on every section using the inverse site arrow.
The corresponding definition chooses that uniquely specified isomorphism, rather
than a bare equivalence counit. `integralInverseImageDerivedCounit` applies it
termwise and localizes, with the standard composition and identity comparisons.
These helpers belong to this item's counit notion; they introduce no independent
notion needing a new node. Their sole postponed theorem is the linearity/naturality
and unique characterization of the canonical u already in the item's statement.

Hypothesis and clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`.
- E and L are fields with `Algebra ℚ_[l]` and `FiniteDimensional ℚ_[l]`.
  `ι : E →ₐ[ℚ_[l]] L` encodes the inclusion. Such a field homomorphism is injective;
  its use allows arbitrary isomorphic models of the specified subfields, without
  imposing a second choice of algebraic closure. The recorded Padic constructions
  supply the valuation rings, their finite quotients, and the completed coefficients.
- `X Y : Scheme.{u}`, `g : X ⟶ Y`, `[IsIso g]` and `inv g` encode the scheme
  isomorphism and its unique inverse. The two `IsUnit` stalk hypotheses express
  invertibility of l on X and Y, equivalently invertibility in every residue field.
- `ProEt.topology` is the small pro-etale site (object universe u+1, Hom universe u),
  and `integralTowerModules` uses its completed coefficient sheaf, not the discrete
  constant valuation ring.
- `K : sfIntegralConstructibleCategory l E Y` retains derived completeness, every
  constructible positive reduction, and its single uniform finite interval.
  The full subcategory inclusion is `K.obj`; its membership is `K.property`.
- G_F and H_F are `inverseImageIntegralDerived l F g` and the same at `inv g`.
  Their coefficient actions use the recorded finite-projection-normalized completed
  maps. The theorem `isomorphismComparisonInputs_constructible` supplies the exact
  membership needed to apply beta to G_E K, with no extra hypothesis.
- C is `integralOrdinaryDerivedScalar`, the exact finite-free ordinary tensor model
  used by the recorded b. This is canonically identified with
  `completedDerivedScalarExtension` by `isomorphismScalarModel_existsUnique`.
  Its first normalization fixes the ordinary-derived counit on every complex;
  its second normalization identifies `scalarCompletion` with the SPECIFIED
  `completedScalarComparison` after that isomorphism. Thus no arbitrary replacement
  for chi is used.
- T is `integralScalarExtension`, definitionally the same universal resolving-class
  localization as `integralScalarExtensionOfUniverses` in this common ambient size.
- b is exactly `isomorphismScalarTensorDerived`; beta is exactly
  `isomorphismComparisonScalarBeta`, whose definition is chi_X inverse, then b,
  then G_L(chi_Y). Its inverse-map version uses hY,hX in that order.
- The first conjunct is b for the inverse map at G_E K, then H_L(b for g at K),
  then u_L at C_Y K, equal to C_Y(u_E at K). Lean's composition order is left to right.
  Both sides have source C_Y H_E G_E K and target C_Y K.
- The second conjunct replaces b by the two specified beta maps and C by T.
  Both sides have source T_Y H_E G_E K and target T_Y K.
- These are ambient derived-category arrow equalities. Fullness makes them exactly
  the requested arrow equalities on the full constructible categories. Naturality
  in K follows from the constituent natural transformations: b, chi and u are
  natural, and inverse chi is natural on the full constructible category where
  its components are invertible. The pointwise universal statement covers every
  object and hence is equivalently the equality of those natural transformations.

Dependencies read and used (all direct statement dependencies are publicly imported):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and the imported recorded coefficient data.
- `def-weil-scheme-morphism-properties` is a convention node with no declaration;
  schemes, morphisms and isomorphisms are the Mathlib objects.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`, topology.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, reexporting the completed limit sheaf.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructibleCategory` and predicate.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `AlgebraicGeometry.Scheme.proEtaleSheafInverseImage`, base change and coefficient maps.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `isoSectionwiseInverseImage`, `isoSectionwiseModuleInverseImage`, and exactness.
- `Sheaf.Paper.IsomorphismDerivedPullback`:
  `isomorphismCompletedCoefficientComparison`, `isomorphismIntegralDerivedPullback_termwise`.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`: `integralScalarExtensionOfUniverses`;
  the imported `integralOrdinaryDerivedScalar` is its ordinary tensor model.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`: `completedScalarComparison`,
  `finiteFreeCompletedScalarComparison`.
- `Sheaf.Paper.IsomorphismComparisonScalarExtension`: `isomorphismScalarTensorDerived`,
  `isomorphismComparisonScalarBeta`, `isomorphismComparisonInputs_constructible`,
  `isomorphismScalarModel_existsUnique`.
- `Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison` supplies the
  already defined exact sectionwise `inverseImageIntegralModules` and derived functor.
  It is the recorded model publicly used by the scalar comparison dependency.
- Proof imports: `Sheaf.CategoryTheory.FiniteFreeScalarCoordinates`
  (`CategoryTheory.Mod.sheaf_finiteFreeScalarCoordinates`),
  `Sheaf.CategoryTheory.RingedSiteModules` (`CategoryTheory.ringedSiteModules`),
  `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
  (`CategoryTheory.Functor.exactFunctor_derivedFunctor`),
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
  (`SheafOfModules.cochainModulesMonoidal`),
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
  (`CategoryTheory.Functor.mapDerivedCategoryFactors`), and
  `Mathlib.CategoryTheory.Localization.Predicate`
  (`CategoryTheory.Localization.natTrans_ext`, `Localization.lift`).

Edge cases checked: g = identity; E = L with identity inclusion; zero K; empty scheme;
negative cohomological degrees; arbitrary constructible finite amplitude; no flatness
of K and no noetherian or nonempty-scheme hypothesis. The site construction preserves
its distinct object/Hom universes. A single ambient u contains the finite field models
and schemes as in the recorded constructible and b interfaces; it is not a hypothesis
identifying the site's object and morphism universes. No false statement or correction
was found.

Searches, performed through msearch.py for this item:

- leanfinder: `Inverse-image tensor scalar comparison conjugated by completion commutes
  with the counit of inverse scheme isomorphisms`: eight hits, scheme tensorCongr and
  pullbackSpecIso identities; none concerns these completed coefficient sheaves/maps.
- loogle: `CategoryTheory.Equivalence.counit_naturality`: one hit, generic naturality of
  an equivalence counit; it does not give the specified tensor/counit compatibility.
- grep, CategoryTheory: `counit.*[Ss]calar|[Ss]calar.*counit`: zero hits.
- leansearch: `Completed extension of scalars commutes with inverse image equivalence
  counit using the canonical tensor comparison`: eight ordinary module scalar counit
  and linear-equivalence hits, no completed sheaf comparison coherence.
- rg on `lean/WeilConjectures` and `lean/Sheaf` for the item ID and completed/scalar
  counit patterns found ordinary adjunction counits, finite-coefficient and open-map
  comparisons, and completed scalar functor counits; none states the two identities.
- rg for `integralInverseImageCounit|completedInverseImage_scalarCounit` on project,
  Mathlib and `dag/lean_names_upstream.json`: no declaration clash.
- Read the existing inverse-image composition module: its normalized compositor is
  for two arbitrary maps and has no identity-map counit; it supplies no duplicate u.

Validation: the module, including both theorem statements, compiled cleanly using
scompile.py on the server (sandbox 13.0 s, library 10.4 s). Only the two named theorem
proofs are postponed; all definitions have real data.

## Second reading by Q152

A second pass over the node and completed file checked the composition directions,
the inverse-map hypothesis order, the precise source and target of both conjuncts,
and the full constructible membership at the inner beta input. It also checked the
ordinary-derived-model normalization against `isomorphismScalarModel_existsUnique`:
its equation e.hom followed by completedScalarComparison equals scalarCompletion,
so the existing beta uses exactly the specified chi in that model. The section
formula uses the inverse site arrow, which gives a restriction from the twice
reindexed site object to U, as required for the counit direction. No mismatch was
found. This is a self-check, not an independent reviewer: the dispatcher expressly
prohibits starting other agents; the maintainer's independent review remains pending.
