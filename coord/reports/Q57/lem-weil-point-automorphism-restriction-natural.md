## Worker report

The module `Sheaf.Paper.PointAutomorphismRestrictionNatural` states
`AlgebraicGeometry.ProEtale.point_automorphism_restriction_natural`, with its sole
postponed proof `sorry`. It gives real definitions for the canonical maps and
coefficient choices used in this statement. It changes only the item's `lean` record;
there are no new nodes, dependency repairs or statement corrections.

Hypotheses and objects, matched individually:

- The tuple p,a,q,k₀,k is the binder `D : FiniteFieldDatum.{t}`. Its existing fields
  include primality, positive exponent, cardinality, and the algebraic closure.
- The prime ℓ is `l : ℕ` with `[Fact l.Prime]`; `_hl : l ≠ D.p` is retained even
  though the canonical constructions work without using it.
- The finite extension is `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]`. Its valuation ring, chosen uniformizer and finite
  quotients are precisely the recorded `Padic.coefficientExtensionIntegers`,
  `Padic.coefficientExtensionUniformizer` and `Padic.coefficientExtensionRing`.
- The point s is literally `Spec (.of D.k)` throughout. The morphism g has exactly
  this source and target and `[IsIso g]`; there is no `Over` or k₀-linearity binder.
- The small site is `Scheme.ProEt` with `ProEt.topology`. Its object and morphism
  universes remain t+1 and t. The coefficient/module universe is `max u (t+1)`;
  there is no equation between u and t.
- `a : Option ℕ` codes precisely the two allowed coefficient cases. `some n` is
  A_{E,n+1} (covering every positive exponent, including one); `none` is O_E.
  `pointRestrictionScalars` lifts the actual ring into the common universe.
  `pointRestrictionRing` selects `integralCoefficientSheaf` or
  `completedIntegralCoefficientSheafUnrestricted`. The latter is the inverse
  limit of quotient sheaves, never the discrete constant sheaf O_E.
- `pointRestrictionCoefficientMap` selects the recorded
  `inverseImageFiniteCoefficientMap` or `inverseImageCompletedCoefficientMap`.
  Its invertibility instance only reuses the dependency's invertibility proofs.
  `pointRestrictionInverseImage` is the recorded
  `isoSectionwiseModuleInverseImage` through this map: its action is through
  `inv c`, with the original underlying abelian sections.

Every clause of the conclusion:

- U is `ProEt.mk (𝟙 s)`. V is `(proEtaleIsoPostcompose g).obj U`, whose structure
  morphism is id ≫ g. `pointRestrictionArrow g` has underlying map g and target U;
  its defining triangle is exactly g ≫ id = id ≫ g.
- G is expressed in the dependency's canonical sectionwise inverse-image model.
  `proEtaleIsoInverseImageIdentification` fixes the identification by the actual
  distinguished comma coprojection; `IsoSectionwiseInverseImage` reexports that
  interface and supplies the identical sectionwise model in independent coefficient
  universes. Thus `(GM)(U)` has the underlying group M(V), and the distinguished
  insertion is literally identity in these normalized coordinates.
  `pointRestrictionRaw` is restriction along `pointRestrictionArrow g` on the
  underlying abelian presheaf. It is therefore precisely ins composed with res in
  the statement's evaluation coordinates, rather than an unspecified isomorphism.
- `pointRestrictionScalarAt` is `toSheafify` on constants at finite level. At
  integral level it composes that unit with
  `integralConstantToCompletionOfUniverses`, the canonical quotient-cone limit lift.
  The first conjunct says res_g(b) = c⁻¹(b), i.e. σ_R(b) = c⁻¹(b) in these coordinates.
- The second conjunct spells out σ_M(bx) = c⁻¹(b)σ_M(x). The explicit `SMul.smul`
  uses the original module M(V), because c⁻¹(b) belongs to R(V); that is the
  transported target action by definition of `isoSectionwiseModuleInverseImage`.
- The existential `σ` is a natural transformation from the sections functor to
  G followed by sections, valued in `ModuleCat` over the selected scalar ring.
  The following component equation fixes every value to `pointRestrictionRaw`.
  This asserts both linearity for the actual constant scalar actions and module
  naturality. `pointRestrictionSections` is precisely Mathlib module evaluation
  followed by scalar restriction, the construction used by `pointModuleSections`;
  it is written with independent site/coefficient universes.
- `NatTrans.mapHomologicalComplex σ (.up ℤ)` is the specified termwise linear
  chain map. A natural transformation of additive functors gives a chain map for
  each complex and is natural in every chain map. All complexes are ℤ-indexed with
  no boundedness predicate.
- `F` and `H` are functors on the whole `DerivedCategory` of these module sheaves
  with values in `DerivedCategory (ModuleCat Λ)`. `eF` and `eH` identify their
  precomposition with Q with the two termwise sections functors followed by Q.
  This is the localization characterization of the induced sections functors;
  it is not an arbitrary functor or an assumption about exactness. Any two such
  factorizations are canonically isomorphic by the recorded localization leaf.
- `τ : F ⟶ H` asserts naturality for *every* derived morphism v, including roofs:
  `F.map v ≫ τ.app N' = τ.app N ≫ H.map v`. This is the displayed equation of
  the node in Lean's composition order. The final equation conjugates its value
  at Q(N) through eF and eH to `Q.map` of the specific termwise σ. Thus the maps
  are the induced restriction maps, not just an arbitrary natural transformation.
- There is no constructible, bounded, derived-complete or K-flat condition on M,
  the complexes, the derived objects, or their morphisms. No extra exactness
  instance appears as a hypothesis. The standard localization instances only
  choose presentations of the derived categories.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (and its reexported
  `CoefficientExtension`): `Padic.finite_coefficientExtensionRing` and the
  valuation ring/uniformizer/quotient constructions.
- `def-weil-scheme-morphism-properties` is explicitly a convention-only node;
  the needed scheme automorphism is Mathlib's `IsIso` on a scheme morphism.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.mk`, topology.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleBaseChange`, its
  comma-index sheafified left Kan construction `proEtaleSheafInverseImage`,
  the adjunction, and canonical coefficient maps.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: the canonical
  constant-to-completed map; reexported `CompletedIntegralCoefficients` gives
  `integralCoefficientSheaf` and the unrestricted completed limit.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`, reexporting
  `Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison`:
  `inverseImageFiniteCoefficientMap`, `inverseImageCompletedCoefficientMap` and
  its isomorphism theorem; the finite/integral exact inverse-image functors.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules` is exactly
  `SheafOfModules`; the module uses that Mathlib definition directly.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`, reexporting
  `ProEtaleIsomorphismInverseImage`: `proEtaleIsoPostcompose`,
  `proEtaleIsoInverseImageIdentification` and its coprojection normalization,
  `isoSectionwiseInverseImage`, `isoSectionwiseConstantMap`,
  `isoSectionwiseModuleInverseImage` and its additive/exactness instances.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, Q and
  the standard `HasDerivedCategory` presentation.
- `Sheaf.Paper.PointProEtaleSectionsExact`: `pointModuleSections` and
  `point_proEtale_sections_exact`, supplying the proof route for exact sections.
  Its evaluation-and-scalar-restriction construction is used with independent
  universes, so no equality of coefficient and geometric-field sizes is imposed.
- The proof-only leaves are imported explicitly: sheafification and its unit,
  constant sheaves, the continuous left Kan/sheafification adjunction, limits,
  and `Localization.liftNatTrans` / its factorization and uniqueness interface.
  All seven proof steps are reproduced in the theorem docstring.

Edge cases checked: g = id; arbitrary automorphisms not fixing k₀; level n = 1
(the option index zero); the integral case as an actual inverse limit; zero
modules and zero complexes; arbitrary degrees and unbounded complexes; arbitrary
roofs in the localization; and independent u,t. No finite-dimensionality of a
sheaf's sections, finiteness of a module, or completeness of N is imposed.

Searches made with the prescribed msearch wrapper:

- LeanFinder: "restriction transport at a geometric point coefficient normalization
  derived naturality" returned eight ordinary scheme evaluation/restriction lemmas,
  including `Scheme.evaluation_naturality`; none is this pro-etale/completed-derived
  statement.
- Loogle: "natTransΓRes, sheafFiberComapIso, DerivedCategory" returned no hits
  (unknown identifier natTransΓRes for that query).
- grep: `natTransΓRes|sheafFiberComapIso|sigma.*natural` with the initial
  Mathlib/CategoryTheory filter returned no hits. Repeated with `CategoryTheory`
  and `natTransΓRes|sheafFiberComapIso|restriction.*[Nn]at[Tt]rans` found
  `Sites/GlobalSections.lean` and `Sites/Point/Comap.lean`, which provide ingredients
  only, not coefficient normalization or the derived statement.
- LeanSearch: "Restriction transport on pro etale sections at a geometric point
  is linear for finite or completed integral coefficients and natural on unbounded
  derived categories" found eight hits: derived linear functors, ordinary
  restrictions, and additive scalar restriction. No exact statement match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for point restriction,
  automorphism transport and σ found the dependency interfaces and other Frobenius
  constructions, not this statement. Searching the exact node id and all proposed
  declaration names, including `dag/lean_names_upstream.json`, found no duplicate.

The source unit `def-weil-global-geometric-frobenius.md` was read. It motivates
exactly this first transport arrow. Stacks sites.tex, lemma-adjoints-u and
proetale.tex, section-morphism were checked for the coprojection/adjunction and
base-change conventions. As the DAG records, the ambient completed-coefficient
lemma is an agent calculation, not a theorem attributed to Deligne.

Validation: scompile.py checked both the sandbox and actual library-module forms
cleanly (8.2 s and 9.4 s on the clean run). The only `sorry` is the named main theorem.
No disputed statement or node fault was found.

## Second reading by Q57

Author's separate source-and-signature check; independent maintainer review follows
delivery, as specified by the dispatched brief. No other agent was started.

I reopened the node and the final module. The finite-field and coefficient binders
match exactly, including ℓ ≠ p and the absence of a k₀-linearity condition on g.
The option indexing includes both coefficient types and all positive finite levels.
I checked the site arrow's direction, the c inverse action rather than c action,
and the integral scalar map's passage through completion. The component equation
fixes σ to restriction in the distinguished-coprojection coordinates. Bundled
naturality covers both chain maps and every derived morphism; the localization
component equation prevents replacing the induced map by an arbitrary τ. All
complexes remain unbounded, with independent site and coefficient universes.

During this reading/compilation I corrected the site arrow's definitional triangle,
made the original M(V) scalar action explicit in the semilinearity formula,
unfolded Mathlib evaluation for the inherited additive instance, and disabled the
known overly specialized essentially-small sheafification instance locally to this
module's elaboration. The imported common-universe instances supply the same
canonical sheafification and abelian structure. These were elaboration repairs;
no mathematical statement or dependency changed. No remaining mismatch was found.
