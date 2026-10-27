## Worker report

The module `Sheaf.AlgebraicGeometry.SupportInjectiveExactModels` states
`AlgebraicGeometry.ProEtale.supportInjectiveExactModels`, with one `sorry` and no new
construction. The node statement and proof are unchanged. The item's statement dependencies
gain the already-landed `def-pur-support-triangle`, which owns the canonical sheaf row used
here. All other node fields are unchanged.

Hypotheses and clauses, read against the source and Lean:

- Finite commutative coefficients are `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  This is the established module universe for `Scheme.{u}`. `A = 0` is allowed.
- The schemes, closed and open immersions, quasi-compact complement and complementarity
  are `{X Z U : Scheme.{u}}`, `(i : Z ⟶ X)`, `(j : U ⟶ X)`, the three morphism-property
  instances, and `hPair : IsCompl (Set.range i) (Set.range j)`. No finiteness condition
  on X or constructibility condition on the coefficients is imposed.
- Ordinary constant-A sheaves use the published `Sheaf (Scheme.ProEt.topology X)
  (ModuleCat.{u + 1} A)` presentation. `finiteCoefficientRealization_exact` in
  `ProEtaleFiniteModules` identifies this with the recorded intrinsic coefficient module
  category. These are ordinary module operations, with no completion.
- `i^!_0` is the recorded `finiteClosedUpperShriek A i j`, namely closed inverse image of
  `finiteSupportedSections A j`, the kernel of the actual open adjunction unit.
- A bounded-below injective complex is quantified as `I : CochainComplex.Plus ...` with
  `[∀ n : ℤ, Injective (I.obj.X n)]`. Its represented derived object is
  `DerivedCategory.Plus.Q.obj I`. An arbitrary K represented by I is obtained by
  transporting through its specified representing isomorphism; all comparisons in the
  statement are natural transformations, so this introduces no additional assumption.
- E, B and C are `supportedSectionsComplex A i j hPair I.obj`, `I.obj`, and
  `supportCComplex A j I.obj`. The published `supportModelSequence` has exactly these
  objects, canonical supported-kernel inclusion as `f` and open adjunction unit as `g`.
  Its `ShortExact` clause and its evaluation at every integer express both complex and
  degreewise short exactness.
- Preservation of any strict lower bound is stated for E, C, i^!_0I and j^*I using
  `IsStrictlyGE`. B already has the given lower bound. Injectivity of every term of E,
  C, j^*I and i^!_0I is stated with `Injective`; B's injectivity is the input.
- The invertible `rightDerivedFunctorPlusUnit` for i^!_0 at I gives the canonical model
  of Ri^!_0K. Its invertible unit for i_* at i^!_0I gives E as the model for
  Ri_*Ri^!_0K; i_* is exact in this complementary quasi-compact setting, so this is
  i_*Ri^!_0K. The invertible unit for j_* at j^*I gives C as Rj_*j^*K. Exact j^*
  descends termwise, so its termwise I is precisely a representative of j^*K.
- `a` is a NATURAL isomorphism from global sections of E to the existing
  `Sheaf.supportedSectionsFunctor` for the actual specified arrow j, rather than a
  newly chosen complement. Its displayed normalization is the literal kernel inclusion
  after evaluation of `supportModelInclusion` on global sections. Applying it termwise
  identifies the supported section complexes, including differentials.
- `c` is a NATURAL isomorphism `Γ(U,j^*(-)) ≅ (-)(U)`. Its displayed equation with
  `globalSectionsLowerStarIso` says that the image of the sheaf row's second arrow
  becomes exactly restriction from X to U. Together with a it identifies the section
  row with the claimed kernel/restriction row.
- `Function.Injective (kernel.ι ...)`, `Function.Exact (kernel.ι ...) (I^n.res j)` and
  `Function.Surjective (I^n.res j)` express all three degreewise short exactness
  conditions for that row of A-modules, including surjectivity in every integer degree.
  The maps are ModuleCat morphisms, hence A-linear.
- Invertible derived units for Γ_X at I and E, Γ_U at j^*I and Γ_Z at I give exactly
  the global computations. The natural isomorphism e identifies
  RΓ_X Ri_* Ri^!_0 with RΓ_Z. The long displayed equation normalizes e by the three
  successive derived units and the actual chain isomorphism induced by a. Since i_*
  is exact, its right-derived version is its ordinary termwise functor. Thus this is
  the asserted `RΓ(X,i_*Ri^!_0K) = RΓ_Z(X,K)` identification, with the usual units.
- The final two equations give naturality of both actual row arrows in every chain map
  `t`. Naturality of a, c, e, the right-derived units and exact termwise factorizations
  supplies naturality of every section and model identification. Applying the functors
  and natural isomorphisms to complexes gives chain maps automatically.

Dependency declarations read and used (the import paths are their module names):

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, scheme morphisms.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`.
- Mathlib.AlgebraicGeometry.OpenImmersion: `IsOpenImmersion`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and Morphisms.QuasiCompact:
  `LocallyOfFiniteType` and `QuasiCompact`; only quasi-compactness is required here.
- Sheaf.AlgebraicGeometry.ProEtaleFiniteModules: `FiniteCoefficientModules`,
  `finiteCoefficientRealization_exact` and the same module-valued presentation.
- Mathlib.Algebra.Homology.DerivedCategory.Basic and TStructure: `DerivedCategory`,
  `DerivedCategory.Q`, `DerivedCategory.Plus`.
- Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations: the ordinary operations and
  its published finite-operation reexports; the node's constant-ring derived operations
  use these same exact inverse images and ordinary right-derived direct images.
- Sheaf.AlgebraicGeometry.ProEtalePairFlasque and its supported-sections import:
  `finiteSupportedSections`, `finiteSupportedSectionsι`, `finiteClosedUpperShriek`,
  `finiteSupportedClosedComparison_isIso`, `finiteSupportedSections_sections`.
- Mathlib.CategoryTheory.Preadditive.Injective.Basic: `Injective`.
- Sheaf.AlgebraicGeometry.SupportCohomology: `Sheaf.supportedSectionsFunctor`, including
  its action on morphisms and additivity. This is the actual kernel construction in
  `ProEtale.supportSections`, with the arrow for the named open instead of choosing one.
- Sheaf.AlgebraicGeometry.SupportTriangleConstruction (def-pur-support-triangle):
  `supportedSectionsComplex` (reexported from PurSupportExact), `supportModelSequence`,
  `supportModelInclusion`, `supportCComplex`, `supportShriekAdditive`.
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections:
  `globalSectionsLowerStarIso`, `Scheme.ProEt.isTerminalMkId`.
- WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections: `Sheaf.Γ_additive`.

The proof-only imports are the recorded modules for the open/closed adjunctions,
closed-kernel adjoint, open comparison, site localization, ringed-site injective
restriction, Grothendieck property, enough injectives, exact-functor cohomology,
right-derived bounded-below computation and K-injective Hom comparison. In particular
`shortExact_sectionsWithSupport`,
`Adjunction.preservesInjectiveObjects_of_preservesFiniteLimits`,
`proEtale_ringed_closed_kernel_adjoint`, `proEtale_ringed_open_closed`,
`proEtale_ringed_open_comparison`, `weaklyEtale_localization`,
`injective_ringed_site_mono_restriction`, `isGrothendieckAbelianOfUniverses`,
`Functor.rightDerivedFunctorPlus`, `Functor.homologyFunctorIso`,
`CochainComplex.isKInjective_of_injective` and `CochainComplex.IsKInjective.Qh_map_bijective`
are the already-recorded interfaces; none is privately restated.

Sources opened locally: etale-cohomology.tex, section-cohomology-support and
lemma-sections-with-support-acyclic (Tags 09XP and 09XQ); sites-cohomology.tex,
lemma-restriction-along-monomorphism-surjective (093X). The source is available locally,
so no web retrieval was needed.

Edge cases checked before writing: Z empty (zero supported kernel), U empty (identity
supported kernel and zero open term), X empty (all section modules zero), zero coefficient
ring, the zero complex, a complex concentrated in one integer degree, and arbitrary
negative lower bounds. No connectedness, nonzero ring or nonempty scheme assumption is
introduced. Site object/morphism universes remain u+1/u and module values u+1.

Searches performed with the prescribed msearch.py wrapper:

- leanfinder: "Bounded below injective proetale module sheaf supported kernel and
  restriction complexes are injective and give short exact global sections". Hits include
  `CochainComplex.isKInjective_of_injective`, `ShortComplex.ShortExact.moduleCat_injective_f`,
  and local injectivity facts; no full statement.
- loogle: "CategoryTheory.Injective, CochainComplex.IsKInjective". Two hits, including
  the bounded-below K-injectivity theorem; no full support/global-section row theorem.
- grep: "support.*[Ii]njective|[Ii]njective.*support". General support and combinatorics
  hits; no categorical support-injective global-model statement.
- leansearch: "Injective proetale support restriction sheaves and global section complexes
  compute derived support and direct image naturally". General global-section restriction
  lemmas and scheme section maps; no full theorem.
- rg in lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for the item id,
  `supportInjectiveExactModels`, support/injective/model combinations. The closest existing
  theorem is `proEtaleInjectiveSupportGlobalModel`: it supplies the closed support/global
  comparison but does not assert this item's exact sheaf row, surjective section row or
  all the open models. SupportTriangleConstruction supplies the row, reused here.
  The earlier global-boundary module contains related downstream statements; it is not
  imported, avoiding any circular dependency on this item's consumer.

No new notion, dependency repair, statement correction or disputed statement is needed.
The definition-node signature example CompactObject.lean has been withdrawn; its node now
records WeilConjectures.CategoryTheory.CompactObject. That replacement source was read.
The source and report were checked directly against the node again after compilation;
independent maintainer review is supplied by the delivery process, not represented here
as a second worker's review.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
