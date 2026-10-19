## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedSupportDirectImageComparison` states
`AlgebraicGeometry.ProEtale.derivedSupportDirectImageComparison`. Its only postponed proof
is that theorem. It asserts the existence of the normalized natural comparison, packaged
in `DerivedSupportDirectImageComparison`. The data fields are conclusions of the theorem,
not assumptions on the input. The natural isomorphisms are fixed by explicit identity
normalizations on every K-injective complex; this is not an unspecified natural isomorphism.
There is no choice of data from a sorry theorem in any definition.

The node's natural-language statement, dependencies, and proof are unchanged. No new DAG
nodes or dependency repairs are required. The auxiliary declarations specialize existing
functors or spell out the normalization diagrams belonging to this same node.

Clause-by-clause correspondence:

- A finite commutative ring is `A : Type (u + 1)`, `[CommRing A]`, with `[Finite A]` on
  the theorem. No topology, characteristic, primary-torsion, or nonzero-ring assumption
  is imposed. The ordinary constant-coefficient presentation is `Sheaf J (ModuleCat A)`.
  A fixed scalar action extends uniquely to locally constant sections of the constant
  ring sheaf, so this is the established ordinary constant-ring module-sheaf encoding.
- Schemes are `Scheme.{u}`. Closed immersions are `(i : C ⟶ T) [IsClosedImmersion i]`.
  These binders occur for every component of `b`, the forgetting square, and all supported
  restriction fields. The theorem supplies the family for every such scheme and immersion.
- The two sites are precisely `T.smallEtaleTopology` on `T.Etale` and
  `Scheme.ProEt.topology T` on `T.ProEt`. The actual site object and morphism universes
  remain those of the dependencies; no equality between them is added. The coefficient
  universe is the common larger universe, `u + 1`, as in the published fixed-ring APIs.
  Small representatives and the existing Grothendieck/K-injective instances supply the
  universe convention. Generic `supportResolutionUnit` separately binds category, Hom,
  and derived-localization universes.
- `supportNu A T` is the existing `comparisonLowerStar (ModuleCat A) T`, hence literally
  restriction along `Scheme.toProEt T`, as specified by the site-comparison dependency.
- `supportEt` and `supportPro` are transparent specializations of the recorded
  `CategoryTheory.Sheaf.supportedSectionsFunctor`, with the recorded
  `Etale.supportRestrictionArrow i` and `ProEtale.supportRestrictionArrow i`. They take
  the actual restriction kernel. Their morphisms are the existing kernel maps; no second
  kernel construction or substitute support functor is introduced.
- Every derived support, section, and direct-image functor is `.rightDerivedFunctor`,
  on `DerivedCategory` of integer-indexed complexes. There is no `DerivedCategory.Plus`,
  boundedness, étale-origin, finite-type, Noetherian, or quasi-compactness hypothesis.
- `b` is the required natural isomorphism `Rν_* ⋙ RΓ_C^et ≅ RΓ_C^proet`.
  Its component at any `N` is exactly the displayed `b_{C,N}` in the node.
- `kernel_normalization` specifies this isomorphism on every K-injective `J`.
  `supportResolutionUnit` is the actual derived-functor unit, transported from the
  homotopy localization to complexes by the existing `quotientCompQhIso`.
  `supportKernelIdentity` has identity components, so mapping it on complexes and
  localizing is precisely the identity between the two kernel complexes. The two
  resolution-unit factors on the other side are the canonical computations of
  `RΓ_C^et(Rν_* QJ)`. For K-injective `J` they are isomorphisms: `ν_*` preserves
  K-injectives as the right adjoint of the exact comparison inverse image. Thus this
  equation prescribes the required identity, not an arbitrary automorphism.
- `supportForgetEt` and `supportForgetPro` are the actual kernel inclusions.
  The field `forget` is equality of natural transformations around the square with the
  final-object comparison `g`, so it expresses compatibility with forgetting supports.
- An arbitrary open is `(V : T.Opens)` and the support on it is
  `pullback.snd i V.ι`, the required `C ×[T] V → V`. The exact restriction functors
  `supportRestrictEt/Pro` reuse the existing `openImmersionRestriction` constructions.
  Their left-adjoint instances reuse their existing restriction/direct-image adjunctions.
- The auxiliary `openEt/openPro` maps are uniquely normalized on ordinary sheaves by
  `openEt_sections/openPro_sections`: after the monic support inclusion they are the
  literal restriction of ordinary sections, `supportSectionRestrictionEt/Pro`.
  The `derivedOpenEt/Pro_normalization` fields say that derived restriction is obtained
  by applying these same maps on every K-injective complex, with the canonical exact
  restriction factorization `mapDerivedCategoryFactors`. These equations determine
  the usual support-restriction arrows and make the restriction identifications explicit.
- `rho` is the canonical isomorphism `j_et^* Rν_{T,*} ≅ Rν_{V,*} j_proet^*`.
  `rho_normalization` fixes it on every K-injective representative by
  `supportOpenIdentity`, the literal underived restriction/direct-image identity.
- `open_square` is the equality between `b` followed by pro-etale support restriction
  and etale support restriction followed by `rho` and the restricted `b`.
  No restriction on `V` is imposed, including no quasi-compactness condition.
- `supportOpenPullback` is the dependency's specified adjunction-mate inverse-image
  comparison, transported through the existing open-restriction isomorphisms.
  `supportDerivedOpenPullback` is its termwise derived image, using the canonical
  composition isomorphisms. `supportDerivedAdjunction` is the canonical derived
  comparison adjunction. The field `unit_square` equates the two restricted derived
  units with exactly these maps, for every unbounded etale complex `M`.
- `g` and `final_normalization` give the final-object comparison, normalized by the
  literal identity `(ν_*J)(T) = J(T)`. `full_support` states that forgetting support for
  `i = 𝟙 T` is invertible on both sites. Together with `forget`, this identifies
  `b_{T,N}` with `g` under the canonical full-support identifications, as requested.

The structure notation packages the existential comparison and all its equations.
The normalization equations uniquely determine its maps: on ordinary kernels use the
monic inclusion; on derived functors use K-injective representatives and their Hom
bijection. Consequently the statement retains the canonical construction, and all
auxiliary existential data describe the canonical arrows in the node. It does not
assume the desired comparison or choose an unnormalized equivalence.

Dependency declarations used and read:

- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`, the
  sheafification of the constant presheaf; fixed-ring module sheaves use its scalar action.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  ordinary ringed-site module category. The established fixed-ring encoding here is
  `Sheaf J (ModuleCat A)`, not condensed modules or structure-sheaf modules.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and `Scheme.Etale`;
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`; the size-convention node is metatheoretic and has no declaration.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparisonModules`;
  its functors and adjunction are the upstream `comparisonLowerStar`, `comparisonUpperStar`,
  and `comparisonAdjunction` in `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`.
- `Sheaf.AlgebraicGeometry.SupportCohomology`: `Sheaf.supportedSectionsFunctor`, its
  additive instance, and the etale/pro-etale `supportRestrictionArrow` declarations.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`: `CochainComplex.IsKInjective`;
  this is the dependency's `mathlib_match`, not a missing Lean record.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `supportSiteComparison_pullback_coherent` and its canonical
  `supportSiteComparisonCoefficientPullbackIso`, used by `supportOpenPullback`.
- The exact open restriction functors and their right-image adjunctions come from
  the existing etale and finite-coefficient pro-etale open-immersion `Defs` modules.
- The unbounded unit, natural-transformation, and derived-adjunction APIs come from
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor` modules
  `Defs`, `Comp`, `KInjective`, and `Adjunction`. Available proof-dependency modules
  are imported without `public`. The proof-only node
  `lem-pur-comparison-pullback-open-unit` has no recorded declaration yet, so has no
  import; it is named in the proof docstring for the later proof stage.

Source check: read the current main-20261015 blueprint proof paragraph 4, the node's
complete eight-step expansion, Stacks derived.tex 070Y/070K and 08BJ,
sites-cohomology.tex 08FI, and proetale.tex section 099R. These support the unbounded
kernel computation, preservation and restriction of K-injectives, and the normalization.

Edge cases checked mathematically before and against the final statement:

- `C` empty: the complement is all of `T`, the kernel is zero, and both comparisons
  are the unique map of zero support objects.
- `C = T`: the empty-covering sheaf axiom makes sections on the complement zero;
  the support kernel is all final-object sections. This is the explicit full-support clause.
- `T` empty, `V` empty, `V = T`, zero complexes, and the zero ring are included.
  The exact restriction identifications and the unit equations remain well-typed;
  no nonempty/nontrivial assumption is made.
- Arbitrarily unbounded `N` and `M`, an open that is not quasi-compact, and complexes
  not of etale origin are all included. Only K-injectivity of the test representatives
  occurs in normalization conclusions, not as a restriction on derived objects.
- Scheme object and morphism universes are not identified; the helper's category
  and localization universes are independently bound.

Searches made:

- `msearch.py ... leanfinder "derived sections with closed support commute with etale
  proetale direct image K injective"`: eight unrelated scheme/image injectivity hits;
  no supported derived comparison.
- `msearch.py ... loogle "Sheaf.sectionsFunctor, Functor.rightDerived"`: no hits;
  `Sheaf.sectionsFunctor` is not an identifier in this Mathlib.
- `msearch.py ... grep "support.*[Cc]omparison|derivedSupport|supportedSections"`:
  no Mathlib match.
- `rg` of the upstream `WeilConjectures` source for the exact node id returned no hit;
  searching support-comparison/derived-support terms found compact-support comparisons,
  not this arbitrary-complex closed-support/direct-image statement.
- `rg` of `lean/Sheaf` found `SupportSiteComparison`, `SupportCohomology`,
  `EtaleSupportedSections`, and the open-comparison interfaces. The former states a
  bounded-below comparison on etale-origin objects with geometric hypotheses, so is
  not this node. The common kernel and canonical pullback declarations are reused.
- Searched Mathlib, upstream, and `lean/Sheaf` for the new helper and structure names;
  no name collision was found. Live `scompile.py --source` confirmed the recorded
  comparison-pullback source, matching the shared checkout.

Validation: compile every delivered file with `scompile.py`; dry-run and final
preflight/compilation results are recorded by the delivery wrapper. Only the one named
main theorem is left with `sorry`, and its docstring contains the complete eight-step
proof plan. No disputed statement or source-based statement correction was needed.


## Returned-delivery validation

Rechecked the retained packet on 2026-10-17 UTC for the return reporting a
60-second sandbox timeout at immutable head 145cef2ee3fd. The prescribed initial
`deliver2.py Q15 lem-pur-derived-support-comparison-direct-image --no-push`
passed: dry-run commit 9d483594ae compiled both the sandbox and library paths and
passed the current server preflight. The timeout did not recur. Following the
repair brief's saved-packet instruction, the Lean file is retained unchanged.

Self-check against the current node and recorded dependency interfaces confirms
finite commutative coefficients, arbitrary schemes and closed immersions,
unbounded derived objects, identity normalization on K-injective kernel complexes,
forgetting supports, every open restriction, the canonical comparison-adjunction
unit equation, and the full-support final-object comparison. The auxiliary maps
are constructed or normalized by the displayed equations. All variables and
universes are bound explicitly; the sole `sorry` is the named main theorem.
The node copy differs from the current shared node only in `lean`; its recorded
signature matches the file, all helper declarations are listed, and every Lean
line is at most 100 characters. No statement correction was required.

## Second reading by Q15

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
