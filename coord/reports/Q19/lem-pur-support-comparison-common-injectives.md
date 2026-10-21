## Worker report

The module `Sheaf.Paper.PuritySupportCommonInjectives` states
`AlgebraicGeometry.ProEtale.supportComparisonCommonInjectives` with one `sorry`.
It supplies three real owning-node constructions, without choosing a resolution:
`supportComparisonSource` is the sheaf concentrated in degree zero as an object of
`CochainComplex.Plus`; `supportComparisonAugmentation` is the termwise ordinary unit
followed by direct image of `h`; `supportComparisonDerivedResolutionMap` is `R(Qh)`,
including the canonical factorization of exact inverse image through localization.
The theorem's docstring carries all five proof steps of the DAG node and their citations.
The node copy changes only `lean`. There are no new nodes or dependency repairs.

Hypotheses and clauses, in order:

- The scheme is `T : Scheme.{u}`; the finite commutative coefficient ring is
  `A : Type (u + 1)` with `[CommRing A] [Finite A]`. The common larger universe
  is `u + 1`, the one of both fixed-ring module categories in the recorded APIs.
  The ring is regarded as discrete by the fixed-ring sheaf presentation; no topology
  or additional coefficient hypothesis is needed.
- Ordinary etale and pro-etale module sheaves are respectively
  `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)` and
  `Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)`.
  These are the constant-ring module presentations of the recorded module adjunction
  `T.proEtaleSiteComparisonModules A`. They are canonically identified with the
  ringed coefficient categories by `finiteCoefficientEtaleRealization` and
  `finiteCoefficientRealization` of the imported coefficient node. In particular,
  direct image here is restriction itself, rather than the inverse of coefficient
  realization, which would obscure the node's literal evaluation clause.
- `F` is any sheaf in the first category. `supportComparisonSource T A F` is `F[0]`.
  Applying `comparisonUpperStar` termwise gives its inverse-image complex, representing
  `F_p[0]`. Exactness identifies this with the usual single complex on the inverse
  image sheaf. Outside degree zero the images of zero objects are zero objects;
  no termwise literal identification of an arbitrary left adjoint's zero objects
  is assumed.
- The first conjunct is `∃ J h, QuasiIso h.hom ∧ ∀ n : ℤ, Injective (J.obj.X n)`.
  The binder `J : CochainComplex.Plus ...` gives the lower bound. Thus this is exactly
  the existence of the bounded-below injective resolution of the inverse image.
- The second conjunct quantifies over every `J` and every `h` of that type. Its two
  premises are precisely quasi-isomorphism and injectivity of every term. This
  includes resolutions with arbitrary integer lower bounds, not merely those
  concentrated in nonnegative degrees as in the natural-number resolution bundle.
- `I` is always the concrete termwise direct image
  `(comparisonLowerStar ... T).mapCochainComplexPlus.obj J`. Its type already
  records boundedness below. The first conclusion gives injectivity in every degree.
  The next conclusion is `QuasiIso (supportComparisonAugmentation ... h)`.
  The augmentation's definition is exactly `nu_*(h)` after the ordinary unit.
  These conclusions make it an etale injective resolution.
- The next conclusion supplies `θ : Q I ≅ Rnu_*(nu^* Q(F[0]))` and imposes
  `θ.hom ≫ R(Qh) = alpha_J`, with `alpha_J` the actual
  `rightDerivedFunctorPlusUnit.app` on the homotopy class of `J`.
  The factorization in `supportComparisonDerivedResolutionMap` identifies
  `nu^* Q(F[0])` with `Q(nu^* F[0])`. Since localization inverts `h`, `R(Qh)`
  is invertible. This equation therefore uniquely specifies
  `θ = alpha_J ≫ R(Qh)⁻¹`, the canonical injective computation; it does not
  permit an arbitrary isomorphism. The second equation is
  `Q.map a ≫ θ.hom = (derivedComparisonAdjunctionPlus ... T).unit.app (Q(F[0]))`.
  This is precisely the specified augmentation/derived-unit compatibility.
- For every `W : T.Etale`, evaluation through the existing `sheafSections` functor
  gives an equality of the two `ℤ`-indexed complexes of `A`-modules.
  Equality of complexes includes all their differentials, not just their terms.
- For every `f : W₁ ⟶ W₂` and integer degree, the following conjunct identifies
  the restriction of `I` with the restriction of `J` along `(Scheme.toProEt T).map f`.
  Thus the evaluation identifications are compatible with every site restriction.
- For every closed immersion `i : C ⟶ T`, `Etale.supportRestrictionArrow i` uses
  exactly the complementary open immersion `i.openComplement.ι`. The support
  conjunct is literal equality between the complexes obtained by applying
  `Sheaf.supportedSectionsFunctor` on the etale side and `ProEtale.supportSections`
  on the pro-etale side. These are the recorded kernel-of-restriction constructions.
  Their equality includes the kernels in all degrees and their differentials.
  The final conjunct states equality of the corresponding `kernel.ι` maps in each
  degree. The preceding all-arrow restriction clause includes the same support
  restriction arrows. No alternative kernel model is chosen.
- There is no constructibility, freeness, local constancy, finite generation,
  smoothness or nonemptiness hypothesis on `F` or `T`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the standard fixed-ring
  sheaf presentation of `Etale.DerivedCategoryModule`, `DerivedCategory.Plus` and
  localization. The unused torsion predicate is not imposed on `F`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`,
  `finiteCoefficientEtaleRealization` and `finiteCoefficientRealization`; these
  establish the constant-ring interpretation of the fixed-ring presentation.
- `def-weil-size-convention`: the recorded metatheoretic convention, implemented
  by explicit `universe u` and the common `u + 1` module universe.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparisonModules`, with the existing `comparisonUpperStar`
  and `comparisonLowerStar` of
  `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and `.Resolution`:
  `Injective` and the resolution interpretation; the theorem uses the equivalent
  unbundled integer-indexed `Plus`/`QuasiIso` conditions so it quantifies over
  all bounded-below resolutions as requested.
- `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`:
  `Functor.rightDerivedFunctorPlus`, `rightDerivedFunctorPlusUnit`, and the
  canonical injective computation from `.DerivabilityStructureInjectives`.
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`:
  `isIso_compactSupportComparisonUnit` and the specified
  `derivedComparisonAdjunctionPlus` of the upstream finite-coefficient comparison.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` for the canonical
  open complement appearing in the support restriction arrow.
- `Sheaf.AlgebraicGeometry.SupportCohomology`: `Sheaf.supportedSectionsFunctor`,
  `Etale.supportRestrictionArrow`, `ProEtale.supportRestrictionArrow`, and
  `ProEtale.supportSections`.

The proof imports also retain the recorded Grothendieck module theorem,
comparison-pullback exactness theorem, right-adjoint preservation of injectives,
and `comparisonUnitInjectiveModel`. The last theorem is in the canonically
realized coefficient presentation; its normalized-unit calculation is transported
through that equivalence, or equivalently obtained from its cited generic
`Adjunction.derivedPlus_unit_app_fac` and
`derivedAdjunctionPlus_eq_derivedPlus` in the fixed-ring presentation.
No dependency statement is replaced by a private copy.

Edge cases checked mathematically before writing and on the final signature:
`F = 0`; empty `T`; the zero ring; a nonfield finite ring such as `Z/4`;
empty closed support (the complement is all of `T`); full support (empty open
complement); and resolutions with negative nonzero injective terms but exact
negative cohomology. None is excluded by a binder or instance. The theorem uses
all integer degrees and no assumption that the coefficient ring is a field.

Searches made with the prescribed search wrapper:

- LeanFinder, query `Etale proetale common injective resolution comparison unit
  sections kernels`: eight generic hits, including `InjectiveResolution.kernelFork`,
  resolution comparison morphisms and natural-number resolution lemmas; none
  states this site-specific theorem or its normalization and literal section clauses.
- Loogle, query `InjectiveResolution, Adjunction`: the service returned zero hits
  and reported an unknown identifier. This was not used as positive evidence.
- LeanSearch, query `A common injective resolution on the etale and proetale sites
  computing the comparison adjunction unit and equal support kernels`: eight hits,
  including `InjectiveResolution`, its existence instance, `.of`, `.self`, and a
  generic comonadicity unit formula; no exact match.
- Mathlib grep, query `comparisonLowerStar|commonInjective|common_injective` in
  `CategoryTheory`: zero hits. Direct source reading finds the generic `Plus`
  injective-existence theorem and canonical right-derived functor definitions,
  which are imported rather than restated.
- Project ripgrep in both `lean/WeilConjectures` and `lean/Sheaf` for the item id
  and `commonInjective|common_injective`: no existing declaration of this node.
  Separate searches for all four proposed declaration names and in the upstream
  name index found no collisions. Reading comparison, support and finite-coefficient
  modules located the canonical constructions used above.

Source checked: `literature/stacks-project/proetale.tex`, labels
`lemma-relative-comparison` (Tag 099V), statement and proof, and
`lemma-compare-derived` (Tag 09B1), statement and proof. Both give the comparison
on all bounded-below objects without hypotheses on the individual sheaves.
The common injective model is the refinement already specified in this node.
There is no statement correction and no disputed statement.

Validation: the prescribed server compiler checked both the sandbox module and its
library name. The initial elaboration exposed three line-break parser errors, which
were repaired; the following run typechecked and exposed only three long-line warnings,
which were shortened. Final compile and delivery preflight results are recorded below.

Final validation: `scompile.py` passed without warnings for both the sandbox module
(23.6 seconds) and its library module name (28.5 seconds). The required
`deliver2.py --no-push` then printed `OK (dry run)` for commit `bbd0e6d5ddd`:
preflight and the per-file compilation both pass. The node differs from its base
only in `lean`; its theorem signature is verbatim from the source. Maximum line
length is 96 characters, and the only postponed proof is the owning node's theorem.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
