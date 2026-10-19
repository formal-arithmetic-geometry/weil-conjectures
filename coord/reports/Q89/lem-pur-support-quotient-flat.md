## Worker report

The module `Sheaf.AlgebraicGeometry.SupportQuotientFlat` states
`AlgebraicGeometry.Scheme.supportQuotient_flat_kflat_stalk_comparison` with `sorry`.
Its seven auxiliary definitions construct the two defining arrows, their actual
cokernels and quotient maps, and the canonical constant-section comparison map.
There is no postponed construction data and no auxiliary postponed theorem.

Q55's previously merged delivery was a stage-1 split, recorded in `reviewed`.
The assigned node has no `lean` record and no `reviewed_lean`; the previous worker's
stale-assignment conclusion confused the two stages. This delivery formalizes that
reviewed split without splitting it again or changing its natural statement.

Hypothesis and clause correspondence:

* A finite commutative ring is `(A : Type u) [CommRing A] [Finite A]`.
  Coefficients are `ULift.{u + 1, u} A`, canonically the same ring in the site
  coefficient universe. The coefficient module universe is `u+1`, the original
  sites have object universe `u+1` and morphism universe `u`; no equality of those
  universes is imposed. Finite rings and their zero ring are included.
* The scheme and closed immersion are `{C T : Scheme.{u}} (a : C ⟶ T)
  [IsClosedImmersion a]`. Its actual open complement is `a.openComplement`, with
  immersion `a.openComplement.ι`. The sole additional geometric hypothesis in the
  node is `[QuasiCompact a.openComplement.ι]`. No Noetherianity, separation, base
  field, smoothness, or finite-type hypothesis is added.
* The two ordinary sites are `T.smallEtaleTopology` and `ProEt.topology T`.
  Module-valued sheaves present ordinary modules over the constant ring sheaf.
  They are converted to the recorded intrinsic module categories by
  `etaleSumFlatModuleRealization T (ULift A)` and
  `ProEtale.finiteCoefficientIntrinsicRealization T A`. These are the published
  constant-scalar realization functors, not an arbitrary equivalence or action.
  The latter is already publicly supplied through the recorded
  `ProEtaleIntrinsicExtensionByZero` dependency. The landed
  `lem-pur-etale-sum-flat-kflat` is added to `stmt_deps` for its former interface.
* `etaleSupportQuotientArrow` and `proEtaleSupportQuotientArrow` are the existing
  extension-by-zero adjunction counits evaluated at the constant regular module.
  Their sources are `j_! j^* A_T`; the canonical restriction identification
  `j^* A_T = A_U` identifies these sources with the node's `j_! A_U`.
  The counit is the transpose of identity, hence on the unique open-object
  generator it is one. This is precisely the inclusion-of-open-object arrow
  in the node, without choosing an arbitrary map.
* `etaleSupportQuotient` and `proEtaleSupportQuotient` are `cokernel` of those
  arrows. The maps `etaleSupportQuotientMap` and `proEtaleSupportQuotientMap`
  are literally `cokernel.π`, so these are Q and r of the node.
* The first two conjuncts are `SheafOfModules.IsFlatOnSite` of those two
  quotients under their canonical coefficient realizations. This is the recorded
  exact sheaf tensor functor condition, hence preservation of short exact sequences.
* The next two conjuncts are `CochainComplex.IsKFlatIndependentCoefficients` of
  `(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj` of each realized
  quotient. Thus the complexes have exactly Q in degree zero; their tensor tests
  are arbitrary unbounded integer complexes, with the recorded signed direct-sum
  total tensor. No bounded-below derived category replaces the stated unbounded one.
* Geometric points are all `(Ω : Type u) [Field Ω] [IsSepClosed Ω]
  (t : Spec (.of Ω) ⟶ T)`. Membership of their unique underlying point in C is
  `t (IsLocalRing.closedPoint Ω) ∈ Set.range a`. On C the statement supplies a
  module isomorphism from `(pointSmallEtale t).sheafFiber.obj Q` to `ULift A`.
  Its normalization composes the constant-presheaf sheafification unit at the
  final object, its actual germ map `toPresheafFiber`, the stalk of `cokernel.π`,
  and this isomorphism, and asserts the identity of the regular A-module.
  In particular the quotient of constant one maps to one, and the isomorphism
  is canonical. Off C the last stalk clause is `IsZero` of that module stalk.
* `supportQuotientConstantComparison` is the comparison adjunction transpose of
  the map extending the constant pro-etale scalar sections. The final conjunct
  supplies a unique isomorphism `ν^* Q_et ≅ Q_proet` whose composite with
  `ν^* r_et` is this exact constant comparison followed by `r_proet`.
  This is exactly the node's normalized canonical comparison, with the coefficient
  identification made explicit rather than comparing arrows with different sources.

Dependency declarations used (their signatures and source docstrings were read):

* `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`,
  `constantSheafAdj`, `toSheafify`.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules`, inherited by the intrinsic realizations.
* `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and `Scheme.Etale`.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `Scheme.ProEt.topology`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, the ordinary localization convention; no derived object
  is needed merely to express flatness/K-flatness of this degree-zero complex.
* `Mathlib.AlgebraicGeometry.Scheme`: `Scheme` and its morphisms.
* `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: the imported `QuasiCompact`.
* `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `Etale.openImmersionLowerShriek` and `Etale.openImmersionLowerShriekAdjunction`.
* `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `Scheme.sfIntrinsicExtensionByZero` and `Scheme.sfIntrinsicModuleEquivalence`;
  its recorded functor is the transport of the same fixed-scalar
  `ProEtale.openImmersionLowerShriek` used in the actual counit here.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`:
  the recorded `siteSheafTensorRightMap` interface publicly retains the
  independent-universe `siteSheafTensorRight` used by flatness.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
* `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlatIndependentCoefficients`.
* `Mathlib.CategoryTheory.Sites.Point.Basic`: `Point.sheafFiber` and its germ map;
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint`: `Scheme.pointSmallEtale`.
* `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparisonModules`, the exact fixed-coefficient
  `ProEtale.comparisonAdjunction` / `comparisonUpperStar` used here.
* `Sheaf.AlgebraicGeometry.EtaleSumFlatKFlat`: `Scheme.etaleSumFlatModuleRealization`.
* `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`:
  `ProEtale.finiteCoefficientIntrinsicRealization`, publicly imported by the
  recorded intrinsic extension-by-zero module.

All proof dependencies with recorded modules are imported non-publicly unless
already required publicly by the statement. In particular these include bounded
flat K-flatness, open-closed flatness, both open-closed sequences, finite stalks,
constant stalks, inverse-image exactness, and comparison exactness.
`lem-weil-pbc-closed-immersion-finite` and
`lem-weil-pbc-free-yoneda-presheaf-module` have no recorded Lean module to import;
they remain explicit references in the theorem's complete proof docstring.
There are no new nodes, dependency repairs, statement corrections, or disputes.

Edge cases checked before writing: C empty gives the cokernel of the identity,
hence Q=0 and every geometric stalk zero. C=T gives empty open complement,
hence Q=A_T and quotient map identity. Empty T has no geometric points and
only the zero sheaf; the universally quantified stalk assertion is correctly
vacuous there. The zero coefficient ring is permitted: the regular coefficient
module and both quotients are zero, and the normalized one is also zero.
Disconnected T and nonreduced closed subschemes are included: the stalk criterion
uses precisely the underlying closed image. No pro-etale geometric-stalk
conservativity is assumed. Degree zero uses `ComplexShape.up ℤ`, not the natural
number single-complex convenience abbreviation.

Searches for existing declarations:

* `msearch.py ... leanfinder "The cokernel of extension by zero of the constant ring
  sheaf on an open complement is flat and K-flat"`: eight hits, all generic
  `SheafOfModules.relationsOfIsCokernelFree` / presentation / generator declarations;
  none states this geometric quotient result.
* `msearch.py ... loogle "SheafOfModules, cokernel, Flat"`: zero hits; reports
  unknown identifier `cokernel` in that query.
* `msearch.py ... grep "supportQuotient|SupportQuotient|[Kk][Ff]lat" CategoryTheory`:
  zero hits.
* `msearch.py ... leansearch "The quotient of a constant module sheaf by extension
  by zero of an open complement is tensor flat"`: eight generic algebraic
  module-flatness hits, including `Module.Flat.rTensor_exact` and
  `Module.Flat.iff_rTensor_exact`; none is the sheaf quotient theorem.
* `rg` for `supportQuotient|SupportQuotient|support_quotient|quotient.*[Ff]lat`
  in the upstream WeilConjectures and shared lean/Sheaf trees: no matching
  declaration of this statement. Broader searches found
  `Etale.supportedCoefficients` and `ProEtale.supportedCoefficients`, read in full:
  these are direct images of constants from the closed scheme, rather than
  the actual cokernels. Their exactness in coefficient modules does not itself
  assert intrinsic tensor flatness, degree-zero K-flatness, the stalk-generator
  normalization, and quotient-normalized comparison. Thus this is not an exact
  existing match, and their different direct-image construction is not copied.
* `rg` for `supportQuotient|SupportQuotient|closed.support.*flat` in Mathlib's
  Algebra/Category/ModuleCat, the upstream AlgebraicGeometry tree, and shared
  lean/Sheaf/AlgebraicGeometry: only an explanatory supported-product docstring.
* `grep -rn "lem-pur-support-quotient-flat"` in the upstream WeilConjectures:
  no hit. Existing coefficient-realization APIs were located by `rg` and reused.

Validation: the final file compiled cleanly through the prescribed
`scompile.py Q89 lem-pur-support-quotient-flat .../SupportQuotientFlat.lean`,
both sandbox and library-mode checks (6.9 and 6.8 seconds), with no errors or
unexpected warnings. The expected theorem proof is `sorry` throughout stage 2.

## Second reading by Q89

Author's second reading, not the maintainer's independent review: reopened the
node and the final module. Matched the finite commutative coefficients, ordinary
sites and modules, closed immersion, and quasi-compact complement to their exact
binders; checked that neither IsLocallyNoetherian nor a field hypothesis is present.
Unfolded the two quotient definitions: both are actual cokernels of the existing
open-extension counits, and both r maps are literally the same cokernel projections.
Read the source docstrings of the recorded intrinsic extension and both realization
interfaces to check the scalar actions agree with the node. The four leading
conjuncts use the recorded flat and K-flat predicates on those actual objects.
Checked the two geometric membership cases, the specified constant germ followed
by the actual quotient map, and the final comparison identity including its
otherwise implicit coefficient identification.

Corrected during this reading: the natural-number `CochainComplex.single₀`
abbreviation was replaced by the integer-indexed `HomologicalComplex.single`;
the stalk normalization now writes the actual constant germ composite explicitly,
so it asserts the required generator normalization without an unnecessary
filtered-colimit preservation instance in a smaller indexing universe. Removed
an unused argument from the canonical constant comparison application.
No mathematical hypothesis or conclusion changed. Final review found no mismatch.
