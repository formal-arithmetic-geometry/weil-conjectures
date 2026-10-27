## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleCompactificationBoundedModels` states
`AlgebraicGeometry.Etale.etaleCompactification_bounded_models`, with one `sorry` proof.
Its helper `etaleCompactificationAcyclicComparison` constructs the actual canonical arrow
from the existing right-derived unit and the inverse exact-functor localization comparison.
It contains no postponed data or proof. Both declarations belong to this item's notion;
there is no new independent definition node, dependency repair, or statement correction.

Hypothesis and clause correspondence:

- The schemes are `U V : Scheme.{u}`. `Etale e`, `IsSeparated e`, and `QuasiCompact e`
  render separated etale finite type: the existing etale instance already supplies
  `LocallyOfFiniteType e`. No extra finite-presentation hypothesis is imposed.
- `IsLocallyNoetherian U`, `CompactSpace U`, and the corresponding V instances render
  exactly Noetherian schemes with finite affine covers. Mathlib's
  `isNoetherian_iff_of_finite_iSup_eq_top` identifies this with the stated cover condition.
- `c : Compactification e` supplies W=`c.Z`, j=`c.i`, r=`c.g`, an open immersion,
  properness, and the equation `e = c.i ≫ c.g`. No Noetherian hypothesis on W is assumed.
- `R : Type (u+1)`, `CommRing R`, `Finite R` is an arbitrary finite commutative ring
  in the recorded six-functor coefficient universe. Smaller rings admit their usual lift;
  no universe equality or new site convention is imposed.
- `N : EtaleCompactSupportNormalization R` names the prescribed normalization in the
  node, already supplied by the dependency theorem `nonempty_etaleCompactSupportNormalization`.
  The conclusion holds for every such normalization; no new comparison compatibility is
  assumed. Its `sheaf_normalization` and `derived_normalization` fields pin the actual maps.
- K is `CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u+1} R)) ℤ`.
  The hypothesis `∀ n, n < a ∨ b < n → IsZero (K.X n)` is precisely support in [a,b].
  No flatness or injectivity is a hypothesis on this K.
- The first conclusion is `IsNoetherian c.Z`.
- The positive higher-direct-image clause is
  `∀ (n : ℤ) (q : ℕ), 0 < q → IsZero ((rStar.rightDerived q).obj (jShriek.obj (K.X n)))`.
  Positive natural degrees enumerate precisely all positive integer cohomological degrees;
  `rightDerived` is the usual right-derived functor on single sheaves, identified by the
  recorded single-object comparison. This uses actual module sheaves, not their sections.
- `IsIso (etaleCompactificationAcyclicComparison R c K)` states the canonical
  acyclic-complex comparison is an isomorphism in the derived category.
- `nu` is a natural isomorphism `jShriek ⋙ rStar ≅ eSum`. The equation
  `nu.inv = N.sheafComparison e c` forces exactly the inverse of the prescribed graph
  sheaf comparison, hence the proper-support-to-sheet-components degree-zero comparison;
  it is not a freely chosen isomorphism. In degree zero the derived unit is the identity
  by left exactness, as explained in the node proof and theorem docstring.
- `NatIso.mapHomologicalComplex nu (.up ℤ)` is the chain isomorphism nu_K. By the
  existing definition its degree-n hom component is literally `nu.hom.app (K.X n)`;
  differential compatibility and naturality in chain maps are part of the natural
  transformation and chain-map types, with no separate assumed chain compatibility.
- The displayed equality is alpha_K followed by `N.comparison e c` followed by the
  canonical exact-sum localization comparison, equal to `DerivedCategory.Q.map` of
  that actual chain-isomorphism hom. The last localization factor identifies
  D(eSum)(Q K) with Q(eSum K). This is exactly c_K alpha_K = Q(nu_K), with all
  changes of representation specified. It asserts equality of derived arrows, not
  merely equality on individual cohomology sheaves.
- Naturality of alpha is written explicitly for every `phi : K ⟶ L`, even if L is
  unbounded. Naturality of c is intrinsic to `N.comparison e c`, a natural isomorphism;
  naturality of nu_K is intrinsic to `NatIso.mapHomologicalComplex nu`.
- The three `IsZero` conjuncts for every n outside [a,b] give the same degree interval
  for the actual degreewise j_!K, r_*j_!K, and eSum K, not replacement resolutions.
- Only the final implication assumes `∀ n, exactFunctor _ _ (tensorRight (K.X n))`.
  This is exactly the recorded flat-sheaf node's exposed exactness predicate, on the
  ordinary ModuleCat-valued sheaf encoding. Its conclusion states the same predicate
  for each of the three image terms, then `(HomologicalComplex.quasiIso _ (.up ℤ)).kFlat`
  for K and all three image complexes. This is the K-flat predicate explicitly exposed
  by the recorded K-flat node for this encoding; it is equivalent to total tensor
  preserving acyclicity. There is no flatness assumption on any preceding clause.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, in the affine-cover
  interpretation of `IsLocallyNoetherian`/`IsNoetherian` from
  `Mathlib.AlgebraicGeometry.Noetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, `IsSeparated`.
- `WeilConjectures.Compactification.RefinementCategory`, publicly importing
  `WeilConjectures.Compactification.Defs`: `Compactification`, with Z, i, g, comm,
  isOpenImmersion, isProper; the recorded refinement notion is not duplicated.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the recorded ordinary etale
  sheaf encoding `CategoryTheory.Sheaf` (the relevant node note explicitly permits
  the ModuleCat encoding used by six functors).
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its public coefficient
  dependency: `DerivedCategoryModule`/`DerivedCategory`, `DerivedCategory.Q`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`; its ordinary right-derived functor supplies r_*.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`:
  `AlgebraicGeometry.Etale.etaleLowerShriek`.
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization`:
  `EtaleCompactSupportNormalization` and the existence theorem; its full structure,
  including the graph normalization and homotopy representative formula, was read.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `CategoryTheory.exactFunctor` exposed in the recorded lean.declarations and note;
  `IsFlatOnSite` itself takes the different ringed-site encoding, so is not misapplied.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  its exposed `CategoryTheory.MorphismProperty.kFlat`, specialized to quasi-isomorphisms;
  the independent ringed-site predicate is not duplicated or misapplied.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`:
  `Functor.rightDerivedFunctorUnitQ`, with the exact source and target needed here.
  `Functor.mapDerivedCategoryFactors` is the existing exact-functor factorization.
  `NatIso.mapHomologicalComplex` gives the existing degreewise chain isomorphism.

The module also imports the recorded, stated proof dependencies as non-public imports:
`RightDerivedFunctor.PlusSingle`, `EtaleModuleEnoughInjectives`,
`EtaleInverseImageModulesExact`, `EtaleCompactSupportGraphDerivedIso`,
`LowerShriek.EtaleMapProjection`, and `BoundedFlatIndependentCoefficients`.
The graph-comparison definition is publicly available through the normalization module.
The finite-type-over-Noetherian node is a Mathlib leaf, not missing Lean data; its matches
`LocallyOfFiniteType.isLocallyNoetherian` and `QuasiCompact.compactSpace_of_compactSpace`
were read. No proof-import cycle was introduced.

Edge cases checked before writing: U empty (all source sheaves zero), zero coefficient
ring (all module objects zero), zero complex, a>b (the support condition forces all
terms zero), arbitrary negative a and b, q=0 (correctly excluded from positive vanishing),
identity e, and an open immersion. The theorem does not impose a≤b, nonemptiness,
positive characteristic, nonzero R, finite Tor dimension, or field coefficients. In
particular Z/4 is allowed; flatness is conditional, not presumed for all its modules.
No node fault or STATEMENT-DISPUTED issue was found.

Searches for the same statement or definitions:

- `msearch.py ... leanfinder "Etale compactification bounded flat complexes acyclic
  proper direct image canonical comparison"`: 8 hits, all scheme etaleness or affine
  limit results; no compactification bounded-model theorem.
- `msearch.py ... loogle '"IsKFlat", "rightDerivedFunctorUnit"'`: 0 hits.
- `msearch.py ... grep 'compactification.*[Kk][Ff]lat|[Ee]tale.*[Aa]cyclic'`: 0 hits.
- `msearch.py ... leansearch "A bounded complex of flat etale sheaves is K-flat and
  exact sum extension computes compactly supported direct image"`: 8 hits, ordinary
  module flatness/tensor exactness and derived-category support; no exact statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for compactification/boundedness,
  acyclicity, exactFunctor, kFlat, and the proposed declaration names: existing
  normalization, flat-complex and K-flat tools found and reused; no duplicate theorem.
- `rg -n 'lem-sp-etale-compactification-bounded-models' lean/WeilConjectures`: no hit.
- Source read: `literature/stacks-project/more-etale.tex`,
  `remark-Rf-lower-shriek-change-of-rings` (Tag 0GL6), plus the node's complete seven-step
  bounded-model argument and the full normalization/graph comparison interfaces.

Validation: the required `scompile.py` compiled the module as both sandbox and library
with no errors or warnings (17.1 s and 30.7 s). The first elaboration check found the
namespace spelling `nu.mapHomologicalComplex` invalid; it was corrected to the actual
existing API `NatIso.mapHomologicalComplex nu`, then both checks passed. Every universe
and variable is explicitly bound (`set_option autoImplicit false`). Lines are ≤100
characters. The sole postponed theorem is the main declaration and its docstring
carries all seven proof steps. Independent review is performed by the maintainer as
specified in this dispatched worker's brief.

## Second reading by Q07

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
