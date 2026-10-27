## Worker report

The module `Sheaf.Paper.RationalContinuousCoefficientDerivedLocalization` states
`CategoryTheory.rationalContinuousCoefficient_derivedLocalization` with `sorry`.
Its fully written assertion predicate is `ContinuousScalarLocalizationAssertions`;
`continuousCoefficientRestrictLinear` supplies real restriction-of-scalars data for
the raw category. No functor is replaced by an arbitrary tensor-like functor.
The prescribed ordinary and derived universal pair is a parameter `d` of the recorded
`SheafOfModules.DerivedChangeOfRingsCochainModel` type: this ranges over universal
pairs of the actual extension, rather than assuming any desired conclusion.

Hypothesis-by-hypothesis and clause-by-clause reading:

- Prime ell: `(l : ℕ) [Fact l.Prime]`; finite coefficient extension:
  `(E : Type v) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
  The integer ring and chosen uniformizer are exactly
  `Padic.coefficientExtensionIntegers l E` and `Padic.coefficientExtensionUniformizer l E`.
- Small site: `{C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]`
  and `{J : GrothendieckTopology C}`; sheafification and sheaf-compose instances
  express the node's size/existence conventions. The two localization universes
  `wR` and `wS` remain independent, as do `uC`, `vC`, `u`, `v`.
- Ring sheaf and constant coefficient map: `R : Sheaf J CommRingCat.{u}` and
  `a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)`.
  This is the equivalent adjoint description of a map out of the constant sheaf:
  a compatible global family of ring maps, with the exact section action.
- S is `ringedLocalizationRingOfUniverses R (a t)` and its map is
  `ringedLocalizationRingUnitOfUniverses R (a t)`, the actual sheafified
  sectionwise localization. `MR` and `MS` in the predicate are the recorded
  `ringedSiteModules` abbreviation for Mathlib `SheafOfModules`.
- D(R), D(S), all cohomology and all shifts use Mathlib `DerivedCategory`, its
  `homologyFunctor`, and its triangulation. The two `HasDerivedCategory` binders
  allow any chosen localization size, without forcing their Hom universes equal.
- The E=A[1/t] identification is an algebra isomorphism `eE`. Because it is an
  A-algebra isomorphism, it fixes the specified map A→E; the localization universal
  property determines it uniquely. This uses the already landed
  `lem-weil-l-adic-integers-localization-uniformizer`, added to `stmt_deps`.
  The E-action on D(S) is explicitly the localized coefficient section map composed
  with `eE.symm`; the raw E-action is restriction of its localized tensor action
  through the same inverse. It is not an arbitrary `Linear E` binder.
- The ordinary functor is `d.E`; the existing model's `obj_eq` and `map_eq` fix
  it to `SheafOfModules.changeOfRings` and `changeOfRingsHom` (the ordinary tensor
  extension, the usual symmetry identifies either tensor order). `d.additive`
  is in the model; `∃ hl : PreservesFiniteLimits d.E` and
  `∃ hc : PreservesFiniteColimits d.E` assert exactness. `d.E.Linear A` specifies
  the section-action linearity.
- F is the existing model's `d.T`, with its universal counit `d.ε` and its K-flat
  computation `d.computes`. The assertion supplies its `CommShift`, triangulated
  property, A-linearity, and `e : d.T ≅ d.E.mapDerivedCategory`.
  `NatTrans.CommShift e.hom ℤ` gives comparison as triangulated functors.
- For every complex K, `e.hom.app (Q.obj K) ≫ mapDerivedCategoryFactors.hom.app K =
  d.ε.app K` fixes the comparison to the universal counit. For every K-flat P
  and quasi-isomorphism p:P→K the following displayed equality identifies its
  representative with `Q.map (T.map p)`. By the model's `computes`, the counit
  on P is invertible; Q(p) is invertible too. Thus this is precisely the stated
  K-flat resolution formula, with no restriction on the choice of resolution.
- The degree-zero iso `e0` is fixed to whiskering e followed by
  `mapDerivedCategorySingleFunctor 0`, not just existence of an unrelated iso.
- For every r, the natural iso `h r` is fixed to whiskering e and the inverse
  of `mapDerivedCategoryHomologyFunctorIso r`. The latter is the existing
  localization descent of the cycle/boundary comparison, as its definition shows.
  This is natural on *all derived arrows*, since these are natural isomorphisms
  of functors on the derived category.
- Vanishing: for any `I : Set ℤ`, zero cohomology in every degree in I implies
  zero cohomology of FK in I. In particular this covers every requested interval,
  including empty and unbounded intervals.
- Any full triangulated subcategory: `∀ P : ObjectProperty (DerivedCategory MR),
  [P.IsTriangulated]`. `P.FullSubcategory` has the inherited A-linearity;
  Mathlib's predicate does not require closure under ambient isomorphisms.
  No constructibility, boundedness, or finiteness predicate occurs.
- Raw source: exactly `ScalarLocalization A P.FullSubcategory t`, with its tensor
  Homs and its existing `localization` functor. Existential structures supply its
  induced shift; the equality for every n fixes the shift to `ScalarLocalization.map`.
  The `HEq` specifies the identity Q shift comparison. The triangle iff fixes
  distinguished triangles to precisely isomorphic images of integral triangles;
  `IsTriangulated` and Q exactness are included.
- Descended functor: `G` with `hobj : ∀ K, G.obj K = d.T.obj (P.ι.obj K.obj)` fixes
  its object map. For every tensor `b ⊗ₜ[A] f`, its arrow is the prescribed
  `eE b • F(f)`, conjugated only by `hobj` equalities. Taking b=t^(-n) gives
  the requested fraction formula, while all b states the full E-scalar formula.
- Raw representative independence is explicit for every n,m,k: from
  `t^k • (t^m • f - t^n • g) = 0` the two denominator-scaled F-images agree.
  A genuine functor supplies identity and composition laws; `G.Additive` supplies
  addition preservation, `G.Linear E` preservation of every coefficient scalar.
- `Nonempty (Q ⋙ G ≅ P.ι ⋙ d.T)` states factorization. The `CommShift` on G is
  natural on every raw morphism by its type; the `HEq` components are those of
  `P.ι ⋙ d.T`. `G.IsTriangulated` carries every integral image and every triangle
  isomorphic to one to a distinguished triangle, including the connecting arrow
  with this specified shift comparison.

Dependency interfaces read and used:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, retaining the ordinary tensor extension.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`,
  `HasDerivedCategory`; `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, `homologyFunctorFactors`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: its public coefficient
  constructions above; `Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer`:
  `Padic.coefficientExtension_localization_uniformizer` justifies eE.
- `Mathlib.CategoryTheory.Linear.LinearFunctor`: `Functor.Linear`;
  `Mathlib.CategoryTheory.Triangulated.Subcategory`:
  `ObjectProperty.IsTriangulated`, inherited inclusion and triangulation;
  `WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive`:
  `linear_shiftFunctor_fullSubcategory`.
- `Sheaf.CategoryTheory.ScalarLocalization`: `ScalarLocalization`, `localization`,
  `map`, `linear` and the actual tensor Hom category.
- `Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses`:
  `ringedLocalizationRingOfUniverses`, `ringedLocalizationRingUnitOfUniverses`.
- `Sheaf.CategoryTheory.ScalarLocalizationCoefficientActions` is retained publicly;
  the independent-universe interfaces are in the item module itself.
- `Sheaf.CategoryTheory.SiteCoveringAxioms` gives the site conventions;
  `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`.
- `Mathlib.CategoryTheory.Triangulated.Functor`: `Functor.IsTriangulated`;
  `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` publicly retains
  `SheafOfModules.DerivedChangeOfRingsCochainModel`, including its actual extension
  `E`, derived universal pair `T, ε`, and canonical K-flat counit.
- All recorded proof modules are imported (Mathlib localization/universal-property
  and exact/homology modules arrive through public statement imports). The proof
  docstring follows all eight DAG proof steps.

Sources read: Bhatt–Scholze 6.8.14(2) in the local PDF; Stacks derived.tex
lemma-right-derived-exact-functor (015F), proposition-construct-localization (05R6),
and homology.tex lemma-exact-functor (010N). No statement correction or dispute.

Edge cases checked before and while writing: empty site, zero R, nilpotent or zero
image of the uniformizer, all cohomology degrees (negative, zero, positive), zero
and unbounded complexes, denominator exponent 0, t-torsion in Hom, empty and
unbounded vanishing intervals, full subcategories not closed under ambient isos,
and separate site/coefficients/derived Hom universes. None is excluded by a hidden
nonzero-section, boundedness, faithful action, or enough-points hypothesis. An empty
full triangulated subcategory is already excluded by the definition of triangulated
subcategory (it contains a zero object), as in the source.

Searches for an existing statement or missing constructions:

- msearch LeanFinder: “Exact scalar localization of sheaves induces a derived
  triangulated functor with cohomology comparison and descends to linear fractions”.
  Eight hits, including `mapDerivedCategory` and `mapDerivedCategoryFactors`;
  no assembled sheaf localization / raw-fraction statement.
- msearch Loogle: `CategoryTheory.Functor.mapDerivedCategory,
  CategoryTheory.ScalarLocalization`: no hit; the latter is a project name.
- msearch LeanSearch: “exact localization sheaves derived categories fraction linear
  functor”: eight general derived/localization results; no full statement.
- msearch grep: `mapDerivedCategory.*[Hh]omology|homology.*mapDerivedCategory`
  in Mathlib Algebra/Homology: no result. Direct rg in the upstream extension found
  `mapDerivedCategoryHomologyFunctorIso`, reused for the canonical comparison.
- Direct rg on Mathlib CategoryTheory/Linear found no general compHom linear-category
  restriction helper; `Module.compHom` is reused for the small inline construction.
- Direct rg of upstream WeilConjectures and project Sheaf for
  `rational.continuous|derived.*[Ll]ocalization|[Ll]ocalization.*derived` found
  many derived-localization consumers, no full statement. Exact grep of the item's
  id in upstream WeilConjectures found none. More specific rg for the proposed main
  names and generalized coefficient helpers found no existing declarations.
- Direct inspection of the original coefficient-action module found `C : Type u`
  with `SmallCategory C` tied to its coefficient universe u; the new independent
  signatures are required to preserve the item's general-site size convention.

Validation of the returned packet: scompile.py compiled its two modules and the
initial saved-packet dry run passed. The repair consolidates them into one item
module; its fresh compile and dry run are recorded below. No direct Lean/lake build
was run.

## Returned delivery repair (H13)

The returned head c42d10ecf8f5 replaced the landed, proved, existing:true record of
`def-weil-pbc-scalar-localization-coefficient-actions`. This was incorrect. The
repair removes that dependency node copy from the packet, so its live record and
all six original declarations stay byte-identical. The live
`Sheaf.CategoryTheory.ScalarLocalizationCoefficientActions` module is imported.

The six independent-universe helpers are now in
`Sheaf.Paper.RationalContinuousCoefficientDerivedLocalization`, listed in the
item's `lean.declarations`: `scalarLocalizationSectionsMap_memOfUniverses`,
`scalarLocalizationSectionsMapOfUniverses`,
`scalarLocalizationCoefficientLinearOfUniverses`,
`scalarLocalizationDerivedLinearOfUniverses`,
`scalarLocalizationSections_isUnitOfUniverses`, and
`scalarLocalizationCoefficientMapOfUniverses` (all in `CategoryTheory`). Their
source/blueprint docstrings assign them to this item, as the return authorizes.
The two postponed helper theorems retain complete proof descriptions. The section
map, restriction action, induced derived action and unique localization lift have
exactly their previous data and independent universes. The separate helper module
and the dependency node replacement are no longer delivered. There are no new
nodes or dependency modules.

The main assertion and theorem signatures are unchanged. The uniformizer
localization theorem remains in `stmt_deps`; its conclusion is the canonical
A-algebra identification re-quantified as `eE`, as the independent review passed.

## Second reading by Q113

A second pass by the same worker (the dispatcher expressly forbids spawning an
independent worker) reopened the node and the consolidated item Lean file after
the H13 repair. The clause mapping in the Worker report still holds: the assertion
predicate and main theorem retain their binders, universal-pair parameter,
canonical comparison normalizations, cohomology/vanishing clauses, raw shifts and
triangles, and coefficient-linear fraction formula. The six moved declarations
have the same signatures and construction data; only their owning module and
blueprint docstrings changed. The extra universe `w` belongs to the generalized
derived-action helper; `wR` and `wS` in the item remain independent.

The live coefficient-action record and module were read again. Their six names,
proved declarations and existing:true record are retained through the unchanged
public import. The dependency node copy and separate helper module are absent
from the repaired packet. Every moved helper is registered in the item's
lean.declarations, and every postponed theorem has its source and proof docstring.
The item's lean.statement is now the multiline signature verbatim from the file.
The only changed DAG data outside the item lean is the previously accepted
addition of the landed uniformizer-localization node to stmt_deps. No statement
correction or dispute is introduced by this repair. The maintainer performs the
independent review after delivery, as specified by the brief.

Repair validation: scompile.py compiled the consolidated file in both sandbox
(13.4 s) and library module modes (12.2 s), exit 0 with no errors or warnings.
The self-check verified one module and one node, all nine declarations registered,
three whole-proof sorry theorems, every declaration assigned to this blueprint,
all Lean lines at most 100 characters, and a verbatim multiline main signature.
The mathematical node statement and the dependency record are unchanged.
