## Worker report

`Sheaf.AlgebraicGeometry.InjectiveComplexSliceSectionModel` states
`CategoryTheory.injectiveComplexSliceSectionModel`. Its only postponed theorem is
this node's theorem. The other declarations construct actual functors, natural
transformations, and their structural instances; they are recorded in
`lean.declarations` and have source/blueprint docstrings. No data is chosen from an
existence theorem with an undetermined object.

The retained packet's dry run failed because its recorded signature included `:=`,
which the signature checker excludes. Self-review also found that its structure
had arbitrary section objects and bare `Prop` fields instead of assertions of the
source's clauses. That structure has been removed. Every clause is now a concrete
proposition about canonical constructions; the old report's claim of exactness
for the placeholder structure was incorrect. The natural-language node statement
has not changed. The existing landed node
`def-weil-pbc-ringed-derived-restriction` was added to `stmt_deps`, because its
recorded exact general-site interface is used directly.

Hypothesis and object correspondence:

- The small site is `C : Type u`, `[SmallCategory C]`, with topology
  `J : GrothendieckTopology C`. This is the node's small site in its fixed
  coefficient universe, after the skeleton of `def-weil-size-convention`.
- The unital, possibly noncommutative coefficient ring is `Λ : Type u` with
  `[Ring Λ]`. Its constant sheaf is literally
  `(constantSheaf J RingCat.{u}).obj (RingCat.of Λ)`. The transparent abbreviation
  `constantModuleSheaves J Λ` is `SheafOfModules.{u}` of that ring sheaf.
- `HasWeakSheafify`, `HasSheafify`, and `WEqualsLocallyBijective` encode the existing
  sheafification and abelian-category constructions. `HasDerivedCategory.{w}`
  selects the localizations for modules on the site, all its slices, and coefficient
  modules in a common chosen derived-category universe. These are construction
  instances on small sites, not exactness, injectivity, comparison, or vanishing
  hypotheses. The ring sheafification instance on each slice lets the theorem state
  the constant-ring restriction identification, with its unit normalization.
- `L : CochainComplex.Plus (constantModuleSheaves J Λ)` packages exactly a cochain
  complex and an integer lower bound: `CochainComplex.plus` means
  `∃ n : ℤ, L.obj.IsStrictlyGE n`. `hInjective` quantifies over every integer term.
- `K : DerivedCategory.Plus (constantModuleSheaves J Λ)` packages membership in
  D-plus. `e : DerivedCategory.Plus.Q.obj L ≅ K` is the specified derived
  identification. Using the full subcategories retains arbitrary representatives
  and identifications, including changes of `e`.

Clause correspondence, in the order of the theorem's conclusion:

1. The first conjunction supplies, for every `W`, the isomorphism from the
   restricted constant ring sheaf to the constant ring sheaf of the slice. Its
   equality with `constantCoefficientMap (J.over W) Λ` fixes the scalar map on
   the constant presheaf, rather than selecting an arbitrary ring isomorphism.
2. The next conjunction asserts `PreservesFiniteLimits`,
   `PreservesFiniteColimits`, and `Injective (M.over W)` for every injective module
   sheaf `M`. The functor is exactly `SheafOfModules.overFunctor`.
3. `coefficientSectionPresheaf` restricts scalars along the canonical ring
   sheafification unit by Mathlib's `PresheafOfModules.restrictScalars`; its maps
   are the underlying sheaf restriction maps. `constantModuleEvaluation` evaluates
   this presheaf. `constantModuleSectionDiagram` applies this evaluation degreewise
   with `mapHomologicalComplex`: its differential is literally evaluation of
   `L.obj.d`, and its arrows are literally the degreewise restrictions.
4. `constantModuleDerivedSections` is Mathlib's `rightDerivedFunctorPlus` of this
   evaluation. `constantModuleSliceEvaluation` evaluates the actual restricted
   ringed site at `op (Over.mk (𝟙 W))`, using the same constant scalar map restricted
   along `Over.forget W`. `constantModuleSliceDerivedSections` derives that
   terminal evaluation. `constantModuleSliceRestriction` is the exact module
   restriction's `mapDerivedCategoryPlus`.
5. The family `beta` identifies object evaluation's right derived functor with
   actual derived sections after slice restriction. The first condition after
   `beta` fixes its comparison on every bounded-below complex by the right-derived
   units and `mapDerivedCategoryPlusFactorsh`. This removes arbitrary choices of
   comparison. `constantModuleSectionComparison` is the right-derived unit at
   `L` followed by the derived image of the chosen `e`. The next condition asserts
   `IsIso` of this map followed by `beta`. Thus the source and target are exactly
   Q of the literal section complex and derived sections of `K` on the slice.
6. `constantModuleDerivedRestriction` is constructed with
   `Functor.rightDerivedNatTrans`, from actual section restriction, its induced
   homotopy transformation, and the two right-derived units. On slice derived
   sections it is transported by `beta W` and `beta W'`. Because `beta` satisfies
   the preceding unit normalization, this is the uniquely normalized derived
   section pullback along localization/relocalization. The displayed square
   asserts alpha followed by this rho equals Q of literal restriction followed by
   alpha at the target. `ObjectProperty.homMk` only bundles the literal chain map
   as a morphism of bounded-below complexes.
7. The next clause quantifies over `L'`, `K'`, `e'`, a chain map `f` and a derived
   map `k` with `Q.map f ≫ e'.hom = e.hom ≫ k`. Its equality is the required
   naturality in complexes and identifications, including `f = identity` and a
   change of `e`.
8. `D.op ⋙ constantModuleSectionDiagram J Λ L.obj` is a strict functor for every
   small `I : Type i` and `D : I ⥤ C`. Its functor laws are actual restrictions'
   functor laws, and the clause supplies one integer lower bound for all its
   objects. The independently explicit universe `i` imposes no restriction on
   diagrams, and no colimit or size-sensitive operation on `I` is required.
9. The last clause takes any injective module sheaf `M`, the single complex in
   degree zero, restricts it by the actual derived slice restriction, and asserts
   `IsZero` of every positive homology object of actual slice derived sections.
   It makes no assertion that forgetting the module structure preserves injectives.

Dependency interfaces read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: the covering-site component;
  Mathlib's associated `GrothendieckTopology` is the chosen site representation.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  transparent Mathlib `SheafOfModules`, used verbatim.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`, `CategoryTheory.constantSheaf`,
  and `toSheafify`: constant ring sheaf and its canonical scalar map.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
  `SheafOfModules.overFunctor`, `over`, and the localized `J.over W`:
  actual sectionwise localized ringed site and restriction.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`; `TStructure`, `DerivedCategory.Plus`;
  `CochainComplexPlus`, `CochainComplex.Plus`: the recorded derived and bounded
  below notions. `CategoryTheory.Injective` is the recorded injectivity predicate.
- The newly cited landed module
  `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`,
  `CategoryTheory.ringedOverFunctor_exactGeneral`: supplies additive exact slice
  restriction, with Mathlib's canonical `mapDerivedCategoryPlus` construction.
- Proof inputs are imported from
  `Sheaf.Algebra.Homology.LocalizedRestrictionAdjunction`,
  `CategoryTheory.localized_restriction_adjunction`;
  `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`,
  `SheafOfModules.isGrothendieckAbelianOfUniverses`;
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`,
  `CategoryTheory.IsGrothendieckAbelian.enoughInjectives`;
  `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves`;
  and Mathlib `RightDerivedFunctorPlus`, `Functor.rightDerivedFunctorPlus`,
  `rightDerivedFunctorPlusUnit`, and `rightDerivedNatTrans`.
  The proof dependency `lem-pe-constant-left-module-inverse-image` currently has
  no recorded Lean module to import. It is not assumed in this statement.

Edge cases checked by reading the actual types/constructions: the zero complex;
any integer lower bound (not only zero); empty `C` and empty indexing `I`;
identity and composite site arrows; terminal slice object `id_W`; arbitrary
specified derived identifications and their changes; the zero ring; and
noncommutative rings (all scalar constructions use `Ring`, never `CommRing`).
No `STATEMENT-DISPUTED` flag or mathematical node correction is needed.

Searches: the retained node's stage-1 LeanSearch, LeanFinder, Loogle and Mathlib
pattern searches were reviewed; none asserts the complete node statement.
The resumed worker ran these additional searches:

- `msearch.py` LeanFinder: “Natural derived evaluation of constant ring module
  sheaves on localized slice sites computed by one bounded below injective
  complex”. Eight hits (Tilde constants, local cohomology diagram, module local
  generators); none is this statement.
- `msearch.py` Loogle:
  `CategoryTheory.Functor.rightDerivedFunctorPlus, CategoryTheory.Injective`:
  zero hits.
- `msearch.py` grep:
  `injectiveComplexSliceSectionModel|constantModuleSectionComparison|constantModuleDerivedRestriction`:
  zero hits in Mathlib.
- `rg` for the item id in upstream `WeilConjectures/` and project `lean/Sheaf/`:
  no existing complete declaration. `rg` for the new scalar-evaluation helper
  names in Mathlib, upstream and project: none.
- Targeted `rg` and source reads of `SheafOfModules.evaluation`,
  `PresheafOfModules.restrictScalars`, `overFunctor`, `rightDerivedFunctorPlus`,
  `mapDerivedCategoryPlus`, and `mapDerivedCategoryPlusFactorsh` found the
  reusable APIs used here. No independent new notion or dependency repair was
  needed; all helpers belong to the canonical section model of this node.

Validation: `scompile.py Q11 lem-pe-injective-complex-slice-section-model` compiled
both the sandbox probe and the named module without errors or warnings. All
variables and universes are explicit. The only `sorry` is the node's named theorem,
whose docstring includes the six-step proof and its literature references.

## Resumed packet self-check (2026-10-17)

The required initial dry run compiled the saved module but rejected five entries
of `lean.declarations`: `moduleSheavesEnoughInjectives`,
`sliceModuleEnoughInjectives`, `sliceRestrictionAdditive`,
`sliceRestrictionFiniteColimits`, and `sliceRestrictionFiniteLimits`. They were
file-local instances, so their recorded public names did not exist. Each is now
a public instance with the same construction and source docstring. This also
removes the forbidden file-local instances from the statement module.

Read the current node, its statement-dependency records and their source
signatures/docstrings, and checked the saved clause correspondence against the
module. The theorem retains the noncommutative coefficient ring, all integer
lower bounds, the specified derived identification, normalized canonical maps,
restriction square, naturality, arbitrary small diagrams and positive-degree
vanishing. No change to its mathematical statement was needed. The five public
instances are the only Lean changes in this resumed repair.

The prescribed `scompile.py` compiled both the sandbox probe and final library
module cleanly (9.2 s and 10.7 s respectively); no warnings were emitted.

## Final resumed validation

The saved packet passed the prescribed dry run, including server preflight and
per-file compilation. The final self-check confirmed that only `lean` and the
addition of the already landed derived-restriction dependency differ from the
base node, and that the module contains exactly one postponed theorem. The
recorded signature had identical tokens but collapsed whitespace; it now copies
the signature's actual line breaks and indentation verbatim. No Lean source or
mathematical statement was changed in this final continuation.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
