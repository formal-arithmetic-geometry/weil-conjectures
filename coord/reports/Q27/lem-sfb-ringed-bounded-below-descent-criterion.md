## Worker report

The module Sheaf.CategoryTheory.RingedBoundedBelowDescent states
CategoryTheory.RingedToposMorphism.boundedBelowDescent, with `sorry` as its only
proof. No definitions, additional nodes, dependency repairs, or statement corrections
are needed. The node's natural-language statement is unchanged.

Source read: literature/stacks-project/sites-cohomology.tex,
lemma-equivalence-bounded (Tag 0D7U), statement and entire proof, lines 6390–6445.
The node's six proof steps are included in the theorem docstring. In particular,
the spectral sequence has only its p=0 column and a finite filtration in each
total degree; there is no local cohomological bound in this result.

Clause-by-clause correspondence:

- The small sites are `{C D : Type u} [SmallCategory C] [SmallCategory D]`
  with Grothendieck topologies `J` and `K`. This is the chosen-small-site
  presentation of the size convention; site, coefficient and module sizes fit u.
  Derived morphism sizes remain independent `wO` and `wR`, with two explicit
  `HasDerivedCategory` instances. The module uses the standard abelian instance,
  not a chosen second abelian structure.
- Commutative ring sheaves are `O : Sheaf J CommRingCat.{u}` and
  `R : Sheaf K CommRingCat.{u}`. Their images under
  `sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})` are used only to meet
  the existing RingCat-valued module-sheaf and ringed-topos interfaces.
- The ringed-topos map is the recorded `RingedToposMorphism` binder `f`.
  Its `modules` field is the structural-map-induced direct image, not an
  unconstrained functor. The ordinary inverse image is `F`, with
  `adj : F ⊣ f.modules`: this presents the module inverse image by its defining
  adjunction to that direct image. Left adjoints with their adjunction units
  are uniquely isomorphic, so this does not assume another kind of pullback.
- Exactness of f* is `[F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F]`. Its derived functor is exactly Mathlib's
  `F.mapDerivedCategory.{wR, wO}`, with its standard termwise comparison
  `F.mapDerivedCategoryFactors.{wR, wO}`.
- `Rf`, its comparison `β`, and `hRf : Rf.IsRightDerivedFunctor β ...`
  specify total right derived direct image of `f.modules` at quasi-isomorphisms.
  `hKI` specifies computation by K-injectives: `β.app I` is invertible whenever
  `I.IsKInjective`. These binders present the very derived functor stipulated
  by the node; they are not an acyclicity assumption on arbitrary sheaves.
- `d : F.mapDerivedCategory ⊣ Rf` is the stipulated derived adjunction.
  `hd` fixes its canonical normalization on each complex P: the derived unit,
  followed by Rf of the termwise comparison, equals the localization of the
  ordinary termwise unit followed by β at F(P). This is the canonical
  derived-unit factorization. It determines the unit, hence the adjunction
  and its counit; no arbitrary derived adjunction is substituted.
- A and B are `ObjectProperty` predicates on the exact recorded module
  categories. For each, `ContainsZero`, `IsClosedUnderIsomorphisms`,
  `IsClosedUnderKernels`, `IsClosedUnderCokernels`, and
  `IsClosedUnderExtensions` expand precisely the node's weak Serre condition.
  `FullSubcategory` supplies full morphism sets; isomorphism closure makes it
  strictly full. Full Serre closure under all subobjects is not imposed.
- `eHeart : B.FullSubcategory ≌ A.FullSubcategory` and
  `hHeart : eHeart.functor ⋙ A.ι ≅ B.ι ⋙ F` say that this equivalence is induced
  by F. The natural isomorphism is the standard way to identify a restriction
  with a functor landing in a full subcategory; no unrelated heart equivalence
  is used.
- `hunit` quantifies over every module G with `B G`, and asserts invertibility
  of `d.unit.app ((DerivedCategory.singleFunctor ... 0).obj G)`. Thus the
  acyclicity hypothesis is exactly on G in degree zero, with the canonical unit.
- `DerivedCategory.homologyProperty A` (respectively B) means every integer
  cohomology object lies in A (respectively B). Intersection with
  `DerivedCategory.TStructure.t.plus` means bounded below: there exists an
  integer n with zero cohomology below n, by `DerivedCategory.isGE_iff`.
  The full subcategories in the existential conclusion are precisely D+_B
  and D+_A, inside the ordinary unbounded derived categories.
- The existential `e` is an equivalence of those full subcategories. Its two
  functor equalities after inclusion identify its functor with termwise
  derived F and its inverse with Rf. Such restrictions have literally those
  objects and morphisms; proof fields of full-subcategory objects are irrelevant.
- The final two universal clauses assert `IsIso (d.unit.app L)` on every
  bounded-below B-object and `IsIso (d.counit.app M)` on every bounded-below
  A-object. These are the actual ambient canonical adjunction components,
  not merely some isomorphisms between the same objects.

Dependency declarations read and used:

- Sheaf.CategoryTheory.RingedToposMorphism:
  CategoryTheory.RingedToposMorphism, including every structural field and its
  induced module-direct-image normalization.
- Sheaf.CategoryTheory.RingedSiteModules:
  CategoryTheory.ringedSiteModules, the transparent abbreviation of
  Mathlib SheafOfModules; its category and abelian instance are inherited.
- Sheaf.CategoryTheory.SiteCoveringAxioms:
  CategoryTheory.Precoverage.IsSiteForCoverings. This is the recorded sites
  dependency module; the statement itself uses its underlying existing
  GrothendieckTopology and Sheaf interfaces, not covering-family data.
- def-weil-size-convention has a convention-only record and no declaration;
  explicit universes implement it.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory,
  HasDerivedCategory, Q and singleFunctor; ExactFunctor: mapDerivedCategory
  and mapDerivedCategoryFactors; TStructure: TStructure.t, IsGE and isGE_iff.
- WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty:
  DerivedCategory.homologyProperty; Mathlib's ObjectProperty closure classes,
  FullSubcategory and inclusion functors are reused through its imports.
- Proof imports: Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses,
  SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses;
  Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction,
  SheafOfModules.module_pullback_pushforward_adjunction;
  Mathlib.CategoryTheory.Adjunction.Limits,
  CategoryTheory.Adjunction.rightAdjoint_preservesLimits;
  Mathlib.Algebra.Homology.ShortComplex.PreservesHomology,
  CategoryTheory.Functor.homologyFunctorIso;
  WeilConjectures.CategoryTheory.TruncationHypercohomology,
  CategoryTheory.exists_truncationHypercohomology.
  The two cohomology-to-unit/counit proof dependencies currently have no Lean
  record, so no nonexistent module is imported. They are proof inputs, not
  notions needed to type this statement.

Edge cases checked before writing: zero objects and the zero heart satisfy the
stated weak Serre conditions and give the expected zero derived subcategories;
the full heart recovers the usual bounded-below equivalence criterion. The
identity morphism has identity units and counits. Any integer lower bound,
including negative bounds, is allowed, and bounds may depend on the object.
Unbounded-above objects remain allowed. Degree zero and all negative cohomology
are accounted for by the ordinary singleFunctor and integer-indexed homology.
Empty sites and zero coefficient rings are not excluded. The two derived
morphism universes are not identified. No disputed statement or node fault found.

Searches made, with results:

- msearch.py leanfinder, query: "Exact pullback equivalence of weak Serre hearts
  and acyclic derived unit implies bounded below derived equivalence".
  Eight hits: exact-functor localization and derived-category boundedness APIs;
  no bounded-below heart descent criterion.
- msearch.py loogle, query: `"DerivedCategory", "equivalence"`.
  Zero hits.
- msearch.py leansearch, query: "An exact left adjoint inducing an equivalence
  on weak Serre subcategories induces an equivalence on bounded below derived
  subcategories when the derived unit is invertible on the heart".
  Eight hits, mainly Adjunction.derived, derived unit factorization and abstract
  adjoint equivalence; none states this cohomological descent criterion.
- msearch.py grep, query: `weak.?[Ss]erre|bounded.?[Bb]elow.*[Ee]quivalence`,
  Mathlib CategoryTheory. Zero hits.
- rg over Mathlib CategoryTheory and Algebra/Homology, WeilConjectures and Sheaf:
  `WeakSerre|IsWeakSerre|weakSerre|boundedBelowDescent|bounded_below_descent`.
  Found and reused homologyProperty and the existing ObjectProperty weak Serre
  closure classes; found no theorem matching the item.
- rg in WeilConjectures for the item id: no result. Further search for
  `bounded.*descent|equivalence-bounded|boundedBelowDescent` found unrelated
  bounded complex/graded descent and no declaration with this signature.

Validation: scompile.py compiles both sandbox and actual module forms in well
under 60 seconds. Explicit CommRingCat and RingCat universe arguments resolve
an expensive unification problem; the delivered file does not raise heartbeat
or timeout limits and has no diagnostic commands or local notation.

## Second reading by Q27

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
