## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteTypeHomColimitQcEquality` states
`SheafOfModules.finite_type_hom_colimit_qc_equality`. Its sole proof is `sorry`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.

Sources read: Stacks `sheaves.tex`, Tag 009F (`lemma-directed-colimits-sections`),
statement and proof of (2), lines 3444–3500; `modules.tex`, Tag 01B5
(`definition-finite-type`), lines 810–818, and Tag 01BS
(`lemma-finite-presentation-quasi-compact-colimit`), lines 3818–3856. The item is
explicitly the finite-type equality strengthening formulated by its stage-1 worker;
01BS's finite-presentation and overlap hypotheses are not imported into this lemma.
The declaration docstring reproduces all five steps of the node's proof, including
local lifting through the generating epimorphism rather than sectionwise surjectivity.

Hypotheses and clauses, matched individually:

- A topological space X with a sheaf of commutative rings O is bundled as
  `(X : RingedSpace.{u})`. This is Mathlib's `SheafedSpace CommRingCat`; it imposes
  no local-ring, scheme, separation, or compactness assumption on X.
  `moduleRings X` is the project's existing forgetful view of its commutative ring
  sheaf as a ring sheaf. Thus no noncommutative generalization is silently substituted.
- The category of O-modules is `ringedSiteModules.{u} (moduleRings X)`, the recorded
  dependency's transparent abbreviation of Mathlib `SheafOfModules`.
- I is a nonempty directed preordered set through `{I : Type u}`, `[Preorder I]`,
  `[IsDirected I (· ≤ ·)]`, and `[Nonempty I]`. A preorder rather than a partial
  order retains the allowed non-antisymmetric case. Its universe is the common
  site/coefficient/module universe; no independent smaller index universe occurs.
- The specified diagram and its transitions are `(F : I ⥤ ...)` and
  `F.map (homOfLE hik)`. Functoriality supplies exactly the diagram identities.
- The given object F and specified legs c_i, with their colimit universal property,
  are `(c : Cocone F)` and `(_hc : IsColimit c)`. The object is `c.pt`, the legs
  `c.ι.app i`. This quantifies over every colimit cocone, rather than assuming a
  particular chosen colimit or adding a preservation hypothesis.
- The open subset is `(U : Opens X)`. Its quasi-compactness is
  `(_hU : IsCompact (U : Set X))`, valid in arbitrary topological spaces and without
  any Hausdorff or quasi-separatedness assumption.
- G is `(G : ringedSiteModules.{u} ((moduleRings X).over U))`. The over-site of an
  open U has objects precisely opens contained in U and the usual open coverings.
  Its ring sheaf `R.over U` evaluates to R on those opens, so this encodes exactly
  the specified restriction, not an arbitrary pullback or arbitrary comparison map.
- `[G.IsFiniteType]` is the dependency's recorded Mathlib definition of locally
  finite generating sections with an epimorphism from the free module. Finite
  generating index types include the empty type. No finite-presentation hypothesis
  is present.
- `(i j : I)` and `(g : G ⟶ (F.obj i).over U)` /
  `(g' : G ⟶ (F.obj j).over U)` give exactly the two O|U-linear maps.
  Mathlib `SheafOfModules.Hom` consists of sectionwise linear natural maps.
- `(_h : g ≫ (c.ι.app i).over U = g' ≫ (c.ι.app j).over U)` is precisely
  equality of the two composites into the restricted specified colimit object.
  Lean's `≫` writes composition in diagram order.
- `∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k), ...` supplies a common later stage.
  Its final equation uses `g ≫ (F.map (homOfLE hik)).over U` and the analogous
  expression for g'. These are exactly the requested restricted transition maps.
- The node's final negative qualifications are honored by the absence of finite
  presentation, quasi-separatedness, and monomorphism/injectivity assumptions.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the recorded declaration of `def-weil-sheaf-of-modules-category`, transparently
  using Mathlib `SheafOfModules` and its `Hom` structure.
- `Mathlib.CategoryTheory.Limits.HasLimits`: the colimit interface; its underlying
  `CategoryTheory.Limits.Cocone` and `IsColimit` signatures and documentation were
  read in `Limits/Cones.lean` and `Limits/IsLimit.lean`. This is the recorded
  `def-weil-pbc-category-colimit` interface, retaining the specified cocone legs.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`:
  `SheafOfModules.IsFiniteType`, `LocalGeneratorsData`, `GeneratingSections` and
  the latter's `epi` field, for `def-weil-pbc-module-finite-type-presentation`.
  The finite-presentation half is not needed for this statement.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` (publicly
  available through the imports): `SheafOfModules.over`, `overFunctor`, and
  `SheafOfModules.Hom.over`. Their definitions restrict by the forgetful functor
  from `Over U`, exactly preserving values and restrictions on opens below U.
- `WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris`:
  `AlgebraicGeometry.moduleRings`, the existing ringed-space convention.

Every recorded proof dependency with a module is imported without `public`:
`Sheaf.CategoryTheory.ModuleDirectedColimitUnderlyingSets`
(`SheafOfModules.underlying_directed_colimit_isColimit`),
`Mathlib.CategoryTheory.Sites.Limits`
(`CategoryTheory.Sheaf.sheafifyCocone`, `isColimitSheafifyCocone`),
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`
(`CategoryTheory.sheafification_sections_local`),
`Mathlib.CategoryTheory.Limits.Types.Filtered`
(`CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff` and its primed
variant), and
`WeilConjectures.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting`
(`AlgebraicGeometry.RingedSpace.module_exactness_local_lifting`). Their source
signatures and docstrings were read. Definition proof dependencies already have
public statement imports. No proof-dependency import creates a cycle.

Edge cases checked: U may be empty, X may be empty, G may be zero, local generating
families may have zero elements, I may be a singleton, i may equal j, the preorder
may fail antisymmetry, and transition maps need not be injective. For the empty open
or zero generators, any common bound of i and j suffices; the sheaf axiom handles
empty opens. No condition on compactness of intersections is used. The finite-type
argument bounds finitely many local stages only after taking a finite cover of U.

Searches actually run with `batch2/msearch.py` for this group and item:

- LeanFinder: "Maps from a finite type sheaf of modules into a directed colimit
  which agree in the colimit agree at a later stage on a quasi compact open".
  Eight hits: scheme-limit section lemmas, `Scheme.IsLocallyDirected.ι_eq_ι_iff`,
  `Module.DirectLimit.exists_eq_of_of_eq`, and `Scheme.Modules.instHasColimits`.
  None state the module-sheaf finite-type Hom assertion.
- Loogle: `SheafOfModules.IsFiniteType`. Four hits: the finite-type class,
  `exists_localGeneratorsData`, its constructor, and finite presentation implies
  finite type. These provide the existing notion, not the requested theorem.
- Grep: `IsFiniteType|exists_eq_of_isColimit|eventually.*eq` in
  `Algebra/Category/ModuleCat/Sheaf`. Ten hits in Generators and Quasicoherent,
  concerning finite generators and finite presentations, no theorem matching this item.
- LeanSearch: "Two maps from a finite type module sheaf to stages of a directed
  colimit which agree in the colimit eventually agree on a quasi compact open".
  Eight hits concerning direct-limit congruence, sheaf colimit existence, scheme
  gluing, sheafification congruence, and tilde restriction; no exact match.
- Direct `rg` in both project roots for `IsFiniteType`, finite-type/colimit names,
  and the proposed declaration name found finite-type module results and unrelated
  site-colimit stabilization theorems; none match this assertion. A literal grep for
  this item id in `lean/WeilConjectures` found no declaration. The proposed declaration
  name was also checked in `dag/lean_names_upstream.json` with no collision.
- Mathlib's categorical `IsFinitelyPresentable.exists_eq_of_isColimit` is a nearby
  result, but requires categorical finite presentability, which the node does not
  assume. It cannot be used as an existing exact statement.

The example Sheaf CompactObject module is now withdrawn; its node records the
upstream `WeilConjectures.CategoryTheory.CompactObject`. That current module and
record were read for the header, public-section, namespace and docstring conventions.

Validation: `scompile.py NP lem-weil-pbc-finite-type-hom-colimit-qc-equality` compiled
the delivered file both in its sandbox and at its actual module path on the server
(1.7 s and 1.5 s respectively), with no errors or non-sorry warnings. The node copy
changes only `lean`; its signature is extracted verbatim from the Lean source.
No statement dispute or node fault was found.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
