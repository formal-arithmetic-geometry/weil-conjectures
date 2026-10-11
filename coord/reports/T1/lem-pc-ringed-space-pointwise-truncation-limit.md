## Worker report

The module `Sheaf.Topology.PointwiseTruncationLimit` states
`AlgebraicGeometry.RingedSpace.pointwise_truncation_limit`, with one `sorry` and no
new definition. It formalizes Stacks [0D62](https://stacks.math.columbia.edu/tag/0D62)
and [0H72](https://stacks.math.columbia.edu/tag/0H72), opened online because the
local Stacks TeX checkout is absent. No correction or disputed statement is needed.

Hypotheses and clauses:

- The ringed space is `X : RingedSpace.{u}`. Its module category is the recorded
  `SheafOfModules.{u} (moduleRings X)`, with the existing abelian instance. The binder
  `HasDerivedCategory.{w}` supplies the chosen localization/morphism universe, not a
  boundedness assumption. `E : DerivedCategory ...` is arbitrary and unbounded.
- For each point `x : X`, `hlocal` asserts existence of `b : ℤ → ℤ` and
  `B : Set (Opens X)`. The clause `∀ U ∈ B, x ∈ U` says all members are open
  neighborhoods. The clause `∀ V, x ∈ V → ∃ U ∈ B, U ≤ V` says they form a
  fundamental system. Neither a countable nor a uniform system is required.
- The vanishing clause quantifies over every integer `m`, every cohomology degree
  `p : ℕ`, and every open `U ∈ B`, with the strict bound `b m < (p : ℤ)`.
  The coefficient is exactly `(DerivedCategory.homologyFunctor ... (m-p)).obj E`.
  `IsZero ((openModuleCohomology X p U).obj ...)` is zero cohomology of this
  module on U. Ordinary module-sheaf cohomology has natural-number degrees;
  negative degrees vanish automatically, so this loses none of the source's
  vanishing conditions even when b(m) is negative.
- The tower's nth term is `(DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E`
  for every `n : ℕ`, including zero. Its transition is
  `(t.natTransTruncGEOfLE (-((n+1 : ℕ) : ℤ)) (-(n : ℤ)) ...).app E`.
  The tiny arithmetic proof supplies only the inequality specifying this canonical
  transition. The map c_n is `(t.truncGEπ (-(n : ℤ))).app E`. Compatibility
  is built into these Mathlib canonical transformations, not imposed on arbitrary maps.
- `HasProduct` is the product of these precise tower terms in D(O_X), not a
  product of complexes. `K`, `π`, `δ`, and `hK : IsDerivedLimitTriangle ... K π δ`
  encode the specified triple and its distinguished Roos triangle with `1-s`.
- The first conclusion is `∃ c : E ⟶ K, ∀ n, c ≫ π ≫ Pi.π ... n = c_n`.
  Lean composes left-to-right, so this is the node's pr_n ∘ p ∘ c = c_n.
- The second conclusion quantifies over *every* morphism c satisfying exactly those
  projection identities and asserts `IsIso c`. It does not assert uniqueness of c,
  nor merely that one choice is invertible.

Dependency declarations read and used:

- Mathlib.Algebra.Category.ModuleCat.Sheaf: `SheafOfModules` (the general-site
  `mathlib_match` of def-weil-sheaf-of-modules-category). Its record explicitly says
  this general form is used for ringed spaces; `Scheme.Modules` would restrict X
  to schemes and is not used.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `HasDerivedCategory`,
  `DerivedCategory`, and `DerivedCategory.homologyFunctor` (cohomology descended
  from complexes, exposed by the derived t-structure import).
- Mathlib.Algebra.Homology.DerivedCategory.TStructure: `DerivedCategory.TStructure.t`.
  Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE: `truncGE`, `truncGEπ`,
  `natTransTruncGEOfLE`, and its canonical projection compatibility.
- Sheaf.CategoryTheory.Triangulated.DerivedLimit: `CategoryTheory.IsDerivedLimitTriangle`.
  It states exactly that the specified Roos triangle is distinguished; the existential
  object predicate `IsDerivedLimit` would forget the specified π and δ.
- Sheaf.Topology.RingedSpaceModuleCohomology: `RingedSpace.moduleCohomology`
  defines the underlying injective-module-resolution convention. The imported
  Sheaf.Topology.OpenModuleCohomology specializes it to opens using the recorded
  `RingedSpace.openModuleCohomology`. Its landed node `def-sc-open-module-cohomology`
  is added to stmt_deps (allowed landed-definition addition). No duplicate is defined.
- Sheaf.Paper.PQFCohomology: `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`
  was read. This existing dependency concerns schemes, long exact sequences and
  higher direct images. The present statement uses the more general recorded ringed
  space/open cohomology definitions above, so this unrelated theorem is not imported.

Edge cases checked: the empty space makes hlocal vacuous and has only zero module
sheaves; zero E satisfies all local bounds. For every actual point, the system B
is nonempty by taking V = top; no empty-neighborhood system can satisfy hlocal.
Bounds b(m) may be negative; degree zero is tested when required. Integer m is
unrestricted, and n=0 gives truncation at zero. Universes u and w are explicit;
no chosen standard derived-category instance or artificial boundedness is introduced.
Products are assumed only for this countable tower, as in the node. No hypothesis
about a point, dimension, quasi-coherence, or scheme structure is added.

Searches for an exact existing declaration:

- msearch.py leanfinder: `pointwise cohomology vanishing reconstructs derived object
  from lower truncations` returned eight basic CochainComplex truncation/quasi-isomorphism
  results, no pointwise derived-limit reconstruction theorem.
- msearch.py loogle: `DerivedCategory.TStructure.t, IsDerivedLimit` returned zero
  hits (unknown project identifier IsDerivedLimit).
- msearch.py leansearch: `pointwise vanishing cohomology derived limit truncations`
  reported service unavailable, Internal Server Error. No verdict inferred from it.
- msearch.py grep: `is_limit_per_point|pointwise.*truncation|truncation.*limit`
  in Mathlib/Algebra/Homology returned zero hits.
- rg in WeilConjectures and lean/Sheaf for `pointwise.*truncation`,
  `is_limit_per_point`, and the item id returned no exact theorem. A broader search
  found the scheme-specific QCohTruncationDerivedLimit, which cites the ringed-space
  result and is not the same statement. Grep/rg for this item's id in upstream Lean
  and dag/lean_names_upstream.json returned no declaration. The new full declaration
  name was likewise absent from the source and project searches.

Validation: scompile.py compiled the 75-line module on the server in 2.6 seconds,
exit code 0, no errors or warnings. All variables and universes are bound explicitly.
The required dry run is run after writing this record; the second reader supplies
its independent reading and delivers.

## Second reading by T1

I read the node statement and matched each item to
`AlgebraicGeometry.RingedSpace.pointwise_truncation_limit`.

- The base object is `X : RingedSpace.{u}`; the Lean binder is identical.
- The derived category is the category of `SheafOfModules.{u} (moduleRings X)`,
  with `[HasDerivedCategory.{w} ...]`; this is the dependency's recorded general
  ringed-space category and introduces no scheme, Noetherian, or boundedness
  hypothesis.
- `E` is arbitrary in that derived category. For each `x : X`, Lean introduces
  `b : ℤ → ℤ` and `B : Set (Opens X)`, requires every `U ∈ B` to contain `x`,
  requires `∀ V, x ∈ V → ∃ U ∈ B, U ≤ V`, and imposes the stated vanishing for
  every `m : ℤ`, `p : ℕ`, and `U ∈ B` whenever `b m < (p : ℤ)`. The coefficient
  is exactly `homologyFunctor ... (m - (p : ℤ))`, and the open cohomology functor
  is exactly `openModuleCohomology X p U`.
- The tower is indexed by all `n : ℕ`, with terms
  `t.truncGE (-(n : ℤ)).obj E`, canonical `natTransTruncGEOfLE` transitions, and
  canonical projections `truncGEπ`; the arithmetic proof supplies only the
  required transition inequality.
- `K`, `π`, and `δ` have the specified product and shift types, and `hK` is the
  recorded `IsDerivedLimitTriangle`, so the chosen Roos derived limit is fully
  specified.
- The conclusion first existentially quantifies `c : E ⟶ K` and requires every
  projection composite to equal `c_n`; the second conjunct quantifies every such
  compatible `c` and requires `IsIso c`. Composition order in Lean is the node's
  `pr_n ∘ p ∘ c` convention.

Edge cases were checked: `n = 0` is included; negative values of `b m` and all
integer `m` are allowed; `p = 0` is included; the empty space makes the local
hypothesis vacuous; a nonempty point forces a nonempty neighborhood system by
taking the top open; and the zero derived object satisfies the hypotheses. No
universe restriction or characteristic assumption is added.

I searched Mathlib, `WeilConjectures`, and `lean/Sheaf` with `rg` for the item and
for `pointwise.*truncation`, `truncation.*limit`, and `is_limit_per_point`; only
the unrelated scheme-specific `QCohTruncationDerivedLimit` was found. The
configured LeanFinder/Loogle/LeanSearch searches in the worker record likewise
found no existing theorem. The dependency declarations and the source tags 0D62
and 0H72 were read. No mismatch was found, so no file, statement, or dependency
record was changed.

The module was recompiled with `scompile.py`; it completed with exit code 0 and
no warnings other than the permitted `sorry` declaration warning.
