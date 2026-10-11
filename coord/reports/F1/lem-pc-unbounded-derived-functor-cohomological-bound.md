## Worker report

The module `Sheaf.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound` states
`AlgebraicGeometry.isZero_homology_rightDerivedFunctor_of_cohomological_bound`.
Its only proof is `sorry`; it introduces no definitions. The item node changes only in `lean`.

Hypothesis and clause correspondence:

- A scheme X: `(X : Scheme.{u})`, with no separation, finiteness, or Noetherian assumptions.
- The category Mod(O_X): `SheafOfModules.{u} (moduleRings X.toRingedSpace)`, using the
  shared carrier and category instance of `def-pc-derived-category` rather than the separate
  `X.Modules` category instance. These are Zariski sheaves of structure-sheaf modules.
- The additive functor into abelian groups: the binder `F` into `AddCommGrpCat.{u}` and
  `[F.Additive]`. No left-exactness hypothesis is added: both right-derived constructions
  used here are defined for additive functors, as required by Stacks 08D4.
- Commutation with countable direct products:
  `[PreservesLimitsOfShape (Discrete ℕ) F]`. Every countable family can be padded with
  zero objects to an N-indexed family; additivity preserves the zero object.
- A nonnegative integer N: `(N : ℕ)`, cast into Z in the conclusion.
- Vanishing for every quasi-coherent module and every p ≥ N:
  `hN : ∀ M, M.IsQuasicoherent → ∀ p : ℕ, N ≤ p → IsZero ((F.rightDerived p).obj M)`.
- An integer b: `(b : ℤ)`, with no nonnegativity restriction.
- E in D_QCoh(O_X): `(E : schemeDerivedCategory X)` and
  `(hE : schemeDerivedQCohProperty X E)`. This is equivalent to an object of the full
  subcategory `schemeDerivedQCohCategory X`, without imposing bounded-below support.
- H^i(E) = 0 for i > b: `hb`, universally quantified over integer degrees, with strict `b < i`
  and `IsZero` applied to the module-valued `DerivedCategory.homologyFunctor`.
- H^i(RF(E)) = 0 for i > b+N-1: the conclusion universally quantifies integer i and
  uses exactly `b + (N : ℤ) - 1 < i`, `F.rightDerivedFunctor.obj E`, and the
  abelian-group-valued `DerivedCategory.homologyFunctor`.

The `HasDerivedCategory` binders specify the shared localization infrastructure, with explicitly
bound, independently chosen morphism universes `w`, `w'`. `HasKInjectiveResolutions` and
`HasInjectiveResolutions` specify the infrastructure for the two existing right-derived
constructions. These exist for the sheaf module category (enough injectives and unbounded
K-injective resolutions), and do not impose a geometric condition on X. No K-injective
resolution assumption on the target category is needed. All variables and universes are explicit.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its category structure
  (`def-pc-scheme`).
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules` and its `Hom`/category structure
  (`def-weil-sheaf-of-modules-category`, mathlib_match, with no lean record required).
- `Mathlib.CategoryTheory.Abelian.RightDerived`: `CategoryTheory.Functor.rightDerived`
  (`def-sp-left-exact-additive`, mathlib_match). Its full signature requires additive F,
  abelian source/target, and source injective resolutions, not left exactness.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `AlgebraicGeometry.schemeDerivedCategory`
  and `AlgebraicGeometry.schemeDerivedQCohProperty` (`def-pc-derived-category`), read in full.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`:
  `CategoryTheory.Functor.rightDerivedFunctor`, the existing unbounded derived functor
  built using K-injectives and localization; its full definition and docstring were read.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsQuasicoherent`, reexported by the derived-category module.

Edge cases checked before writing: N=0 gives the sharper bound b-1, as the source states;
N=1 gives b; negative b and all negative cohomological degrees remain allowed. E=0,
F=0, and the empty scheme satisfy the formulation. No nonempty index type or support
interval is assumed. Unbounded-below quasi-coherent E remains covered. No target morphism
universe is tied to the source morphism universe. The module/source sheaf and abelian-group
object universe is u, following the shared scheme-derived-category declaration.

Searches (2026-10-11):

- msearch.py leanfinder, query "additive functor commuting with countable products upper
  cohomological bound on unbounded derived complexes": 8 hits, all generic DerivedCategory
  support/localization lemmas, none stating this bound.
- msearch.py loogle, query "CategoryTheory.Functor.rightDerived, DerivedCategory.homologyFunctor":
  0 hits.
- msearch.py grep, query "cohomological.*bound|rightDerivedFunctor.*[iI]sLE" in
  Algebra/Homology/DerivedCategory: 1 unrelated Ext/TStructure docstring hit.
- msearch.py leansearch, query "cohomological dimension bound for right derived functor of
  unbounded quasi coherent complexes": unavailable, Internal Server Error.
- rg on WeilConjectures and lean/Sheaf for the bound patterns and the item id: no matching
  theorem. Specific adic lower-star bounds in the source use another category and another
  functor; the source's RightDerivedFunctor/Defs gives the construction, not this bound.
- rg for the proposed full declaration name in Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json: no existing declaration.

Source checked directly at https://stacks.math.columbia.edu/tag/08D4 (the local literature
checkout is absent). The upper-bound clause in part (3) agrees exactly with this statement.
No statement correction or disputed statement is necessary.

Proof-record fault for stage 3: Step 5's claimed inequality m=max(0,N-i-1) ≥ -b-1 does not follow from
N-i-1 ≤ -b-1 (take b=-5, N=1, i=10: m=0 < 4). The conclusion follows by first choosing
m sufficiently large, at least max(0,N-i-1,-b-1), and then chaining down to -b-1,
or by extending the stable identification directly. The docstring uses that valid argument.
The node's statement and proof fields are preserved for the next proof worker.

Validation: scompile.py compiled the single module on the server in 2.6 seconds, exit 0,
with no errors or warnings. The delivery dry run is the final validation.

## Second reading by F1

I read the node statement and Stacks Project Tag 08D4, part (3), against the module
`Sheaf.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound`.

- The scheme object is rendered by `(X : Scheme.{u})`; this is the Mathlib scheme of
  `[def-pc-scheme]`, with no separation, finiteness, or Noetherian hypothesis. Verdict: match.
- The source category is rendered by
  `SheafOfModules.{u} (moduleRings X.toRingedSpace)`, and the target category by
  `AddCommGrpCat.{u}`. Verdict: match the two categories in the node and source.
- The additive functor is the explicit `F` binder with `[F.Additive]`; countable product
  commutation is exactly `[PreservesLimitsOfShape (Discrete ℕ) F]`. Verdict: both hypotheses
  are present, with no left-exactness assumption added.
- The nonnegative integer is `(N : ℕ)`, and the vanishing hypothesis is exactly
  `hN : ∀ M, M.IsQuasicoherent → ∀ p : ℕ, N ≤ p → IsZero ((F.rightDerived p).obj M)`.
  Verdict: match, including all quasi-coherent modules and every `p ≥ N`.
- The derived object is `(E : schemeDerivedCategory X)` with
  `hE : schemeDerivedQCohProperty X E`, rendering `E ∈ D_QCoh(O_X)`. Verdict: match;
  no bounded-below condition is imposed.
- The upper support hypothesis is `hb : ∀ i : ℤ, b < i → IsZero (...)`, rendering
  `H^i(E)=0` for every `i>b`. Verdict: match, including integer degrees and strict inequality.
- The conclusion is `∀ i : ℤ, b + (N : ℤ) - 1 < i → IsZero (...)`, with target
  `DerivedCategory.homologyFunctor AddCommGrpCat.{u} i` applied to
  `F.rightDerivedFunctor.obj E`. Verdict: exact upper bound and target from the node.
- The derived-category and resolution typeclass binders supply the infrastructure required by
  the two recorded derived-functor constructions; they do not impose a geometric condition on
  `X`. Verdict: accepted infrastructure assumptions.

Edge cases checked: `N = 0` gives `b - 1`, `N = 1` gives `b`, negative `b` and all integer
degrees are admitted, and `E = 0`, `F = 0`, and an empty scheme are not excluded. The statement
uses no nonempty index type, support interval, or tied source/target morphism universe.

I repeated the existing-definition searches with LeanFinder/Loogle/grep over Mathlib,
`WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`; no declaration states this
bound. The source page was checked directly at Tag 08D4. No mismatch was found, so no Lean or
node statement was changed. The module compiled cleanly with `scompile.py`; its only proof is
`sorry`, as required for stage 2.
