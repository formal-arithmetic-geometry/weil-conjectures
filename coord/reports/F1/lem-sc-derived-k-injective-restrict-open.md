## Worker report

The module `Sheaf.Algebra.Homology.KInjectiveRestrictOpen` states that for a ringed
space `X`, an open `U : Opens X`, and a K-injective cochain complex `I` of
`SheafOfModules (moduleRings X)`, the complex obtained by applying
`SheafOfModules.overFunctor (moduleRings X) U` termwise is K-injective.  This is the
Lean rendering of the open inclusion `j : U ↪ X`, its termwise restriction
`j⁻¹ I`, and the conclusion that it is K-injective.  The class binder
`[I.IsKInjective]` is the node's K-injective hypothesis.  The explicit
`@CochainComplex.IsKInjective ...` supplies the target category and instances so the
mapped homological complex is recognized as a cochain complex.

The module imports `Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`, using
`AlgebraicGeometry.open_restriction_adjunction_exact` for exactness and the
extension-by-zero adjunction, and Mathlib's `CochainComplex.IsKInjective` notion.
The proof is `sorry`, as required at stage 2; the docstring records the intended
application of `CategoryTheory.Adjunction.preservesKInjectiveComplexes`.

Edge cases checked: `U = ⊥` (empty open) and `U = ⊤` (identity restriction) are
allowed by `U : Opens X`; no nonemptiness assumption is introduced.  The complex
is unbounded because its index is `ℤ`; no boundedness or injectivity of individual
terms is added.  Universes are explicitly fixed by `universe u` and
`SheafOfModules.{u}`.

Searches: `msearch.py leanfinder` for restriction of K-injectives found only generic
K-injective declarations and no restriction theorem; `msearch.py loogle`
`CochainComplex.IsKInjective` found the generic notion and no open restriction
result; grep of Mathlib for `IsKInjective.*restrict|restrict.*IsKInjective` found
zero hits.  `rg` over `WeilConjectures/` found the generic
`CategoryTheory.Adjunction.preservesKInjectiveComplexes` but no theorem for open
restriction.  `rg` over project `lean/Sheaf` found no existing declaration with
this node's statement.

## Earlier second reading (a previous round; superseded)

The node and module were read independently.  The binders `X`, `U`, and `I`
match the ringed space, open subspace, and complex in the node.  The typeclass
binder exactly supplies K-injectivity of `I`; the conclusion maps the complex
termwise with the restriction functor and asserts Mathlib's same K-injectivity
predicate in the module category on `U`.  No hypotheses or conclusion clauses
are added or omitted.  The explicit category and instance arguments in
`@CochainComplex.IsKInjective` only resolve elaboration and do not alter the
proposition.

## Second reading by F1

I independently read the node, the Lean module, all five statement dependencies,
and the actual Stacks `cohomology.tex` text at
`lemma-restrict-K-injective-to-open` (Tag 08BS). The local literature checkout is
absent, so I read the upstream raw TeX and checked the tag page
https://stacks.math.columbia.edu/tag/08BS. The surrounding section adds no global
finiteness, separatedness, locality, characteristic, or boundedness hypothesis.
The node agrees with the source; there is no statement correction.

Object/hypothesis/conclusion checklist:

- Ringed space `(X, O_X)`: `(X : RingedSpace.{u})`. Mathlib's `RingedSpace`
  abbreviates `SheafedSpace CommRingCat`, so this is a general ringed space,
  not a locally ringed space or a scheme. Verdict: exact.
- Open inclusion `j : U ↪ X`: `(U : Opens X)` canonically determines the
  inclusion. No separate arbitrary morphism replaces this inclusion. Verdict: exact.
- Sheaves of `O_X`-modules: `SheafOfModules.{u} (moduleRings X)`.
  I read `moduleRings` in `Sheaf.Paper.DerivedHomMayerVietoris`: it composes
  `X.sheaf` with the forgetful functor from commutative rings to rings, preserving
  the structure sheaf and module actions. Mathlib's `SheafOfModules` has a
  presheaf of modules and its underlying abelian sheaf condition. Verdict: exact.
- The arbitrary complex `I` is
  `(I : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ)`.
  It has all integer degrees and no boundedness or termwise-injectivity premise.
  Verdict: exact.
- K-injective hypothesis: `[I.IsKInjective]`. I opened Mathlib's class: every
  map from an acyclic complex is homotopic to zero, exactly the definition node.
  Verdict: exact, with no extra mathematical hypotheses.
- Termwise restriction `j⁻¹ I`: the object of
  `(SheafOfModules.overFunctor.{u} (moduleRings X) U).mapHomologicalComplex
  (ComplexShape.up ℤ)` at `I`. I opened `overFunctor`: it is the restriction
  pushforward along the forgetful functor from `Over U`, using the identity ring
  map. Opens over `U` are precisely opens contained in `U`; this is restriction
  to the open subspace, not inverse image along an unrelated map. Verdict: exact.
- Conclusion: `@CochainComplex.IsKInjective` on that restricted complex in
  `SheafOfModules.{u} ((moduleRings X).over U)`. The target is modules over the
  restricted structure sheaf `O_U`; the explicit category/Abelian arguments are
  inferred canonical Mathlib instances. Verdict: exact.

Dependencies: `Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`,
`AlgebraicGeometry.open_restriction_adjunction_exact`, gives exact restriction,
exact extension by zero and `j_! ⊣ j⁻¹` for this same `X,U`. I read its module
against its node; no arbitrary functors or scheme-only assumptions remain.
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`,
`CategoryTheory.Adjunction.preservesKInjectiveComplexes`, gives the generic
preservation statement for an additive right adjoint of an exact additive functor.
Its orientation is correct here. The other three dependency notions are Mathlib's
ringed spaces, module sheaves, and K-injective complexes, whose definitions I read.
There are no new definition nodes or dependency modules in this delivery and no
missing notion, private copy, or hollow definition.

Edge cases: the empty open `⊥`, full open `⊤`, empty ringed space, zero complex,
and degree zero are all included. There is no indexing-family nonemptiness
premise, no restriction on characteristic, and no field or scheme hypothesis.
The arbitrary universe `u` follows the dependency's small-open-site encoding;
all spaces, rings and modules can be placed in a common sufficiently large
universe. No independently smaller universe of test complexes is introduced.
Every variable and universe is explicitly bound. The only theorem proof is
`sorry`; no result is proved in this stage.

Independent searches (2026-10-11):

- LeanFinder via `msearch.py`, query “open subspace restriction functor sends
  homotopically injective module complexes to K-injective complexes”: eight hits,
  principally `CochainComplex.isKInjective_of_injective` and injective-resolution
  facts; these require boundedness or resolutions and are not this statement.
- Loogle via `msearch.py`, query `"IsKInjective"`: twelve hits, the definition,
  shifts, homotopy equivalences, and injective resolutions; no open restriction.
- LeanSearch via `msearch.py`, query “restriction to an open subspace preserves
  K-injective cochain complexes of modules”: service unavailable (Internal Server
  Error); no mathematical verdict inferred from this failure.
- `rg` for `IsKInjective`, `PreservesKInjectiveComplexes`, and
  `homotopically.injective`, filtered with `ringed`, `restriction`, `overFunctor`,
  and `open`, across Mathlib, `WeilConjectures`, and project `lean/Sheaf`:
  no existing theorem with this ringed-space restriction statement. The source
  has specialized étale/adic results and the generic adjunction theorem, not
  this declaration. The project's `rhom_into_kinjective_local` mentions the
  argument in its proof docstring but states a derived-morphism bijection.

Mismatches repaired: the file lacked the standard copyright/license/author
header; added it. The node's `lean.statement` put the colon and conclusion
on different lines than the file; replaced it with the literal signature from
`theorem` up to `:=`. The theorem docstring compressed the two proof steps;
expanded them to explicitly name both dependency nodes, the exact-left-adjoint
hypothesis, and application to the given complex. The mathematical signature
and node statement were correct and are unchanged.

Validation: server single-file compilation was clean before these documentary
repairs; the delivery dry run recompiles the final module and checks its records.
