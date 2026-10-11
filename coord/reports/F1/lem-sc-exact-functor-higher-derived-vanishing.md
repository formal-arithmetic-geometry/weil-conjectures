## Worker report

The module `Sheaf.CategoryTheory.Abelian.ExactFunctorHigherDerivedVanishing` states
`CategoryTheory.Functor.isZero_rightDerived_obj_of_exact`, with the proof `sorry`.
There are no definitions, new nodes, dependency modules, or statement corrections.
The node copy changes only `lean`. All universes and variables are explicitly bound.

Hypothesis and clause correspondence:

- Categories A and B: `{A : Type u₁} {B : Type u₂}` with independent morphism
  universes `[Category.{v₁} A] [Category.{v₂} B]`.
- Both categories abelian: `[Abelian A] [Abelian B]`, using the Mathlib class
  recorded by `def-sp-abelian`.
- Both have enough injectives: `[EnoughInjectives A] [EnoughInjectives B]`.
  The target-category assumption is retained exactly as the node requests, although
  the construction of the right derived functor uses only the source category's
  injective resolutions. Mathlib infers `HasInjectiveResolutions A` from
  `Abelian A` and `EnoughInjectives A`.
- The functor v:A → B: `(v : A ⥤ B)`.
- Additive: `[v.Additive]`, as recorded in `def-sp-left-exact-additive`.
- Exact: `[PreservesFiniteLimits v] [PreservesFiniteColimits v]`. For additive
  functors between abelian categories these are equivalent to preserving kernels
  and cokernels, hence exact sequences. This is the same formulation used by the
  upstream exact derived-functor module `RightDerivedFunctor/PlusExact.lean`.
  Mathlib's `Functor.preservesHomology_of_map_exact` in `Abelian/Exact.lean`
  gives kernel/cokernel preservation from exact-sequence preservation;
  `Functor.preservesFiniteLimits_of_preservesKernels` and
  `Functor.preservesFiniteColimits_of_preservesCokernels` in
  `Preadditive/LeftExact.lean` give the equivalent finite-limit/colimit formulation.
- Every object M: `(M : A)` without an injectivity assumption on M.
- Every integer q>0: `(q : ℤ) (hq : 0 < q)`. The conclusion uses `q.toNat`
  because Mathlib indexes ordinary right derived functors by natural numbers.
  On positive integers this conversion is a bijection with positive natural
  numbers and leaves the degree unchanged; no degree is lost or added.
- Right derived via injective resolutions: `v.rightDerived q.toNat`, precisely
  the declaration recorded by `def-sp-left-exact-additive`.
- Vanishing: `IsZero ((v.rightDerived q.toNat).obj M)`, the categorical formulation
  of the object being zero, independent of a chosen zero object.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`; its class signature and docstring give
  preadditivity, finite products, kernels/cokernels, and normal monos/epis.
- `def-sp-left-exact-additive`: `CategoryTheory.Functor.Additive` in
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`,
  `CategoryTheory.Limits.PreservesFiniteLimits` (and `PreservesFiniteColimits`)
  in `Mathlib.CategoryTheory.Limits.Preserves.Finite`, and
  `CategoryTheory.Functor.rightDerived` in
  `Mathlib.CategoryTheory.Abelian.RightDerived`.
  The latter is the chosen injective-resolution functor followed by homology.
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj` in that same module
  identifies it with H^n(v(I)) for any injective resolution.
- `def-sp-injective-resolutions`: `CategoryTheory.InjectiveResolution` and
  `CategoryTheory.HasInjectiveResolutions` in
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`;
  `CategoryTheory.Injective` and `CategoryTheory.EnoughInjectives` in
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`.
  Their full signatures and docstrings were read.
  `Mathlib.CategoryTheory.Abelian.Injective.Resolution` supplies the instance
  of `HasInjectiveResolutions` from an abelian category with enough injectives.
  These modules are transitively imported by `Abelian.RightDerived`.

Source: Stacks Project Tag 015F, Lemma 13.16.9(5),
https://stacks.math.columbia.edu/tag/015F, opened and read. The literature checkout
on this machine lacks the node's named TeX file, so the authoritative online tag
was used. It asserts vanishing in all nonzero integer degrees for an exact
functor; this node requests the positive-degree injective-resolution case.
The theorem's docstring includes all three proof steps and their dependency ids.

Edge cases checked before writing: degree 1 is the first vanishing degree;
degree 0 is explicitly excluded (the identity functor on abelian groups has
R^0(M)=M, so it could not be included); negative degrees are outside the node's
conclusion. The zero object M and the zero functor give zero in every positive
degree. Injective M recovers the existing Mathlib special case. No injectivity
of v(M) or preservation of injectives is assumed. Independent object and
morphism universes avoid imposing smallness or equal universes on A and B.
No mathematical statement fault or dispute was found.

Searches for an existing statement (2026-10-11):

- `msearch.py ... leanfinder "higher right derived functors of an exact additive
  functor vanish"`: eight hits, including
  `Functor.isZero_rightDerived_obj_injective_succ`, degree-zero identification,
  Ext maps, and induced derived-category functors; no exact match.
- `msearch.py ... loogle "CategoryTheory.Functor.rightDerived,
  CategoryTheory.Limits.IsZero"`: only
  `Functor.isZero_rightDerived_obj_injective_succ`, whose additional hypothesis
  `[Injective X]` was checked in its full signature. It is not the statement
  for all M and exact v.
- `msearch.py ... grep "isZero_rightDerived|rightDerived.*exact|rightDerived.*[Ee]xact"
  CategoryTheory`: three hits, all in `Abelian/RightDerived.lean`; no exact match.
- `msearch.py ... leansearch "exact additive functor higher right derived functors
  vanish"`: unavailable, Internal Server Error; no mathematical verdict inferred.
- `rg -n` of the same vanishing/exactness patterns and the item id in upstream
  `WeilConjectures` and project `lean/Sheaf`: long-exact-sequence, acyclicity,
  total derived-functor, and comparison results, no matching statement.
  The upstream `PlusExact.lean` declaration signatures and docstrings were read:
  they assert an isomorphism of total derived functors, not this objectwise
  positive-degree vanishing statement.
- Name collision search for `isZero_rightDerived_obj_of_exact` in
  `dag/lean_names_upstream.json`, Mathlib, upstream `WeilConjectures`, and
  project `lean/Sheaf`: no hits.

Validation: the server single-file compile via `scompile.py F1
lem-sc-exact-functor-higher-derived-vanishing <module>` succeeded in 1.1 seconds,
with no errors or warnings. Delivery dry-run results are recorded below.

The delivery dry run `deliver2.py F1
lem-sc-exact-functor-higher-derived-vanishing --no-push` printed
`OK (dry run)`: compilation and preflight pass except for the independent second
reading, which the second reader writes. Nothing was pushed.

## Second reading by F1

I read the node copy, its recorded dependency nodes, the Lean module, and the
source at Stacks Project Tag 015F, Lemma 13.16.9 (label
`lemma-right-derived-exact-functor` in `derived.tex`). The source states that an
exact functor of abelian categories has vanishing right derived functors in every
nonzero degree. The node intentionally records the positive-degree case and
requires enough injectives so that Mathlib's chosen injective-resolution
construction is available.

The object and hypothesis checklist is:

- The source and target categories are `A : Type u₁` and `B : Type u₂`, with
  independent category universes `[Category.{v₁} A]` and `[Category.{v₂} B]`.
  Lean has exactly these four explicit universe binders.
- Abelian structures on both categories are `[Abelian A] [Abelian B]`, matching
  `def-sp-abelian` and Mathlib's `CategoryTheory.Abelian` class.
- Enough injectives are `[EnoughInjectives A] [EnoughInjectives B]`. The source
  only needs the source-side structure for right derived functors; the node
  explicitly asks for both, and Lean retains both without strengthening any
  other clause.
- The functor is `(v : A ⥤ B)`, with additivity `[v.Additive]`.
- Exactness is rendered by `[PreservesFiniteLimits v]
  [PreservesFiniteColimits v]`, the recorded Mathlib formulation for an exact
  additive functor between abelian categories (preservation of kernels and
  cokernels, hence finite limits and colimits).
- The arbitrary object is `(M : A)`, with no injectivity or finiteness
  hypothesis.
- The degree is an arbitrary integer `(q : ℤ)` with `(hq : 0 < q)`. Since
  `Functor.rightDerived` is indexed by `ℕ`, Lean uses `q.toNat`; the positivity
  hypothesis makes this the same positive degree specified by the node.
- The conclusion is exactly `IsZero ((v.rightDerived q.toNat).obj M)`, the
  categorical zero-object formulation of vanishing.

No hypothesis or conclusion clause was missing, added, weakened, or strengthened.
The theorem's docstring repeats the node's three proof steps: choose an injective
resolution; transport its positive-degree cohomology vanishing through the exact
functor; identify the result with the defining right derived functor. Its cited
dependency names are the node's names.

Edge cases checked were `q = 1` (the first positive degree), exclusion of `q = 0`,
the zero object, the zero functor, injective `M`, and independent category and
morphism universes. No empty index set or characteristic assumption is introduced
by the Mathlib definitions. The positive-integer encoding excludes no case in the
node; negative degrees are outside its stated quantifier.

I searched Mathlib, the upstream `WeilConjectures` source, project `lean/Sheaf`,
and the upstream-name index using LeanFinder, Loogle, LeanSearch, and `rg`. The
searches found Mathlib's `Functor.isZero_rightDerived_obj_injective_succ` (which
requires an injective object), exact-functor derived-category results, and the
right-derived definitions, but no theorem for every object under exactness. The
LeanSearch service was unavailable in the worker run; the available searches and
their results are recorded in `searches.jsonl`. No declaration collision was found.

The Stacks source and all dependency signatures agree with the worker module. I
found no mismatch and made no change to the theorem or node fields. The module
was recompiled with `scompile.py`; it compiled cleanly with no warnings.
