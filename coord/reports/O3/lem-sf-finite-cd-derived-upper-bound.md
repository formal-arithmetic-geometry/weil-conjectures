## Worker report

The module `lean/Sheaf/SixFunctors/FiniteCDDerivedUpperBound.lean` states
`CategoryTheory.finiteCDDerivedUpperBound`, the finite cohomological dimension theorem
from Stacks Tag 07K7.  It contains no proof beyond the required `sorry`.

The Lean rendering of each part of the node statement is as follows.

- The abelian categories are `{A : Type u₁} [Category.{v₁} A] [Abelian A]` and
  `{B : Type u₂} [Category.{v₂} B] [Abelian B]`.
- Enough injectives in `A` is `[EnoughInjectives A]`.
- The additive left exact functor is `(F : A ⥤ B) [F.Additive]
  [PreservesFiniteLimits F]`; `PreservesFiniteLimits` is Mathlib's left-exact
  functor class in an abelian category.
- Unbounded cochain derived categories are represented by
  `[HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]` and the types
  `DerivedCategory A` and `DerivedCategory B`.
- The nonnegative integer bound is `(N : ℤ)` together with `(hN0 : 0 ≤ N)`.
- Uniform vanishing above the bound is
  `(hN : ∀ (q : ℕ), N < (q : ℤ) → ∀ (X : A),
  IsZero ((F.rightDerived q).obj X))`, rendering `R^q F(X) = 0` for every
  natural degree above `N` and every object `X`.
- Existence of the total right derived functor is the existential pair
  `RF : DerivedCategory A ⥤ DerivedCategory B` and
  `α : (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
  (DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B)) ⟶
  (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A) ⋙ RF`, together
  with `RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A
  (ComplexShape.up ℤ))`.  Thus `RF` is characterized by the localization
  universal property, rather than by an arbitrary chosen functor.
- The upper-bound conclusion is
  `∀ (t : ℤ) (E : DerivedCategory A), (∀ (i : ℤ), t < i →
  IsZero ((DerivedCategory.homologyFunctor A i).obj E)) →
  ∀ (i : ℤ), t + N < i → IsZero ((DerivedCategory.homologyFunctor B i).obj
  (RF.obj E))`, exactly expressing `H^i(E)=0` for `i>t` implies
  `H^i(RF(E))=0` for `i>t+N`.

The declaration uses only recorded dependency notions: `Abelian` (the node
`def-sp-abelian` and Mathlib `CategoryTheory.Abelian`), `Injective`/injective
resolutions and enough injectives (the node `def-sp-injective-resolutions`,
Mathlib `CategoryTheory.Injective`, `CategoryTheory.EnoughInjectives`, and
`CategoryTheory.HasInjectiveResolutions`), additive and left exact functors plus
object right-derived functors (the node `def-sp-left-exact-additive`, Mathlib
`Functor.Additive`, `PreservesFiniteLimits`, and `Functor.rightDerived`), and
unbounded derived categories and cohomology (the node
`def-weil-abstract-derived-category`, Mathlib `DerivedCategory`, `DerivedCategory.Q`,
`DerivedCategory.homologyFunctor`, and `HomologicalComplex.quasiIso`).
No dependency module was needed because each recorded dependency is a usable
Mathlib declaration or match.

Edge cases checked before writing: `N = 0` is allowed by `0 ≤ N` and the vanishing
hypothesis then starts at positive derived degree; arbitrary integer `t` is allowed;
the quantifiers include zero objects and zero cohomology; the quantification over all
integer degrees includes empty/zero complexes and has no boundedness restriction on
`E`; and independent category and localization universes are retained explicitly.

Searches made:

- `msearch.py ... leanfinder "unbounded total right derived functor finite cohomological dimension upper cohomology bound"`: eight hits, all generic `DerivedCategory.IsGE`/`IsLE` support declarations; no amplitude theorem.
- `msearch.py ... loogle "Functor.totalRightDerived, Functor.IsRightDerivedFunctor, DerivedCategory.homologyFunctor"`: no hits (the query's qualified names were unknown to Loogle).
- `msearch.py ... grep "finiteCD|cohomological.*dimension|totalRightDerived" CategoryTheory`: hits only Mathlib's generic `totalRightDerived`/`IsRightDerivedFunctor` definitions and no finite-dimension upper-bound statement.
- `rg -n "finiteCDDerivedUpperBound"` over the project and upstream source: no existing declaration.
- `rg -n "finite cohomological dimension|upper bound|unbounded right derived"` over project and upstream source: no matching theorem declaration.

The source proof is recorded in the declaration docstring step-by-step: degree
function and long-exact-sequence bounds; termwise right-acyclic replacements; exact
complex preservation and cone quasi-isomorphism detection; localization/right-derived
existence; and finite dimension shifting on cycles for the stated upper bound.

## Earlier second reading (a previous round; superseded)

I re-read the node statement and the completed signature against the source place.  The
category hypotheses, enough-injectives assumption, additive and left exact functor,
integer `N ≥ 0`, vanishing of every object right-derived functor above `N`, existence
of the total right-derived functor, and both cohomology support clauses all occur in
the signature with the same quantifiers.  The localization map uses `F` applied to
cochain complexes followed by the target derived localization, and the universal
property uses the source quasi-isomorphism property.  No clause was added, dropped,
weakened, or specialized; the independent universes and the `N = 0` edge case remain.


## Second reading by N3

I independently opened the item node, all four statement-dependency nodes and their
recorded Mathlib signatures, all nine proof-dependency records, the sandbox module,
and Stacks `derived.tex`, lemma-unbounded-right-derived (Tag 07K7), lines
9977–10109. There is no `statement_change`, no new node and no dependency module.
The node is an explicit specialization of 07K7: enough injectives gives enough
right-acyclic objects, and the uniform hypothesis gives the source's vanishing
`R^n F = 0` with `n = N+1`. Part (4)(c), with interval `[-∞,t]`, then gives
precisely the conclusion above `t+N`. The source assumes abelian categories and
left exactness here; it assumes neither Grothendieckness nor enough injectives in
B. Nothing in the Lean adds either assumption.

The object/hypothesis/conclusion inventory and its Lean rendering are:

1. Two abelian categories A and B: `{A : Type u₁} [Category.{v₁} A]
   [Abelian A]` and `{B : Type u₂} [Category.{v₂} B] [Abelian B]`.
   Verdict: exact. `CategoryTheory.Abelian` in Mathlib's Abelian/Basic has the
   preadditive, kernel, cokernel, finite-product and normal mono/epi data of
   `def-sp-abelian`; finite biproducts and the zero object follow in that API.
2. Every A-object embeds into an injective: `[EnoughInjectives A]`.
   Verdict: exact. I read `Injective`, `InjectivePresentation` and
   `EnoughInjectives` in Preadditive/Injective/Basic; the latter requires a
   presentation for every X, consisting of a mono into an injective object.
   The Resolution module supplies `HasInjectiveResolutions` from these hypotheses;
   no further resolution assumption is present in the signature.
3. F is an additive left exact functor A → B: `(F : A ⥤ B) [F.Additive]
   [PreservesFiniteLimits F]`. Verdict: exact. AdditiveFunctor's `map_add` is
   equivalent to finite-biproduct preservation, and Preadditive/LeftExact's
   `preservesFiniteLimits_of_preservesKernels` verifies that finite-limit
   preservation is precisely the node's kernel preservation for an additive
   functor. There is no stronger exactness assumption.
4. Object derived functors R^q F: `(F.rightDerived q).obj X`. Verdict: exact.
   I read `Functor.rightDerived` and `InjectiveResolution.isoRightDerivedObj` in
   Mathlib CategoryTheory/Abelian/RightDerived: the former is injective-resolution
   cohomology and the latter compares any such resolution. This is the recorded
   `def-sp-left-exact-additive`, not a different total-derived construction.
5. An integer N ≥ 0: `(N : ℤ) (hN0 : 0 ≤ N)`. Verdict: exact.
6. Uniform vanishing on every object in every degree above N:
   `hN : ∀ (q : ℕ), N < (q : ℤ) → ∀ (X : A),
   IsZero ((F.rightDerived q).obj X)`. Verdict: exact. Natural object-derived
   degrees are the q ≥ 0 of the node; N ≥ 0 means no missing negative-degree case.
   The order of the q and X universal binders changes no dependence.
7. Unbounded cochain derived categories and cohomology:
   `[HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]`,
   `DerivedCategory A`, `DerivedCategory B`, and
   `DerivedCategory.homologyFunctor A i` / `B i`. Verdict: exact.
   I opened DerivedCategory/Basic and HomologySequence: Q localizes all
   ℤ-indexed cochain complexes at `HomologicalComplex.quasiIso`, and
   `homologyFunctorFactors` identifies derived cohomology with complex cohomology.
   `HasDerivedCategory` specifies the chosen localization size, as the dependency
   explicitly requests, and its `standard` construction exists without any
   extra mathematical assumption.
8. Existence of the unbounded total right derived functor:
   `∃ (RF : DerivedCategory A ⥤ DerivedCategory B) (α :
   F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
   DerivedCategory.Q ⋙ RF), RF.IsRightDerivedFunctor α
   (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ∧ ...`.
   Verdict: exact. I opened Functor/Derived/RightDerived: the class is the left
   Kan-extension universal property along the specified localization, with the
   correct unit direction. Thus this states existence of RF as a derived functor,
   rather than merely an unconstrained functor satisfying a bound. Taking the
   localization directly from complexes agrees with the dependency's equivalent
   homotopy-category presentation.
9. For every integer t and E, the assumed upper cohomology bound:
   `∀ (t : ℤ) (E : DerivedCategory A), (∀ (i : ℤ), t < i →
   IsZero ((DerivedCategory.homologyFunctor A i).obj E)) → ...`.
   Verdict: exact; t is arbitrary, and E has no lower boundedness assumption.
10. For the same RF and every such t and E, the shifted upper bound:
    `∀ (i : ℤ), t + N < i → IsZero
    ((DerivedCategory.homologyFunctor B i).obj (RF.obj E))`.
    Verdict: exact, including the strict inequality. RF and α are chosen before
    t and E, so a single derived functor satisfies all the required bounds.

Edge cases: N = 0 permits every exact functor satisfying positive-degree
vanishing, and asserts no increase in the upper bound; degree i = t+N is
correctly excluded from the vanishing conclusion. Negative and zero t are
included. The zero object, zero complex and trivial abelian categories are
included by the unrestricted object binders; no nonzero/nonempty condition is
added. There is no indexing family, scheme, field or characteristic in this
abstract statement, so empty index sets, empty schemes and characteristic
restrictions do not arise. The object universes u₁/u₂, morphism universes v₁/v₂
and localization universes w₁/w₂ are six explicitly bound, independent
universes; there is no hidden equality, smallness restriction or unbound
variable. Every signature variable and hypothesis was checked by eye.

Independent searches (2026-10-16), using different descriptive terms from the
first reader's queries:

- LeanFinder through msearch: “Derived functor of a left exact functor of finite
  homological dimension preserves bounded above complexes up to a finite shift”.
  Eight results: exact-functor `mapDerivedCategory` infrastructure and standard
  `IsLE`/`IsGE` support lemmas. None is this finite-dimension theorem.
- Loogle through msearch: `CategoryTheory.Functor.IsRightDerivedFunctor`.
  Twelve results: the class, Kan-extension conversion, total-right-derived
  existence/uniqueness and descent. I read the class signature and universal
  direction above; none supplies the finite-dimension hypothesis or bound.
- LeanSearch through msearch: “Unbounded derived functor exists for a left exact
  additive functor with uniformly bounded higher right derived functors and
  preserves upper cohomology bounds up to that bound”. Eight results: ordinary
  derived functors, resolution comparisons, and Kan-extension definitions;
  no match for the upper-bound theorem.
- `rg` across Mathlib CategoryTheory and Algebra/Homology, upstream
  WeilConjectures, and the project's lean/Sheaf, with
  `cohomologicalDimension`, `finite.{0,30}(dimension|amplitude)`,
  `rightDerived.{0,40}(isLE|IsLE)`, `IsLE.{0,40}(rightDerived|totalRightDerived)`,
  “upper cohomolog”, and the proposed declaration name. I opened the project's
  `CategoryTheory.Functor.exists_rightDerived_computes_acyclic_of_finite_dimension`
  in FiniteCohomologicalDimensionAcyclicComplex: it assumes Grothendieck A and
  concludes acyclic-complex computation, with no upper bound, so is not a match.
  I also fetched the current published
  `WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension`
  with `scompile.py --source`. Its exact-complex theorem has the enough-resolution
  hypotheses used by the node; its subsequent total-derived statements assume
  K-injective resolutions/Grothendieckness and do not state this upper bound.
  The remaining geometry hits concern particular sheaf functors, not arbitrary
  abelian categories. The name also has no upstream-name-table collision.

Mismatches found and repaired:

- H8: the old docstring compressed the proof into a paragraph and did not carry
  each DAG step. Expanded it to the full six-step degree-function, replacement,
  exact-complex, cone, localization and cycle-dimension-shifting argument, naming
  the dependency nodes and covering N = 0 explicitly.
- Stage-2 import rule: the old module omitted stated proof dependencies. Added
  non-public imports for FullLongExactSequence, the published pointwise finite-CD
  module, the upstream quasi-isomorphism/cone criterion, and Mathlib's homotopy
  triangulated structure. Unstated replacement and adapted-complex nodes have
  no module to import. The remaining Mathlib proof dependencies are already
  available through the public imports.
- H9 topic convention: moved this generic abelian-category theorem from
  SixFunctors to `lean/Sheaf/CategoryTheory/DerivedCategory/FiniteCDDerivedUpperBound.lean`
  and updated lean.module/lean.file; no declaration name or signature changed.

No H3 mismatch was found, so the mathematical node and theorem signature are
unchanged. No duplicate notion, hollow definition or added theorem is present;
the sole theorem proof remains `by sorry`. The node's lean.statement is extracted
verbatim from the final signature. All declaration and module docstrings retain
the source and blueprint marker. Compilation and the prescribed delivery
preflight are recorded below.

Validation: `scompile.py N3 lem-sf-finite-cd-derived-upper-bound lean/Sheaf/CategoryTheory/DerivedCategory/FiniteCDDerivedUpperBound.lean` completed cleanly for both sandbox and library-path checks (2.2 s and 2.3 s). No error or additional warning was emitted. The signature record and 100-character Lean line-width check also passed.

The prescribed `deliver2.py N3 lem-sf-finite-cd-derived-upper-bound --no-push` dry run printed OK: compilation and the current server preflight both passed.
